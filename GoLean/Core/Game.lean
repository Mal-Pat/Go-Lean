/-
Authors: Malhar A. Patel
-/

import GoLean.Core.Score

/-!
# The game state

A `Game` stores the `GameConfig`, the log of accepted `Action`s,
and the current `Phase`.
Normal play is incremental, while Undo and replay-from-record
are rebuild by folding over a truncated log.

`Game.step : Game → Action → Except IllegalAction Game` is the function
for everything the players can do after setup.
-/

namespace GoLean

/-- Everything decided in the setup phase. -/
structure GameConfig where
  size : Size
  ruleset : Ruleset := {}
  /-- Twice the komi (`13` = 6.5). -/
  komi2 : Int := 13
  handicap : Nat := 0
  /-- Explicit initial black stones `(row, col)`, e.g. an SGF's `AB` setup.
  When either setup list is nonempty it overrides star-point handicap
  placement (`handicap` is then only informational). -/
  setupBlack : List (Nat × Nat) := []
  /-- Explicit initial white stones `(row, col)`, e.g. an SGF's `AW` setup. -/
  setupWhite : List (Nat × Nat) := []
  /-- Force who moves first (used by SGF import). `none` = the convention:
  White after handicap/black-only setup, otherwise Black. -/
  firstToMove : Option Color := none
  blackName : String := "Black"
  whiteName : String := "White"

/-- Everything the players can do after setup. -/
inductive Action where
  /-- Place a stone (also used for free-handicap placement). -/
  | play (r c : Nat)
  | pass
  | resign
  /-- Rewind to before the last stone placement or pass. -/
  | undo
  /-- Scoring: mark/unmark the chain at `(r, c)` as dead. -/
  | toggleDead (r c : Nat)
  /-- Scoring: agree with the current dead marks. -/
  | accept (who : Color)
  /-- Scoring: disagree and return to play. -/
  | resume
  deriving DecidableEq, Repr, Inhabited

/-- Stone placements and passes are "moves" — the navigable game record;
scoring actions, resignation and undo are not. -/
def Action.isMove : Action → Bool
  | .play _ _ | .pass => true
  | _ => false

/-- Reason for rejecting an action. -/
inductive IllegalAction where
  | outOfBoard
  | occupied
  | selfCapture
  | koViolation (rule : KoRule)
  | wrongPhase
  | nothingToUndo
  | notAChain
  | gameOver
  deriving DecidableEq, Repr

def IllegalAction.describe : IllegalAction → String
  | .outOfBoard => "That point is outside the board."
  | .occupied => "That point is occupied."
  | .selfCapture => "Self-capture is not allowed under these rules."
  | .koViolation .simple => "Illegal ko recapture."
  | .koViolation _ => "That move would repeat a previous position (superko)."
  | .wrongPhase => "That action is not available in this phase."
  | .nothingToUndo => "Nothing to undo."
  | .notAChain => "Click a stone to mark its chain dead or alive."
  | .gameOver => "The game is over."

def IllegalMove.toAction : IllegalMove → IllegalAction
  | .occupied => .occupied
  | .selfCapture => .selfCapture
  | .koViolation r => .koViolation r

/-- Details of the game result. -/
inductive ResultDetail where
  | score (card : ScoreCard)
  | resignation (loser : Color)

/-- The final result. `winner = none` is a draw (possible with integer komi). -/
structure GameResult where
  winner : Option Color
  detail : ResultDetail

/-- Standard result string: `B+3.5`, `W+R`, `Draw`, … -/
def GameResult.format : GameResult → String
  | ⟨winner, .resignation _⟩ =>
    match winner with
    | some .black => "B+R"
    | some .white => "W+R"
    | none => "?"
  | ⟨winner, .score card⟩ =>
    match winner with
    | some .black => s!"B+{formatHalfInt (card.blackScore2 - card.whiteScore2)}"
    | some .white => s!"W+{formatHalfInt (card.whiteScore2 - card.blackScore2)}"
    | none => "Draw"

/-- The phase of a game. `finished` keeps the last `ScoreState` so the final
position and dead marks can still be displayed. -/
inductive Phase (s : Size) where
  | playing (ps : PlayState s)
  | scoring (ss : ScoreState s)
  | finished (ss : ScoreState s) (result : GameResult)

/-- Reason for rejecting a `GameConfig`. -/
inductive ConfigError where
  | badHandicap (max : Nat)
  | setupOutOfBoard (r c : Nat)
  | setupOverlap (r c : Nat)
  deriving DecidableEq, Repr

def ConfigError.describe : ConfigError → String
  | .badHandicap max => s!"Handicap must be 0 or 2–{max} on this board."
  | .setupOutOfBoard r c => s!"Setup stone at ({r}, {c}) is outside the board."
  | .setupOverlap r c => s!"Two setup stones at ({r}, {c})."

namespace GameConfig

/-- The initial play state: empty board, explicit setup stones (SGF `AB`/`AW`),
or handicap stones placed (fixed placement on standard boards, free
placement elsewhere). `firstToMove` overrides the conventional first mover. -/
def initialPlayState (cfg : GameConfig) : Except ConfigError (PlayState cfg.size) := do
  let base : PlayState cfg.size ←
    if !cfg.setupBlack.isEmpty || !cfg.setupWhite.isEmpty then do
      -- Explicit setup stones override star-point placement.
      let place (bd : Board cfg.size) (col : Color) (rc : Nat × Nat) :
          Except ConfigError (Board cfg.size) := do
        match Point.ofNats? cfg.size rc.1 rc.2 with
        | none => throw (.setupOutOfBoard rc.1 rc.2)
        | some p =>
          if (bd.get p).isSome then throw (.setupOverlap rc.1 rc.2)
          else return bd.set p (some col)
      let bd ← cfg.setupBlack.foldlM (fun b rc => place b .black rc) (Board.empty cfg.size)
      let bd ← cfg.setupWhite.foldlM (fun b rc => place b .white rc) bd
      -- Handicap convention: black-only setup means White moves first.
      let first := if cfg.setupWhite.isEmpty then Color.white else Color.black
      pure { board := bd, toMove := first, history := #[(bd, first)] }
    else if cfg.handicap ≤ 1 then
      pure (PlayState.initial cfg.size)
    else
      match cfg.size.fixedHandicapPoints cfg.handicap with
      | some pts =>
        -- Fixed placement: stones on star points, White moves first.
        let b := pts.foldl (fun bd p => bd.set p (some Color.black)) (Board.empty cfg.size)
        pure { board := b, toMove := .white, history := #[(b, Color.white)] }
      | none =>
        if cfg.size.maxFixedHandicap != 0 then
          -- Standard board, but the requested handicap is out of range.
          throw (.badHandicap cfg.size.maxFixedHandicap)
        else if cfg.handicap + 2 ≤ cfg.size.cells then
          -- Nonstandard board: free placement, Black plays the stones herself.
          pure { PlayState.initial cfg.size with handicapLeft := cfg.handicap }
        else
          throw (.badHandicap (cfg.size.cells - 2))
  match cfg.firstToMove with
  | none => return base
  | some col =>
    if base.handicapLeft > 0 && col != .black then
      -- Free-handicap placement is Black's; ignore an inconsistent override.
      return base
    else
      return { base with toMove := col, history := #[(base.board, col)] }

/-- One transition of the phase state (everything except `undo`,
which is handled by `Game.step` because it rewinds the log). -/
def stepPhase (cfg : GameConfig) (ph : Phase cfg.size) (a : Action) :
    Except IllegalAction (Phase cfg.size) := do
  match ph with
  | .playing ps =>
    match a with
    | .play r c =>
      match Point.ofNats? cfg.size r c with
      | none => throw .outOfBoard
      | some p =>
        match ps.play cfg.ruleset p with
        | .error e => throw e.toAction
        | .ok ps' => return .playing ps'
    | .pass =>
      let ps' := ps.pass
      if ps'.consecPasses ≥ cfg.ruleset.passesToScore then
        return .scoring { play := ps' }
      else
        return .playing ps'
    | .resign =>
      return .finished { play := ps }
        { winner := some ps.toMove.opp, detail := .resignation ps.toMove }
    | .undo => throw .nothingToUndo  -- handled in `Game.step`
    | _ => throw .wrongPhase
  | .scoring ss =>
    match a with
    | .toggleDead r c =>
      match Point.ofNats? cfg.size r c with
      | none => throw .outOfBoard
      | some p =>
        match ss.toggleDead p with
        | .error _ => throw .notAChain
        | .ok ss' => return .scoring ss'
    | .accept who =>
      let ss' :=
        match who with
        | .black => { ss with blackAccepted := true }
        | .white => { ss with whiteAccepted := true }
      if ss'.blackAccepted && ss'.whiteAccepted then
        let card := ss'.scoreCard cfg.ruleset cfg.komi2
        let winner :=
          if card.blackScore2 > card.whiteScore2 then some Color.black
          else if card.whiteScore2 > card.blackScore2 then some Color.white
          else none
        return .finished ss' { winner, detail := .score card }
      else
        return .scoring ss'
    | .resume =>
      return .playing { ss.play with consecPasses := 0 }
    | _ => throw .wrongPhase
  | .finished _ _ => throw .gameOver

end GameConfig

/-- A full game: setup config, the event log of accepted actions, and the
current phase (equal to folding `stepPhase` over the log). -/
structure Game where
  config : GameConfig
  actions : Array Action := #[]
  phase : Phase config.size

namespace Game

/-- Start a game from a validated config. -/
def new (cfg : GameConfig) : Except ConfigError Game := do
  let ps ← cfg.initialPlayState
  return { config := cfg, phase := .playing ps }

/-- Apply one logged action (no `undo`, as logs never contain it). -/
private def replayStep (g : Game) (a : Action) : Except IllegalAction Game := do
  let ph ← g.config.stepPhase g.phase a
  return { g with actions := g.actions.push a, phase := ph }

/-- Rewind to before the last stone placement or pass, dropping any trailing
scoring actions, and rebuild by replaying the truncated log. -/
def undo (g : Game) : Except IllegalAction Game := do
  match g.phase with
  | .playing _ =>
    let arr := g.actions
    let idx? := (List.range arr.size).reverse.find? fun i =>
      match arr[i]? with
      | some a => a.isMove
      | none => false
    match idx? with
    | none => throw .nothingToUndo
    | some i =>
      let fresh ←
        match Game.new g.config with
        | .ok g0 => pure g0
        | .error _ => throw .nothingToUndo  -- unreachable, config was valid
      (arr.extract 0 i).foldlM replayStep fresh
  | .scoring _ => throw .wrongPhase  -- `toggleDead` is its own inverse
  | .finished _ _ => throw .gameOver

/-- Apply an action to a game. -/
def step (g : Game) (a : Action) : Except IllegalAction Game :=
  match a with
  | .undo => g.undo
  | _ => g.replayStep a

/-- Replay a whole record (e.g. from a saved game). -/
def ofRecord (cfg : GameConfig) (actions : Array Action) : Except String Game := do
  let g0 ← (Game.new cfg).mapError (·.describe)
  actions.foldlM (fun g a => (g.step a).mapError (·.describe)) g0

/-- The board currently on display, in any phase. -/
def curBoard (g : Game) : Board g.config.size :=
  match g.phase with
  | .playing ps => ps.board
  | .scoring ss => ss.play.board
  | .finished ss _ => ss.play.board

/-- The frozen play state, in any phase. -/
def curPlayState (g : Game) : PlayState g.config.size :=
  match g.phase with
  | .playing ps => ps
  | .scoring ss => ss.play
  | .finished ss _ => ss.play

end Game

end GoLean
