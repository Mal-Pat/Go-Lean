/-
Authors: Malhar A. Patel
-/

import Lean.Data.Json
import GoLean.Core.Game
import GoLean.Core.Sgf

/-!
# The RPC protocol layer

Plain, non-dependent DTOs for the widget boundary. The wire state held by
the client is the event log (`ConfigDto` + `Array ActionDto`). The server
rebuilds the `Game` by folding `Game.step` and returns a render-ready `ViewDto`.
The JavaScript never inspects the log and never computes rules.

`handleUpdate` is pure, so the whole protocol is testable with `#eval`.
-/

namespace GoLean

open Lean (ToJson FromJson)

/-- Wire form of `GameConfig` (+ the ruleset toggles, flattened). -/
structure ConfigDto where
  rows : Nat := 19
  cols : Nat := 19
  handicap : Nat := 0
  /-- Twice the komi (`13` = 6.5). -/
  komi2 : Int := 13
  blackName : String := "Black"
  whiteName : String := "White"
  /-- `"simple" | "positional" | "situational" | "none"`. -/
  ko : String := "simple"
  /-- `"territory" | "area"`. -/
  scoring : String := "territory"
  selfCaptureAllowed : Bool := false
  passesToScore : Nat := 2
  deriving ToJson, FromJson, Inhabited, Repr

/-- Wire form of `Action`. `r`/`c`/`who` are meaningful only for the kinds
that use them; the client always sends every field. -/
structure ActionDto where
  /-- `"play" | "pass" | "resign" | "undo" | "toggleDead" | "accept" | "resume"`. -/
  kind : String
  r : Nat := 0
  c : Nat := 0
  /-- For `accept`: `"black" | "white"`. -/
  who : String := ""
  deriving ToJson, FromJson, Inhabited, Repr

/-- The opaque client-held game state: the event log is the wire state. -/
structure GameDto where
  config : ConfigDto
  actions : Array ActionDto := #[]
  deriving ToJson, FromJson, Inhabited, Repr

/-- One intersection, render-ready. -/
structure CellDto where
  /-- `"black" | "white" | ""`. -/
  stone : String := ""
  dead : Bool := false
  /-- `"black" | "white" | ""`. -/
  territory : String := ""
  lastMove : Bool := false
  hoshi : Bool := false
  deriving ToJson, FromJson, Inhabited

/-- Render-ready score breakdown (all numbers pre-formatted). -/
structure ScoreCardDto where
  method : String
  komi : String
  blackTerritory : Nat
  whiteTerritory : Nat
  blackStones : Nat
  whiteStones : Nat
  blackPrisoners : Nat
  whitePrisoners : Nat
  blackScore : String
  whiteScore : String
  deriving ToJson, FromJson, Inhabited

/-- Everything the widget needs to paint, derived server-side. -/
structure ViewDto where
  /-- `"playing" | "scoring" | "finished"`. -/
  phase : String
  rows : Nat
  cols : Nat
  board : Array (Array CellDto)
  toMove : String
  moveNum : Nat
  blackCaptures : Nat
  whiteCaptures : Nat
  blackName : String
  whiteName : String
  komi : String
  rulesSummary : String
  consecPasses : Nat
  passesToScore : Nat
  handicapLeft : Nat
  blackAccepted : Bool := false
  whiteAccepted : Bool := false
  colLabels : Array String
  rowLabels : Array String
  /-- Number of moves (stone placements + passes) in the whole game. -/
  totalMoves : Nat := 0
  /-- In review mode (`phase = "review"`): the move currently shown. -/
  reviewMove : Nat := 0
  /-- The game so far, serialized as SGF (FF[4]). -/
  sgf : String := ""
  scoreCard : Option ScoreCardDto := none
  result : Option String := none
  deriving ToJson, FromJson, Inhabited

structure UpdateRequest where
  game : GameDto
  action : Option ActionDto := none
  /-- `some k`: do not apply any action; instead return a read-only view of
  the position after the first `k` moves (clamped to the game length).
  The event log is left untouched — the client uses this to step back and
  forth through the game. -/
  review : Option Nat := none
  deriving ToJson, FromJson, Inhabited

/-- A rejected action returns the unchanged `game` plus `error`; the log
only advances on success. A `none` view means the config itself was
rejected (the client stays on the setup screen). -/
structure UpdateResponse where
  game : GameDto
  view : Option ViewDto := none
  error : Option String := none
  deriving ToJson, FromJson, Inhabited

/-! ## DTO → core conversions -/

def parseKo : String → Option KoRule
  | "simple" => some .simple
  | "positional" => some .positionalSuperko
  | "situational" => some .situationalSuperko
  | "none" => some .none
  | _ => Option.none

def parseScoring : String → Option ScoringMethod
  | "territory" => some .territory
  | "area" => some .area
  | _ => none

def ConfigDto.toConfig (d : ConfigDto) : Except String GameConfig := do
  let some size := Size.ofNats? d.rows d.cols
    | throw "Board size must be at least 2×2."
  let some ko := parseKo d.ko
    | throw s!"Unknown ko rule: {d.ko}"
  let some scoring := parseScoring d.scoring
    | throw s!"Unknown scoring method: {d.scoring}"
  return { size
           komi2 := d.komi2
           handicap := d.handicap
           blackName := if d.blackName.isEmpty then "Black" else d.blackName
           whiteName := if d.whiteName.isEmpty then "White" else d.whiteName
           ruleset := { ko, scoring
                        selfCaptureAllowed := d.selfCaptureAllowed
                        defaultKomi2 := d.komi2
                        passesToScore := max 1 d.passesToScore } }

def ActionDto.toAction (d : ActionDto) : Except String Action :=
  match d.kind with
  | "play" => .ok (.play d.r d.c)
  | "pass" => .ok .pass
  | "resign" => .ok .resign
  | "undo" => .ok .undo
  | "toggleDead" => .ok (.toggleDead d.r d.c)
  | "accept" =>
    match d.who with
    | "black" => .ok (.accept .black)
    | "white" => .ok (.accept .white)
    | w => .error s!"Bad accept target: {w}"
  | "resume" => .ok .resume
  | k => .error s!"Unknown action kind: {k}"

def Action.toDto : Action → ActionDto
  | .play r c => { kind := "play", r, c }
  | .pass => { kind := "pass" }
  | .resign => { kind := "resign" }
  | .undo => { kind := "undo" }
  | .toggleDead r c => { kind := "toggleDead", r, c }
  | .accept .black => { kind := "accept", who := "black" }
  | .accept .white => { kind := "accept", who := "white" }
  | .resume => { kind := "resume" }

/-- Number of moves (stone placements + passes) in the log. -/
def Game.countMoves (g : Game) : Nat :=
  g.actions.foldl (fun n a => if a.isMove then n + 1 else n) 0

/-- The shortest legal prefix of a log realizing the position after the
first `k` moves: everything up to and including the `k`-th move action,
with non-move actions kept only when a later included move needs the phase
they establish (i.e. they precede the `k`-th move). -/
def movePrefix (actions : Array Action) (k : Nat) : Array Action := Id.run do
  let mut out : Array Action := #[]
  let mut cnt := 0
  for a in actions do
    if a.isMove then
      if cnt ≥ k then
        return out
      cnt := cnt + 1
      out := out.push a
    else if cnt < k then
      out := out.push a
  return out

/-- Rebuild the `Game` from the wire state by folding `Game.step`. -/
def GameDto.build (gd : GameDto) : Except String Game := do
  let cfg ← gd.config.toConfig
  let g0 ← (Game.new cfg).mapError (·.describe)
  gd.actions.foldlM (fun g adto => do
    let a ← adto.toAction
    (g.step a).mapError (·.describe)) g0

/-! ## Core → view conversion -/

private def colorName : Color → String
  | .black => "black"
  | .white => "white"

private def mkBoardCells {s : Size} (b : Board s) (last? : Option (Point s))
    (dead : PointSet s) (terr : Territories s) : Array (Array CellDto) :=
  let stars := s.starPoints
  Array.ofFn (n := s.rows) fun r =>
    Array.ofFn (n := s.cols) fun c =>
      let p : Point s := ⟨r, c⟩
      { stone :=
          match b.get p with
          | some col => colorName col
          | none => ""
        dead := dead.contains p
        territory :=
          if terr.black.contains p then "black"
          else if terr.white.contains p then "white"
          else ""
        lastMove := last? == some p
        hoshi := stars.contains p }

private def ScoreCard.toDto (card : ScoreCard) : ScoreCardDto :=
  { method := card.method.describe
    komi := formatHalfInt card.komi2
    blackTerritory := card.blackTerritory
    whiteTerritory := card.whiteTerritory
    blackStones := card.blackStones
    whiteStones := card.whiteStones
    blackPrisoners := card.blackPrisoners
    whitePrisoners := card.whitePrisoners
    blackScore := formatHalfInt card.blackScore2
    whiteScore := formatHalfInt card.whiteScore2 }

/-- Render-ready view of the current game state. -/
def Game.toView (g : Game) : ViewDto :=
  let s := g.config.size
  let cfg := g.config
  let ps := g.curPlayState
  let (phase, cells, blackAccepted, whiteAccepted, scoreCard, result) :=
    match g.phase with
    | .playing ps =>
      ("playing", mkBoardCells ps.board ps.lastMove? ∅ {}, false, false,
       Option.none, Option.none)
    | .scoring ss =>
      let terr := ss.cleared.territories
      let card := ss.scoreCard cfg.ruleset cfg.komi2
      ("scoring", mkBoardCells ss.play.board none ss.deadMarks terr,
       ss.blackAccepted, ss.whiteAccepted, some card.toDto, Option.none)
    | .finished ss res =>
      let terr := ss.cleared.territories
      let card? :=
        match res.detail with
        | .score card => some card.toDto
        | .resignation _ => Option.none
      ("finished", mkBoardCells ss.play.board none ss.deadMarks terr,
       ss.blackAccepted, ss.whiteAccepted, card?, some res.format)
  { phase
    rows := s.rows
    cols := s.cols
    board := cells
    toMove := colorName ps.toMove
    moveNum := ps.moveNum
    blackCaptures := ps.captures.black
    whiteCaptures := ps.captures.white
    blackName := cfg.blackName
    whiteName := cfg.whiteName
    komi := formatHalfInt cfg.komi2
    rulesSummary := cfg.ruleset.summary cfg.komi2
    consecPasses := ps.consecPasses
    passesToScore := cfg.ruleset.passesToScore
    handicapLeft := ps.handicapLeft
    blackAccepted, whiteAccepted
    colLabels := Array.ofFn (n := s.cols) fun c => colLabel c.val
    rowLabels := Array.ofFn (n := s.rows) fun r => toString (s.rows - r.val)
    totalMoves := g.countMoves
    sgf := g.toSgf
    scoreCard, result }

/-! ## The update entry point -/

/-- A read-only view of the position after the first `k` moves. The board
comes from replaying the log prefix; the SGF and move count stay those of
the full game, and score/result panels are suppressed. -/
def Game.toReviewView (g : Game) (k : Nat) : Option ViewDto := do
  let total := g.countMoves
  let k := min k total
  let gr ← (Game.ofRecord g.config (movePrefix g.actions k)).toOption
  return { gr.toView with
           phase := "review"
           reviewMove := k
           totalMoves := total
           sgf := g.toSgf
           scoreCard := none
           result := none }

/-- Pure handler behind the RPC method: rebuild, then either return a
read-only review view (`review = some k`) or optionally apply one action,
returning the (possibly advanced) wire state plus the view. -/
def handleUpdate (req : UpdateRequest) : UpdateResponse :=
  match req.game.build with
  | .error e => { game := req.game, error := some e }
  | .ok g =>
    let respond (g' : Game) (err : Option String) : UpdateResponse :=
      { game := { config := req.game.config, actions := g'.actions.map Action.toDto }
        view := some g'.toView
        error := err }
    match req.review with
    | some k =>
      match g.toReviewView k with
      | some v => { game := req.game, view := some v, error := none }
      | none => respond g (some "Could not replay the game for review.")
    | none =>
      match req.action with
      | none => respond g none
      | some adto =>
        match adto.toAction with
        | .error e => respond g (some e)
        | .ok a =>
          match g.step a with
          | .error ill => respond g (some ill.describe)
          | .ok g' => respond g' none

end GoLean
