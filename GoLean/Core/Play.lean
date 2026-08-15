/-
Authors: Malhar A. Patel
-/

import GoLean.Core.Board
import GoLean.Core.Rules

/-!
# The play phase

`PlayState` is the live position plus everything needed to continue play:
whose turn it is, prisoner counts, the position history (for ko/superko),
consecutive passes and free-handicap placements.

`PlayState.play` is the move pipeline. The order matters:
occupied check → place → remove opponent chains with no liberties
→ self-capture check/removal → ko check → commit.
-/

namespace GoLean

/-- Prisoners taken by each color. -/
structure Captures where
  black : Nat := 0
  white : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace Captures

/-- Add `n` prisoners to color `col`. -/
def add (cap : Captures) (col : Color) (n : Nat) : Captures :=
  match col with
  | .black => { cap with black := cap.black + n }
  | .white => { cap with white := cap.white + n }

/-- Get the captures of color `col` -/
def of (cap : Captures) (col : Color) : Nat :=
  match col with
  | .black => cap.black
  | .white => cap.white

end Captures

/-- Reason for rejecting a stone placement. -/
inductive IllegalMove where
  | occupied
  | selfCapture
  | koViolation (rule : KoRule)
  deriving DecidableEq, Repr

/-- The state of a game in the play phase. -/
structure PlayState (s : Size) where
  board : Board s
  toMove : Color
  captures : Captures := {}
  moveNum : Nat := 0
  /-- History of each position paired with the color to move next from it. -/
  history : Array (Board s × Color)
  consecPasses : Nat := 0
  lastMove? : Option (Point s) := none
  /-- Free-handicap stones that Black must place
  (turn does not pass to White until this reaches zero). -/
  handicapLeft : Nat := 0
  deriving Repr

namespace PlayState

/-- Empty board with Black to move. -/
def initial (s : Size) : PlayState s :=
  let b := Board.empty s
  { board := b, toMove := .black, history := #[(b, .black)] }

/-- Reject `candidate` board if it repeats a position forbidden by a ko `rule`.
`next` is the color to move after the candidate move. -/
def checkKo {s : Size} (rule : KoRule) (history : Array (Board s × Color))
    (candidate : Board s) (next : Color) : Except IllegalMove Unit :=
  match rule with
  | .none => .ok ()
  | .simple =>
    -- The position before the opponent's last move is `history[size - 2]` (`history` ends with the current position).
    let prev? := if history.size ≥ 2 then history[history.size - 2]? else none
    match prev? with
    | some (prev, _) =>
      if prev == candidate then .error (.koViolation .simple) else .ok ()
    | none => .ok ()
  | .positionalSuperko =>
    if history.any (fun h => h.1 == candidate) then
      .error (.koViolation .positionalSuperko)
    else .ok ()
  | .situationalSuperko =>
    if history.any (fun h => h.1 == candidate && h.2 == next) then
      .error (.koViolation .situationalSuperko)
    else .ok ()

/-- Attempt to place a stone of the current player at `p`. -/
def play {s : Size} (ps : PlayState s) (rules : Ruleset) (p : Point s) :
    Except IllegalMove (PlayState s) := do
  -- Check if the point is occupied
  if (ps.board.get p).isSome then
    throw .occupied
  let mover := ps.toMove
  let opponent := mover.opp
  let placed := ps.board.set p (some mover)
  -- Capture any adjacent opponent chains left with no liberties
  let captured : PointSet s :=
    p.neighbors.foldl (init := (∅ : PointSet s)) fun acc q =>
      if acc.contains q then acc  -- already collected via a shared chain
      else
        match placed.chainAt? q with
        | some ch =>
          if ch.color == opponent && ch.liberties.isEmpty then
            ch.stones.fold (fun a x => a.insert x) acc
          else acc
        | none => acc
  let afterCaps := placed.setPoints captured none
  let (finalBoard, capsByMover, capsByOpponent) ←
    if captured.isEmpty then
      match afterCaps.chainAt? p with
      | some ch =>
        if ch.liberties.isEmpty then
          if rules.selfCaptureAllowed then
            -- The removed stones are prisoners for the opponent.
            pure (afterCaps.setPoints ch.stones none, 0, ch.stones.size)
          else
            throw .selfCapture
        else
          pure (afterCaps, 0, 0)
      | none => pure (afterCaps, 0, 0)  -- unreachable, `p` holds a stone
    else
      pure (afterCaps, captured.size, 0)
  -- During free-handicap placement the turn stays with Black.
  let next := if ps.handicapLeft > 1 then mover else opponent
  checkKo rules.ko ps.history finalBoard next
  return { board := finalBoard
           toMove := next
           captures := (ps.captures.add mover capsByMover).add opponent capsByOpponent
           moveNum := ps.moveNum + 1
           history := ps.history.push (finalBoard, next)
           consecPasses := 0
           lastMove? := some p
           handicapLeft := ps.handicapLeft - 1 }

/-- Pass move. The board is unchanged but the position (with the new player to
move) still enters the history, as situational superko requires.
Passing also forfeits any remaining free-handicap placements. -/
def pass {s : Size} (ps : PlayState s) : PlayState s :=
  let next := ps.toMove.opp
  { ps with toMove := next
            moveNum := ps.moveNum + 1
            consecPasses := ps.consecPasses + 1
            history := ps.history.push (ps.board, next)
            lastMove? := none
            handicapLeft := 0 }

end PlayState

end GoLean
