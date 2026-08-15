/-
Authors: Malhar A. Patel
-/

import GoLean.Core.Game

/-!
# Core engine tests

`#guard`-based: each check runs at elaboration time, so `lake build Tests`
IS the test run. Covers captures (corner, multi-stone), simple ko and
superko, self-capture per ruleset, pass→scoring, dead marks and both
scoring paths, resume, undo, resignation, and handicap (fixed + free).
-/

namespace GoLean.Tests

open GoLean

/-! ## Helpers -/

def size5 : Size := { rows := 5, cols := 5 }
def size9 : Size := { rows := 9, cols := 9 }

def cfg5 : GameConfig := { size := size5 }

def run (c : GameConfig) (as : List Action) : Except IllegalAction Game :=
  match Game.new c with
  | .error _ => .error .wrongPhase
  | .ok g => as.foldlM Game.step g

/-- `some none` = in bounds and empty; `some (some col)` = a stone. -/
def cellAt (eg : Except IllegalAction Game) (r c : Nat) : Option Cell :=
  match eg with
  | .error _ => none
  | .ok g => (Point.ofNats? g.config.size r c).map fun p => g.curBoard.get p

def isErr (eg : Except IllegalAction Game) (e : IllegalAction) : Bool :=
  match eg with
  | .error e' => e' == e
  | .ok _ => false

def phaseName (eg : Except IllegalAction Game) : String :=
  match eg with
  | .error _ => "error"
  | .ok g =>
    match g.phase with
    | .playing _ => "playing"
    | .scoring _ => "scoring"
    | .finished _ _ => "finished"

def toMoveOf (eg : Except IllegalAction Game) : Option Color :=
  match eg with
  | .ok g => some g.curPlayState.toMove
  | .error _ => none

def capturesOf (eg : Except IllegalAction Game) : Option Captures :=
  match eg with
  | .ok g => some g.curPlayState.captures
  | .error _ => none

def resultOf (eg : Except IllegalAction Game) : Option String :=
  match eg with
  | .ok g =>
    match g.phase with
    | .finished _ r => some r.format
    | _ => none
  | .error _ => none

def boardStrings (eg : Except IllegalAction Game) : List String :=
  match eg with
  | .ok g => g.curBoard.toStrings
  | .error _ => []

/-! ## Captures -/

-- Single-stone corner capture: Black takes W(0,0).
def tCorner := run cfg5 [.play 0 1, .play 0 0, .play 1 0]
#guard cellAt tCorner 0 0 == some none
#guard capturesOf tCorner == some { black := 1, white := 0 }

-- Two-stone group capture: W(0,0)+(1,0) die together.
def tGroup := run cfg5 [.play 0 1, .play 0 0, .play 1 1, .play 1 0, .play 2 0]
#guard cellAt tGroup 0 0 == some none
#guard cellAt tGroup 1 0 == some none
#guard capturesOf tGroup == some { black := 2, white := 0 }

-- Playing into an occupied point.
#guard isErr (run cfg5 [.play 2 2, .play 2 2]) .occupied
-- Playing off the board.
#guard isErr (run cfg5 [.play 9 9]) .outOfBoard

/-! ## Ko and superko

Classic ko shape: after `koMoves`, W(1,1) has just captured B(1,2);
Black recapturing at (1,2) would recreate the previous position. -/

def koMoves : List Action :=
  [.play 0 1, .play 0 2, .play 1 0, .play 1 3,
   .play 2 1, .play 2 2, .play 1 2, .play 1 1]

def cfgKo (k : KoRule) : GameConfig := { size := size5, ruleset := { ko := k } }

-- Immediate recapture is an illegal ko under simple ko and both superkos…
#guard isErr (run (cfgKo .simple) (koMoves ++ [.play 1 2])) (.koViolation .simple)
#guard isErr (run (cfgKo .positionalSuperko) (koMoves ++ [.play 1 2]))
  (.koViolation .positionalSuperko)
#guard isErr (run (cfgKo .situationalSuperko) (koMoves ++ [.play 1 2]))
  (.koViolation .situationalSuperko)
-- …but legal with the ko rule off…
#guard phaseName (run (cfgKo .none) (koMoves ++ [.play 1 2])) == "playing"
-- …and legal after a ko threat exchange (board now differs), even for superko.
#guard phaseName (run (cfgKo .simple) (koMoves ++ [.play 4 4, .play 4 3, .play 1 2]))
  == "playing"
#guard phaseName
  (run (cfgKo .positionalSuperko) (koMoves ++ [.play 4 4, .play 4 3, .play 1 2]))
  == "playing"

/-! ## Self-capture -/

def scMoves : List Action := [.play 0 1, .play 4 4, .play 1 0, .play 0 0]

-- Forbidden by default (Japanese-style)…
#guard isErr (run cfg5 scMoves) .selfCapture
-- …allowed when toggled on: the stone is removed and Black gets a prisoner.
def cfgSC : GameConfig :=
  { size := size5, ruleset := { selfCaptureAllowed := true } }
def tSC := run cfgSC scMoves
#guard cellAt tSC 0 0 == some none
#guard capturesOf tSC == some { black := 1, white := 0 }

/-! ## Passing, scoring, agreement -/

-- Two consecutive passes end the play phase.
#guard phaseName (run cfg5 [.play 2 2, .pass, .pass]) == "scoring"
#guard phaseName (run cfg5 [.play 2 2, .pass, .play 3 3, .pass]) == "playing"

-- Lone black stone, territory scoring: 24 territory vs komi 6.5 → B+17.5.
def tScore := run cfg5 [.play 2 2, .pass, .pass, .accept .black, .accept .white]
#guard phaseName tScore == "finished"
#guard resultOf tScore == some "B+17.5"

-- Area scoring (Chinese): 24 territory + 1 stone vs komi 7.5 → B+17.5.
def cfgCh : GameConfig := { size := size5, ruleset := .chinese, komi2 := 15 }
#guard resultOf (run cfgCh [.play 2 2, .pass, .pass, .accept .black, .accept .white])
  == some "B+17.5"

-- Marking a chain dead: W(4,4) dead → prisoner + its point becomes territory.
def tDead := run cfg5
  [.play 2 2, .play 4 4, .pass, .pass,
   .toggleDead 4 4, .accept .black, .accept .white]
#guard resultOf tDead == some "B+18.5"

-- Toggling twice restores the position; accepting after marks reset works.
def tDeadTwice := run cfg5
  [.play 2 2, .play 4 4, .pass, .pass, .toggleDead 4 4, .toggleDead 4 4]
#guard phaseName tDeadTwice == "scoring"

-- An accept followed by a mark change must reset the agreement.
def tReAccept := run cfg5
  [.play 2 2, .play 4 4, .pass, .pass,
   .accept .black, .toggleDead 4 4, .accept .black, .accept .white]
#guard resultOf tReAccept == some "B+18.5"

-- Marking an empty point is rejected.
#guard isErr (run cfg5 [.play 2 2, .pass, .pass, .toggleDead 0 0]) .notAChain

-- Resume returns to play.
def tResume := run cfg5 [.play 2 2, .pass, .pass, .resume]
#guard phaseName tResume == "playing"
#guard toMoveOf tResume == some .white

-- Draw when komi exactly balances (komi 24 on an empty-ish 5×5).
def cfgDraw : GameConfig := { size := size5, komi2 := 48 }
#guard resultOf (run cfgDraw [.play 2 2, .pass, .pass, .accept .black, .accept .white])
  == some "Draw"

/-! ## Resign, undo -/

#guard resultOf (run cfg5 [.play 2 2, .resign]) == some "B+R"
#guard resultOf (run cfg5 [.play 2 2, .play 3 3, .resign]) == some "W+R"

-- Undo rewinds exactly one stone placement.
def tUndo := run cfg5 [.play 2 2, .play 3 3, .undo]
def tOne := run cfg5 [.play 2 2]
#guard boardStrings tUndo == boardStrings tOne
#guard toMoveOf tUndo == toMoveOf tOne
#guard isErr (run cfg5 [.undo]) .nothingToUndo

-- Undo after an undone-and-replayed ko history is still consistent:
-- replaying the truncated log restores the same phase.
#guard phaseName (run (cfgKo .simple) (koMoves ++ [.undo])) == "playing"

/-! ## Handicap -/

-- Fixed placement on 9×9: stones on the star points, White to move.
def cfgH2 : GameConfig := { size := size9, handicap := 2 }
def tH2 := run cfgH2 []
#guard cellAt tH2 2 6 == some (some .black)
#guard cellAt tH2 6 2 == some (some .black)
#guard toMoveOf tH2 == some .white

-- Out-of-range fixed handicap is a config error.
#guard (Game.new { size := size9, handicap := 7 } |>.isOk) == false
#guard (Game.new { size := size9, handicap := 5 } |>.isOk) == true

-- Free placement on a nonstandard board: Black keeps the turn.
def cfgFree : GameConfig := { size := { rows := 5, cols := 7 }, handicap := 3 }
#guard toMoveOf (run cfgFree [.play 0 0, .play 0 2]) == some .black
#guard toMoveOf (run cfgFree [.play 0 0, .play 0 2, .play 0 4]) == some .white

/-! ## Event-sourcing invariant: the log replays to the same state -/

def tReplay :=
  match run cfg5 [.play 2 2, .play 3 3, .pass, .pass, .toggleDead 3 3] with
  | .error _ => false
  | .ok g =>
    match Game.ofRecord g.config g.actions with
    | .error _ => false
    | .ok g' => g.curBoard.toStrings == g'.curBoard.toStrings
        && phaseName (.ok g) == phaseName (.ok g')
#guard tReplay

end GoLean.Tests
