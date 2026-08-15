/-
Authors: Malhar A. Patel
-/

import GoLean.Core.Play

/-!
# The scoring phase

Scoring is a function of the frozen play-phase board plus a set of
dead-marked points.
Clicking a chain will add its entire point set to `deadMarks`, and
any change will reset both players' agreement flags.

Territory uses the Tromp-Taylor definition: after removing dead stones,
an empty region is territory of a color iff its border touches only that color.
-/

namespace GoLean

/-- The territory point sets of both players. -/
structure Territories (s : Size) where
  black : PointSet s := ∅
  white : PointSet s := ∅

/-- Partition the empty points into territory, which are empty regions bordering
exactly one color. Regions bordering both colors or nothing are neutral. -/
def Board.territories {s : Size} (b : Board s) : Territories s := Id.run do
  let mut visited : PointSet s := ∅
  let mut result : Territories s := {}
  for p in s.points do
    if b.get p == none && !visited.contains p then
      let (reg, border) := b.region p (· == none)
      visited := reg.fold (fun v q => v.insert q) visited
      let (touchB, touchW) := border.fold (init := (false, false)) fun (tb, tw) q =>
        match b.get q with
        | some .black => (true, tw)
        | some .white => (tb, true)
        | none => (tb, tw)
      if touchB && !touchW then
        result := { result with black := reg.fold (fun v q => v.insert q) result.black }
      else if touchW && !touchB then
        result := { result with white := reg.fold (fun v q => v.insert q) result.white }
  return result

/-- A full score breakdown. The scores are doubled integers (`.5`-exact). -/
structure ScoreCard where
  method : ScoringMethod
  komi2 : Int
  blackTerritory : Nat := 0
  whiteTerritory : Nat := 0
  /-- Living stones on the cleared board (area scoring). -/
  blackStones : Nat := 0
  whiteStones : Nat := 0
  /-- Captures during play + opponent stones marked dead (territory scoring). -/
  blackPrisoners : Nat := 0
  whitePrisoners : Nat := 0
  blackScore2 : Int := 0
  whiteScore2 : Int := 0
  deriving DecidableEq, Repr

/-- The state of a game in the scoring phase. -/
structure ScoreState (s : Size) where
  /-- The frozen play-phase state. -/
  play : PlayState s
  deadMarks : PointSet s := ∅
  blackAccepted : Bool := false
  whiteAccepted : Bool := false

namespace ScoreState

inductive MarkError where
  | notAChain
  deriving DecidableEq, Repr

/-- Toggle the dead-mark on the entire chain through `p`.
Any change resets both players' agreement. -/
def toggleDead {s : Size} (ss : ScoreState s) (p : Point s) :
    Except MarkError (ScoreState s) :=
  match ss.play.board.chainAt? p with
  | none => .error .notAChain
  | some ch =>
    let marks :=
      if ss.deadMarks.contains p then
        ch.stones.fold (fun m q => m.erase q) ss.deadMarks
      else
        ch.stones.fold (fun m q => m.insert q) ss.deadMarks
    .ok { ss with deadMarks := marks, blackAccepted := false, whiteAccepted := false }

/-- The board after removing all dead-marked stones. -/
def cleared {s : Size} (ss : ScoreState s) : Board s :=
  ss.play.board.setPoints ss.deadMarks none

/-- The number of dead-marked stones of color `col`. -/
def deadCount {s : Size} (ss : ScoreState s) (col : Color) : Nat :=
  ss.deadMarks.fold (fun n p => if ss.play.board.get p == some col then n + 1 else n) 0

/-- Score the position under the given rules and komi. -/
def scoreCard {s : Size} (ss : ScoreState s) (rules : Ruleset) (komi2 : Int) :
    ScoreCard :=
  let cb := ss.cleared
  let terr := cb.territories
  let bT := terr.black.size
  let wT := terr.white.size
  let bS := cb.count (some .black)
  let wS := cb.count (some .white)
  let bP := ss.play.captures.black + ss.deadCount .white
  let wP := ss.play.captures.white + ss.deadCount .black
  let (b2, w2) : Int × Int :=
    match rules.scoring with
    | .territory => (((2 * (bT + bP) : Nat) : Int), ((2 * (wT + wP) : Nat) : Int) + komi2)
    | .area => (((2 * (bT + bS) : Nat) : Int), ((2 * (wT + wS) : Nat) : Int) + komi2)
  { method := rules.scoring, komi2
    blackTerritory := bT, whiteTerritory := wT
    blackStones := bS, whiteStones := wS
    blackPrisoners := bP, whitePrisoners := wP
    blackScore2 := b2, whiteScore2 := w2 }

end ScoreState

end GoLean
