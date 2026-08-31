/-
Authors: Malhar A. Patel
-/

import Std.Data.HashSet

/-!
# Basic types for the game of Go

`Color`, `Size`, `Point`, `Cell`, `PointSet`, star points, fixed-handicap
placement and coordinate labels.
-/

namespace GoLean

/-- Stone color. -/
inductive Color where
  | black
  | white
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Color

/-- The opposite color. -/
def opp : Color → Color
  | black => white
  | white => black

instance : ToString Color where
  toString
    | black => "Black"
    | white => "White"

end Color

/-- The board dimensions, where both `rows` and `cols` must be at least 2. -/
structure Size where
  rows : Nat
  cols : Nat
  rows_ge : 2 ≤ rows := by decide
  cols_ge : 2 ≤ cols := by decide
  deriving DecidableEq

instance : Inhabited Size := ⟨{ rows := 19, cols := 19 }⟩

namespace Size

/-- Convert the number of `rows` and `cols` to `Size`, if both are ≥ 2. -/
def ofNats? (rows cols : Nat) : Option Size :=
  if h : 2 ≤ rows ∧ 2 ≤ cols then some ⟨rows, cols, h.1, h.2⟩ else none

/-- Get the total number of intersections on a board of size `s`. -/
abbrev cells (s : Size) : Nat := s.rows * s.cols

theorem cols_pos (s : Size) : 0 < s.cols :=
  Nat.lt_of_lt_of_le (by decide) s.cols_ge

theorem rows_pos (s : Size) : 0 < s.rows :=
  Nat.lt_of_lt_of_le (by decide) s.rows_ge

end Size

/-- A `Cell` is an intersection that can be a stone or empty. -/
abbrev Cell := Option Color

/-- A `Point` is an intersection on an `s`-sized board. -/
structure Point (s : Size) where
  r : Fin s.rows
  c : Fin s.cols
  deriving DecidableEq, Repr, Hashable

/-- The set of points on a board of size `s`. -/
abbrev PointSet (s : Size) := Std.HashSet (Point s)

namespace Point

/-- Convert `(r,c)` on a board of size `s` to a `Point s`, if possible. -/
def ofNats? (s : Size) (r c : Nat) : Option (Point s) :=
  if h : r < s.rows ∧ c < s.cols then some ⟨⟨r, h.1⟩, ⟨c, h.2⟩⟩ else none

/-- Get the flat index of a point (row-major) `p`. -/
def idx {s : Size} (p : Point s) : Fin s.cells :=
  ⟨p.r.val * s.cols + p.c.val, by
    calc p.r.val * s.cols + p.c.val
        < p.r.val * s.cols + s.cols := Nat.add_lt_add_left p.c.isLt _
      _ = (p.r.val + 1) * s.cols := (Nat.succ_mul _ _).symm
      _ ≤ s.rows * s.cols := Nat.mul_le_mul_right _ p.r.isLt⟩

/-- Get the point from a flat index (row-major) `i`. -/
def ofIdx {s : Size} (i : Fin s.cells) : Point s :=
  ⟨⟨i.val / s.cols, Nat.div_lt_of_lt_mul (Nat.mul_comm s.rows s.cols ▸ i.isLt)⟩,
   ⟨i.val % s.cols, Nat.mod_lt _ s.cols_pos⟩⟩

/-- The orthogonal neighbors of point `p`, which are in-bounds by construction. -/
def neighbors {s : Size} (p : Point s) : Array (Point s) :=
  #[ if _h : 0 < p.r.val then
       some ⟨⟨p.r.val - 1, by have := p.r.isLt; omega⟩, p.c⟩ else none,
     if h : p.r.val + 1 < s.rows then
       some ⟨⟨p.r.val + 1, h⟩, p.c⟩ else none,
     if _h : 0 < p.c.val then
       some ⟨p.r, ⟨p.c.val - 1, by have := p.c.isLt; omega⟩⟩ else none,
     if h : p.c.val + 1 < s.cols then
       some ⟨p.r, ⟨p.c.val + 1, h⟩⟩ else none
   ].filterMap id

end Point

namespace Size

/-- All points on a board of size `s`, in row-major order. -/
def points (s : Size) : Array (Point s) :=
  Array.ofFn (n := s.cells) Point.ofIdx

/-- The star points for the standard square sizes; `[]` otherwise. -/
def starPoints (s : Size) : List (Point s) :=
  let mk (l : List (Nat × Nat)) : List (Point s) :=
    l.filterMap fun (r, c) => Point.ofNats? s r c
  match s.rows, s.cols with
  | 9, 9 => mk [(2, 2), (2, 6), (4, 4), (6, 2), (6, 6)]
  | 13, 13 => mk [(3, 3), (3, 9), (6, 6), (9, 3), (9, 9)]
  | 19, 19 => mk [(3, 3), (3, 9), (3, 15), (9, 3), (9, 9), (9, 15), (15, 3), (15, 9), (15, 15)]
  | _, _ => []

/-- Get the largest fixed handicap available on a board of size `s`
(0 means fixed placement is unsupported; use free placement instead). -/
def maxFixedHandicap (s : Size) : Nat :=
  match s.rows, s.cols with
  | 9, 9 => 5
  | 13, 13 => 9
  | 19, 19 => 9
  | _, _ => 0

/-- Get the star points used for a fixed handicap of `n` stones, in the traditional
order (upper right, lower left, lower right, upper left, sides, center).
Returns `none` if fixed placement is unsupported for this size or `n`. -/
def fixedHandicapPoints (s : Size) (n : Nat) : Option (List (Point s)) := do
  if n < 2 || n > s.maxFixedHandicap then failure
  let (e, mid) ←
    if s == {rows := 9, cols := 9} then pure (2, 4)
    else if s == {rows := 13, cols := 13} then pure (3, 6)
    else if s == {rows := 19, cols := 19} then pure (3, 9)
    else failure
  let hi := s.rows - 1 - e
  let ur := (e, hi)
  let ll := (hi, e)
  let lr := (hi, hi)
  let ul := (e, e)
  let left := (mid, e)
  let right := (mid, hi)
  let top := (e, mid)
  let bottom := (hi, mid)
  let center := (mid, mid)
  let coords : List (Nat × Nat) :=
    match n with
    | 2 => [ur, ll]
    | 3 => [ur, ll, lr]
    | 4 => [ur, ll, lr, ul]
    | 5 => [ur, ll, lr, ul, center]
    | 6 => [ur, ll, lr, ul, left, right]
    | 7 => [ur, ll, lr, ul, left, right, center]
    | 8 => [ur, ll, lr, ul, left, right, top, bottom]
    | 9 => [ur, ll, lr, ul, left, right, top, bottom, center]
    | _ => []
  coords.mapM fun (r, c) => Point.ofNats? s r c

end Size

/-- Standard alphabet column label, skipping `I`.
Falls back to numbers on huge boards. -/
def colLabel (c : Nat) : String :=
  let letters := "ABCDEFGHJKLMNOPQRSTUVWXYZ"
  match letters.toList[c]? with
  | some ch => String.singleton ch
  | none => toString (c + 1)

/-- Format a doubled integer (`13` ↦ `"6.5"`, `14` ↦ `"7"`).
Used for komi and scores, which are exact half-integers. -/
def formatHalfInt (n2 : Int) : String :=
  let sign := if n2 < 0 then "-" else ""
  let n2abs := n2.natAbs
  sign ++ toString (n2abs / 2) ++ (if n2abs % 2 == 1 then ".5" else "")

end GoLean
