/-
Authors: Malhar A. Patel
-/

import GoLean.Core.Types

/-!
# The board, the generic region search, and chains

The board is a flat row-major `Vector`, which makes ko, hashing and serialization 1D.
All subsequent functions use `get`/`set` with a `Point`, so the implementation detail is hidden.

There is only one flood fill, `Board.region`, which is generic over a cell predicate.
Chains, liberties, capture detection and territory regions are all instances of it.
-/

namespace GoLean

/-- A Go board of size `s`. -/
structure Board (s : Size) where
  cells : Vector Cell s.cells
  deriving DecidableEq, Repr

namespace Board

/-- The empty board. -/
def empty (s : Size) : Board s :=
  ⟨⟨Array.replicate s.cells none, by simp⟩⟩

/-- Get the cell at a point `p` (total). -/
def get {s : Size} (b : Board s) (p : Point s) : Cell :=
  b.cells[p.idx]

/-- Set the cell at a point `p` (total) to cell `c`. -/
def set {s : Size} (b : Board s) (p : Point s) (c : Cell) : Board s :=
  ⟨b.cells.set p.idx.val c p.idx.isLt⟩

/-- Set every point in PointSet `ps` to cell `c`. -/
def setPoints {s : Size} (b : Board s) (ps : PointSet s) (c : Cell) : Board s :=
  ps.fold (fun bd p => bd.set p c) b

/-- Get the number of cells equal to `c` on the board `b`. -/
def count {s : Size} (b : Board s) (c : Cell) : Nat :=
  b.cells.foldl (fun n x => if x == c then n + 1 else n) 0

/-- Helper for floodfill algorithm. -/
private def regionAux {s : Size} (b : Board s) (same : Cell → Bool) :
    Nat → List (Point s) → PointSet s → PointSet s → PointSet s × PointSet s
  | 0, _, inside, border => (inside, border)
  | _ + 1, [], inside, border => (inside, border)
  | fuel + 1, p :: rest, inside, border =>
    if inside.contains p then
      regionAux b same fuel rest inside border
    else
      let inside := inside.insert p
      let (nbrsSame, nbrsDiff) := p.neighbors.partition (fun q => same (b.get q))
      let border := nbrsDiff.foldl (fun bd q => bd.insert q) border
      regionAux b same fuel (nbrsSame.toList ++ rest) inside border

/-- Get the connected region of point `p` under the cell predicate `same`,
along with its border (the adjacent points not satisfying `same`). -/
def region {s : Size} (b : Board s) (p : Point s) (same : Cell → Bool) :
    PointSet s × PointSet s :=
  /- Fuel: every point is popped at most once per push, and each of the ≤ `s.cells`
  insertions pushes ≤ 4 points, so `5 * s.cells + 5` suffices as fuel. -/
  regionAux b same (5 * s.cells + 5) [p] ∅ ∅

/-- A `Chain` is a maximal connected group of same-colored stones, with its liberties. -/
structure Chain (s : Size) where
  color : Color
  stones : PointSet s
  liberties : PointSet s

/-- Get the chain through the stone at `p`, or `none` if `p` is empty. -/
def chainAt? {s : Size} (b : Board s) (p : Point s) : Option (Chain s) :=
  match b.get p with
  | none => none
  | some col =>
    let (stones, border) := b.region p (· == some col)
    some ⟨col, stones, border.filter (fun q => b.get q == none)⟩

/-! # The board display (for debugging and tests) -/

/-- `X` black, `O` white, `.` empty. -/
def cellChar : Cell → Char
  | some .black => 'X'
  | some .white => 'O'
  | none => '.'

def toStrings {s : Size} (b : Board s) : List String :=
  (List.range s.rows).map fun r =>
    String.ofList <| (List.range s.cols).map fun c =>
      match Point.ofNats? s r c with
      | some p => cellChar (b.get p)
      | none => '?'

instance {s : Size} : ToString (Board s) where
  toString b := String.intercalate "\n" b.toStrings

/-- Build a board from ASCII art rows (`X`/`B` ↦ black, `O`/`W` ↦ white,
other characters ↦ empty). Missing rows/columns are left empty. -/
def ofStrings (s : Size) (rows : List String) : Board s :=
  s.points.foldl (init := Board.empty s) fun bd p =>
    let ch := ((rows[p.r.val]?.getD "").toList[p.c.val]?).getD '.'
    bd.set p <|
      match ch with
      | 'X' | 'x' | 'B' | 'b' => some .black
      | 'O' | 'o' | 'W' | 'w' => some .white
      | _ => none

end Board

end GoLean
