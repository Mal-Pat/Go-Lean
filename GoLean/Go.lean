/-
Authors : Malhar A. Patel
-/

import Lean
import Mathlib

/-- Stone Type -/
inductive Stone
  | B
  | W
  deriving DecidableEq, Repr, Inhabited

/-- Prints Stone Color -/
def printStone : Stone → String
  | .B => "Black"
  | .W => "White"

/-- Next Turn -/
def nextTurn : Stone → Stone
  | .B => .W
  | .W => .B

/-- Size of board -/
structure Size where
  rl : Nat
  cl : Nat
  two_le_rl : 2 ≤ rl := by decide
  two_le_cl : 2 ≤ cl := by decide

/-- Notation for `Size` -/
notation "s[" rl "," cl "]" => Size.mk rl cl

/-- Board -/
abbrev Board (s : Size) := Vector (Vector (Option Stone) s.cl) s.rl

/--
The Game State, containing the board, next color to move,
and previous board to check for ko.
-/
structure GameState (s : Size) where
  board : Board s
  toMove : Stone
  prev_board : Option <| Board s

/--
Point structure which contains `row` and `col`, and
the proof that both are less than `r.len` and `c.len` respectively
-/
structure Point (s : Size) where
  r : Nat
  c : Nat
  r_lt_n : r < s.rl := by decide
  c_lt_n : c < s.cl := by decide
  deriving DecidableEq, Repr

/-- Notation for `Point` -/
notation "p[" a "," b "," s "]" => @Point.mk s a b (by decide) (by decide)

def Board.getOptStone {s} (board : Board s) (p : Point s)
    : Option Stone :=
  (board[p.r]'(p.r_lt_n))[p.c]'(p.c_lt_n)

-- structure StoneGroup {s} (board : Board s) where
--   size : Nat
--   group : Vector (Point n) size
--   num_liberties : Nat
--   liberties : Vector (Point n) num_liberties
--   st : Stone
--   valid : ∀ p ∈ group.toArray, getOptStone h gsn p = some st

-- structure AllStoneGroups {n h} (gsn : GameState n h) where
--   groups : Array <| StoneGroup gsn
--   complete {st} : ∀ p, getOptStone h gsn p = some st →
--                     ∃ gp ∈ groups, ∃ q ∈ gp.group, p = q

-- def getAllGroups {n h} (gsn : GameState n h) : AllStoneGroups gsn :=
--   sorry

/-- Create an empty board (filled with `none`) of size `s` -/
def emptyBoard (s : Size) : Board s :=
  let row : Vector (Option Stone) s.cl :=
    ⟨Array.replicate s.cl none, by simp⟩
  ⟨Array.replicate s.rl row, by simp⟩

instance {s} : Inhabited (GameState s) where
  default := {
    board := emptyBoard s,
    toMove := Stone.B,
    prev_board := none
    }

#check Array.set

/-- Default 19 × 19 board size -/
def dfltSize : Size := Size.mk 19 19

/-- Default 19 × 19 starting game state -/
def dfltGameState : GameState dfltSize := Inhabited.default

/-- Gets the 4 neighbouring points of a point -/
def getNbhdPoints {s} (p : Point s)
    : Vector (Option <| Point s) 4 :=
  let up : Option <| Point s :=
    if p.r == 0 then none
    else some ⟨p.r - 1, p.c, by grind [p.r_lt_n], p.c_lt_n⟩
  let down : Option <| Point s :=
    if row_eq_n : p.r == s.rl - 1 then none
    else some ⟨p.r + 1, p.c, by grind [p.r_lt_n], p.c_lt_n⟩
  let left : Option <| Point s :=
    if p.c == 0 then none
    else some ⟨p.r, p.c - 1, p.r_lt_n, by grind[p.c_lt_n]⟩
  let right : Option <| Point s :=
    if row_eq_n : p.c == s.cl - 1 then none
    else some ⟨p.r, p.c + 1, p.r_lt_n, by grind[p.c_lt_n]⟩
  ⟨#[up, down, left, right], by simp⟩

def isValid {s} (gs : GameState s) (p : Point s)
    : Bool × String :=
  sorry

def playAt {s} (gs : GameState s) (p : Point s)
    : Except String <| GameState s :=
  let board := gs.board
  let ⟨valid, msg⟩ := isValid gs p
  -- let valid := true
  -- let msg := ""
  if valid then
    let row := board[p.r]'(p.r_lt_n)
    let modified_row := row.set p.c (some gs.toMove) (p.c_lt_n)
    let modified_board := board.set p.r modified_row p.r_lt_n
    Except.ok ⟨modified_board, nextTurn gs.toMove, some board⟩
  else
    Except.error s!"Invalid Move! {msg}"

/-- Pass only changes `toMove`; the board remains the same -/
def pass {s} (gs : GameState s) : GameState s :=
  {gs with toMove := nextTurn gs.toMove}

def printOptStone : Option Stone → String
| some .B => "●"
| some .W => "○"
| none =>    "+"

def printRow {n} (vec : Vector (Option Stone) n) : String :=
  String.intercalate "" (vec.map printOptStone).toList

def printBoard {s} (board : Board s) : String :=
  String.intercalate "\n" (board.map printRow).toList

instance {s} : Repr <| GameState s where
  reprPrec gs _ :=
    let header := "To Move: " ++ printStone gs.toMove ++ "\n"
    let brd := printBoard gs.board
    (header ++ brd).toFormat

#eval dfltSize

#eval dfltGameState

#check Point dfltSize

#eval (@Point.mk (dfltSize) 1 0 (by decide) (by decide))

#check @Point.mk dfltSize 1 0

-- #eval playAt dfltGameState (@Point.mk (dfltSize) 18 4 (by decide) (by decide))

#eval {r := 1, c := 2 : Point (Size.mk 19 19)}

#eval p[1,2,dfltSize]





























  -- have h : r * n + c < board.barr.size := by
  --   rw [board.barr_size]
  --   calc
  --     r * n + c < r * n + n := by grind
  --     _ ≤ (n - 1) * n + n := by
  --       have : r * n ≤ (n - 1) * n :=
  --         Nat.mul_le_mul_right n (by grind)
  --       grind
  --     _ = n * n := by
  --       rw [Nat.mul_sub_right_distrib, Nat.one_mul, Nat.sub_add_cancel]
  --       nth_rw 1 [← Nat.one_mul n]
  --       apply Nat.mul_le_mul_right
  --       have : c < n := by grind
  --       linarith
