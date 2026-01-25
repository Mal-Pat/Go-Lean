/-
Authors : Malhar A. Patel
-/

import Lean
import Mathlib

inductive Stone
  | B
  | W
  deriving DecidableEq, Repr, Inhabited

def printStone : Stone → String
  | .B => "Black"
  | .W => "White"

def nextTurn : Stone → Stone
  | .B => .W
  | .W => .B

/--
The Game State, containing the board, next color to move,
and previous board to check for ko.

`h : 2 ≤ n` is an argument so that `Inhabited GameState n h` can be constructed.
-/
structure GameState (n : Nat) (h : 2 ≤ n := by decide) where
  board : Vector (Vector (Option Stone) n) n
  toMove : Stone
  prev_board : Option <| Vector (Vector (Option Stone) n) n

structure Point (n : Nat) where
  row : Nat
  col : Nat
  row_lt_n : row < n := by decide
  col_lt_n : col < n := by decide
  deriving DecidableEq, Repr

def getOptStone {n} (h : 2 ≤ n := by decide) (gsn : GameState n h) (p : Point n)
    : Option Stone :=
  (gsn.board[p.row]'(p.row_lt_n))[p.col]'(p.col_lt_n)

structure StoneGroup {n h} (gsn : GameState n h) where
  size : Nat
  group : Vector (Point n) size
  num_liberties : Nat
  liberties : Vector (Point n) num_liberties
  st : Stone
  valid : ∀ p ∈ group.toArray, getOptStone h gsn p = some st

structure AllStoneGroups {n h} (gsn : GameState n h) where
  groups : Array <| StoneGroup gsn
  complete {st} : ∀ p, getOptStone h gsn p = some st →
                    ∃ gp ∈ groups, ∃ q ∈ gp.group, p = q

def getAllGroups {n h} (gsn : GameState n h) : AllStoneGroups gsn :=
  sorry

#check Nat.noConfusion

def emptyBoard (n : Nat) : Vector (Vector (Option Stone) n) n :=
  let r : Vector (Option Stone) n :=
    ⟨Array.replicate n none, by simp⟩
  ⟨Array.replicate n r, by simp⟩

instance {n} {h : 2 ≤ n} : Inhabited (GameState n h) where
  default := {
    board := emptyBoard n,
    toMove := Stone.B,
    prev_board := none
    }

#check Array.set

#eval (Inhabited.default : GameState 19)

def dflt : GameState 19 :=
  Inhabited.default

def get_old {n} (h : 2 ≤ n := by decide) (gsn : GameState n h)
    (r c : Fin n) : Option Stone :=
  (gsn.board[r]'(by simp))[c]'(by simp)

#eval get_old _ (Inhabited.default : GameState 19) 1 1

def getNeighborPoints {n} (h : 2 ≤ n := by decide) (p : Point n)
    : Vector (Option <| Point n) 4 :=
  let up : Option <| Point n :=
    if p.row == 0 then none
    else some ⟨p.row - 1, p.col, by grind [p.row_lt_n], p.col_lt_n⟩
  let down : Option <| Point n :=
    if row_eq_n : p.row == n - 1 then none
    else some ⟨p.row + 1, p.col, by grind [p.row_lt_n], p.col_lt_n⟩
  let left : Option <| Point n :=
    if p.col == 0 then none
    else some ⟨p.row, p.col - 1, p.row_lt_n, by grind[p.col_lt_n]⟩
  let right : Option <| Point n :=
    if row_eq_n : p.col == n - 1 then none
    else some ⟨p.row, p.col + 1, p.row_lt_n, by grind[p.col_lt_n]⟩
  ⟨#[up, down, left, right], by simp⟩

def playAt {n} {h : 2 ≤ n} (gsn : GameState n h) (p : Point n)
    : GameState n h :=
  let board := gsn.board
  let row := board[p.row]'(p.row_lt_n)
  let modified_row := row.set p.col (some gsn.toMove) (p.col_lt_n)
  let modified_board := board.set p.row modified_row p.row_lt_n
  ⟨modified_board, nextTurn gsn.toMove, some board⟩

def printOptStone : Option Stone → String
| some .B => "●"
| some .W => "○"
| none =>    "+"

def printRow {n} (vec : Vector (Option Stone) n) : String :=
  String.intercalate "" (vec.map printOptStone).toList

def printBoard {n} (bvec : Vector (Vector (Option Stone) n) n) : String :=
  String.intercalate "\n" (bvec.map printRow).toList

instance {n} {h : 2 ≤ n} : Repr <| GameState n h where
  reprPrec gsn _ :=
    let header := "To Move: " ++ printStone gsn.toMove ++ "\n"
    let brd := printBoard gsn.board
    (header ++ brd).toFormat

#eval (Inhabited.default : GameState 19)

#eval dflt

#eval playAt dflt (.mk 1 0)































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
