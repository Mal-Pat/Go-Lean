/-
Authors : Malhar A. Patel
-/

import Lean
import Mathlib

inductive Color
  | B
  | W
  deriving DecidableEq, Repr, Inhabited

def printColor : Color → String
  | .B => "Black"
  | .W => "White"

inductive Stone
  | B
  | W
  deriving DecidableEq, Repr, Inhabited

structure GameState (n : Nat) where
  board : Vector (Vector (Option Stone) n) n
  toMove: Color
  prev_board : Option <| Vector (Vector (Option Stone) n) n
  deriving DecidableEq

def emptyBoard (n : Nat) : Vector (Vector (Option Stone) n) n :=
  let r : Vector (Option Stone) n :=
    ⟨Array.replicate n none, by simp⟩
  ⟨Array.replicate n r, by simp⟩

instance {n} : Inhabited (GameState n) where
  default := {
    board := emptyBoard n,
    toMove := Color.B,
    prev_board := none
    }

#check Array.set

#eval (Inhabited.default : GameState 19)

def get {n} (gsn : GameState n) (r c : Fin n) : Option Stone :=
  (gsn.board[r]'(by simp))[c]'(by simp)

def printOptStone : Option Stone → String
| some .B => "●"
| some .W => "○"
| none =>    "+"

def printRow {n} (vec : Vector (Option Stone) n) : String :=
  String.intercalate "" (vec.map printOptStone).toList

def printBoard {n} (bvec : Vector (Vector (Option Stone) n) n) : String :=
  String.intercalate "\n" (bvec.map printRow).toList

instance {n} : Repr <| GameState n where
  reprPrec gsn _ :=
    let h := "To Move: " ++ printColor gsn.toMove ++ "\n"
    let b := printBoard gsn.board
    (h ++ b).toFormat

#eval (Inhabited.default : GameState 19)


































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
