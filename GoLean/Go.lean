/-
Authors : Malhar A. Patel
-/

import Lean

/-- Color Type -/
inductive Color
  | B
  | W
  deriving DecidableEq, Repr, Inhabited

/-- Prints Color Color -/
def printColor : Color → String
  | .B => "Black"
  | .W => "White"

/-- Next Turn -/
def nextTurn : Color → Color
  | .B => .W
  | .W => .B

abbrev oppColor := nextTurn

/-- Size of board -/
structure Size where
  rl : Nat
  cl : Nat
  two_le_rl : 2 ≤ rl := by decide
  two_le_cl : 2 ≤ cl := by decide

/-- Notation for `Size` -/
notation "s[" rl "," cl "]" => Size.mk rl cl

/-- Board -/
abbrev Board (s : Size) := Vector (Vector (Option Color) s.cl) s.rl

/--
The Game State, containing the board, next color to move,
and previous board to check for ko.
-/
structure GameState (s : Size) where
  board : Board s
  toMove : Color
  prev_board? : Option <| Board s
  capturedW : Nat
  capturedB : Nat
  msg : String
  moveNum : Nat

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

structure Value (s : Size) where
  color? : Option Color
  point : Point s

structure Stone (s : Size) where
  color : Color
  point : Point s

def Stone.getValue {s} (st : Stone s)
    : Value s :=
  ⟨some st.color, st.point⟩

def Value.getStone? {s} (v : Value s)
    : Option <| Stone s :=
  match v.color? with
  | none => none
  | some color => some ⟨color, v.point⟩

/-- Create an empty board (filled with `none`) of size `s` -/
def emptyBoard {s : Size} : Board s :=
  let row : Vector (Option Color) s.cl :=
    ⟨Array.replicate s.cl none, by simp⟩
  ⟨Array.replicate s.rl row, by simp⟩

def defaultMsg : String := "Valid Move"

instance {s} : Inhabited (GameState s) where
  default := {
    board := emptyBoard,
    toMove := Color.B,
    prev_board? := none,
    capturedW := 0,
    capturedB := 0,
    msg := defaultMsg,
    moveNum := 0
    }

def startGame {s : Size} : GameState s :=
  default

/-- Default 19 × 19 board size -/
def dfltSize : Size := Size.mk 19 19

/-- Default 19 × 19 starting game state -/
def dfltGameState : GameState dfltSize := Inhabited.default

abbrev PointsArr (s : Size) := Array <| Point s
abbrev PointsList (s : Size) := List <| Point s
abbrev ValuesArr (s : Size) := Array <| Value s
abbrev StonesArr (s : Size) := Array <| Stone s

/-- Get some color or none at point `p` on `board` -/
def Board.getColorAt? {s} (board : Board s) (p : Point s)
    : Option Color :=
  (board[p.r]'(p.r_lt_n))[p.c]'(p.c_lt_n)

/-- Check if `p` is empty -/
def Board.isEmptyPoint {s} (board : Board s) (p : Point s)
    : Bool :=
  match board.getColorAt? p with
  | none => true
  | some _ => false

def Board.getValueAt {s} (board : Board s) (p : Point s)
    : Value s :=
  ⟨board.getColorAt? p, p⟩

def Board.getStoneAt? {s} (board : Board s) (p : Point s)
    : Option <| Stone s :=
  match board.getColorAt? p with
  | none => none
  | some color => some ⟨color, p⟩

def Board.getValuesAt {s} (board : Board s) (parr : PointsArr s)
    : ValuesArr s :=
  parr.map fun p => board.getValueAt p

def Board.getStonesAt? {s} (board : Board s) (parr : PointsArr s)
    : Option <| StonesArr s :=
  parr.mapM fun p => board.getStoneAt? p -- Ensure that this works correctly

def StonesArr.getPointsFrom {s} (starr : StonesArr s) -- Ensure that `StonesArr.` works
    : PointsArr s :=
  starr.map fun st => st.point

def ValuesArr.getPointsFrom {s} (varr : ValuesArr s)
    : PointsArr s :=
  varr.map fun v => v.point

def ValuesArr.toStoneArr {s} (varr : ValuesArr s)
    : StonesArr s :=
  varr.filterMap Value.getStone?

def StonesArr.filterColor {s} (starr : StonesArr s) (color : Color)
    : StonesArr s :=
  starr.filter (fun st => st.color == color)

/-- Check if all `points` have same `value` -/
def Board.checkSame {s} (board : Board s) (value : Option Color) (points : PointsList s)
    : Bool :=
  match points with
  | [] => true
  | p :: rest =>
    if board.getColorAt? p == value then
      board.checkSame value rest
    else
      false

structure ValueGroup (s : Size) where
  value : Option Color
  points : PointsArr s
  liberties : PointsArr s
  deriving Repr, DecidableEq

/-- Check if ValueGroup `vg` is valid on `board`,
    that is, every point in `vg` must have same value -/
def ValueGroup.check {s} (vg : ValueGroup s) (board : Board s)
    : Bool :=
  board.checkSame vg.value vg.points.toList

/-- Get number of liberties of a ValueGroup `vg` -/
def ValueGroup.getNumLibs {s} (vg : ValueGroup s)
    : Nat :=
  vg.liberties.size

structure StoneGroup (s : Size) where
  color : Color
  points : PointsArr s
  liberties : PointsArr s
  deriving Repr, DecidableEq

#eval List.Perm [1,2,6,3] [6,2,3,1]

/-- Check if two StoneGroups are equal -/
def StoneGroup.isEqualTo {s} (stg1 stg2 : StoneGroup s)
    : Bool :=
  let b1 := stg1.color == stg2.color
  let b2 := List.Perm stg1.points.toList stg2.points.toList
  b1 && b2

abbrev StoneGroupsArr (s : Size) := Array <| StoneGroup s
abbrev StoneGroupsList (s : Size) := List <| StoneGroup s

#check Array.foldl

/-- Check if a list of StoneGroups contains a particular StoneGroup -/
def StoneGroupsList.contains {s} (stgl : StoneGroupsList s) (target_stg : StoneGroup s)
    : Bool :=
  match stgl with
  | [] => false
  | stg :: rest =>
    match target_stg.isEqualTo stg with
    | true => true
    | false => rest.contains target_stg

/-- Delete duplicate StoneGroups from Array of StoneGroups -/
def StoneGroupsArr.deldups {s} (stgarr : StoneGroupsArr s)
    : StoneGroupsArr s :=
  let stgl := stgarr.toList
  let unqstgl := stgl.foldl
    (fun unql stg => if unql.contains stg then unql else stg :: unql)
    []
  unqstgl.toArray

def StoneGroup.check {s} (stg : StoneGroup s) (board : Board s)
    : Bool :=
  board.checkSame stg.color stg.points.toList

/-- Get number of liberties of a StoneGroup `stg` -/
def StoneGroup.getNumLibs {s} (stg : StoneGroup s)
    : Nat :=
  stg.liberties.size

def StoneGroup.size {s} (stg : StoneGroup s)
    : Nat :=
  stg.points.size

def StoneGroupsArr.totalSize {s} (stgarr : StoneGroupsArr s)
    : Nat :=
  stgarr.foldl (fun n stg => n + stg.size) 0

/-- Convert a `ValueGroup` to a `StoneGroup` if possible -/
def ValueGroup.getStoneGroup? {s} (vg : ValueGroup s)
    : Option <| StoneGroup s :=
  match vg.value with
  | none => none
  | some color => some ⟨color, vg.points, vg.liberties⟩

/-- Convert a `StoneGroup` to a `ValueGroup` -/
def StoneGroup.getValueGroup {s} (stg : StoneGroup s)
    : ValueGroup s :=
  ⟨some stg.color, stg.points, stg.liberties⟩

/-- Get the neighboring points of point `p` -/
def Point.getNbhdPoints {s} (p : Point s)
    : PointsArr s :=
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
  #[up, down, left, right].filterMap id
  -- or #[up, down, left, right].filter fun p => (p != none)

/-- Get the neighboring stones of point `p` on `board` -/
def Board.getNbhdValuesAt {s} (board : Board s) (p : Point s)
    : ValuesArr s :=
  let nbhdpoints := p.getNbhdPoints
  board.getValuesAt nbhdpoints

def Board.getNbhdStonesAt {s} (board : Board s) (p : Point s)
    : StonesArr s :=
  let nbhdValues := board.getNbhdValuesAt p
  nbhdValues.toStoneArr

/-- Delete duplicates in a list -/
def deldups {α} [DecidableEq α] (l : List α) : List α :=
  l.foldl (fun unql a => if a ∈ unql then unql else a :: unql) []

partial def floodFill {s} (board : Board s) (queue : PointsList s)
  (visited : PointsList s) (liberties : PointsList s) (empty : Bool)
    : (PointsList s) × (PointsList s) :=
  match queue with
  | [] =>
    let uniqueLibs := deldups liberties
    (visited, uniqueLibs)
  | cur :: rest =>
    if cur ∈ visited then
      floodFill board rest visited liberties empty
    else
      let nbhdPoints := cur.getNbhdPoints
      let (same, diff) := nbhdPoints.partition
        fun p => (board.getColorAt? cur == board.getColorAt? p)
      let libs :=
        if empty then
          diff
        else
          diff.filter fun p => (board.getColorAt? p == none)
      floodFill board (rest ++ same.toList) (cur :: visited) (liberties ++ libs.toList) empty

/-- Get the ValueGroup at point `p` on `board` -/
def Board.getValueGroupAt {s} (board : Board s) (p : Point s)
    : ValueGroup s :=
  let empty := board.isEmptyPoint p
  let (points, liberties) := floodFill board [p] [] [] empty
  -- maybe add check for ValueGroup here
  ⟨board.getColorAt? p, points.toArray, liberties.toArray⟩

/-- Get the StoneGroup at point `p` on `board` if `p` is not empty -/
def Board.getStoneGroupAt? {s} (board : Board s) (p : Point s)
    : Option <| StoneGroup s :=
  match board.getColorAt? p with
  | none => none
  | some _ => board.getValueGroupAt p |>.getStoneGroup?

/-- Get the StoneGroup from stone `st` on `board` -/
def Board.getStoneGroupFrom {s} (board : Board s) (st : Stone s)
    : StoneGroup s :=
  let (points, liberties) := floodFill board [st.point] [] [] false
  ⟨st.color, points.toArray, liberties.toArray⟩

def Board.getStoneGroupsFrom {s} (board : Board s) (starr : StonesArr s)
    : StoneGroupsArr s :=
  starr.map fun st => board.getStoneGroupFrom st

/-- Set point `p` to `col?` on `board` -/
def Board.setAt {s} (board : Board s) (p : Point s) (col? : Option Color)
    : Board s :=
  let row := board[p.r]'(p.r_lt_n)
  let modified_row := row.set p.c col? (p.c_lt_n)
  let modified_board := board.set p.r modified_row p.r_lt_n
  modified_board

/-- Set point `p` to color `col` on `board` -/
def Board.placeForceAt {s} (board : Board s) (p : Point s) (col : Color)
    : Board s :=
  board.setAt p (some col)

/-- Set all points in `parr` to `col?` on `board` -/
def Board.setManyAt {s} (board : Board s) (parr : PointsArr s) (col? : Option Color)
    : Board s :=
  parr.foldl (fun b p => b.setAt p col?) board

def Board.setValueGroupTo {s} (board : Board s) (vg : ValueGroup s) (col? : Option Color)
    : Board s :=
  board.setManyAt vg.points col?

def Board.captureStoneGroup {s} (board : Board s) (stg : StoneGroup s)
    : Board s :=
  board.setManyAt stg.points none

def Board.captureStoneGroups {s} (board : Board s) (stgarr : StoneGroupsArr s)
    : Board s :=
  stgarr.foldl (fun b stg => b.captureStoneGroup stg) board

/-- Check if playing at `p` is ko -/
def GameState.isKo {s} (gs : GameState s) (p : Point s)
    : Bool :=
  let new_board := gs.board.placeForceAt p (gs.toMove)
  if new_board == gs.prev_board? then
    true
  else
    false

/-- Check if StoneGroup `stg` has zero libs -/
def StoneGroup.hasZeroLibs {s} (stg : StoneGroup s)
    : Bool :=
  if stg.getNumLibs != 0 then
    false
  else
    true

def StoneGroupsArr.filterZeroLibs {s} (stgarr : StoneGroupsArr s)
    : StoneGroupsArr s :=
  stgarr.filter fun stg => stg.hasZeroLibs

#check Array.all

/-- Return the StoneGroups that get captured on playing `toMove` at `p`.
    Ensure you give the new board with `p` set at `toMove` already. -/
def Board.getNbhdGroupCapturesAt {s} (board : Board s) (p : Point s) (toMove : Color)
    : StoneGroupsArr s :=
  let nbhdStones := board.getNbhdStonesAt p
  let oppNbhdStones := nbhdStones.filterColor (oppColor toMove)
  let oppNbhdStoneGroups := board.getStoneGroupsFrom oppNbhdStones
  let oppNbhdZeroLibsStoneGroups := oppNbhdStoneGroups.filterZeroLibs
  oppNbhdZeroLibsStoneGroups.deldups

def Board.hasZeroLibsFrom {s} (board : Board s) (st : Stone s)
    : Bool :=
  let stg := board.getStoneGroupFrom st
  stg.hasZeroLibs

def Board.playCaptures {s} (board : Board s) (p : Point s) (toMove : Color)
    : Except String <| Board s × Nat :=
  let new_board := board.placeForceAt p toMove
  let oppNbhdZeroLibsStoneGroups := new_board.getNbhdGroupCapturesAt p toMove
  if oppNbhdZeroLibsStoneGroups.isEmpty then
    if new_board.hasZeroLibsFrom ⟨toMove, p⟩ then
      Except.error "Illegal: Self-Capture!"
    else
      Except.ok (new_board, 0)
  else
    Except.ok <|
      (new_board.captureStoneGroups oppNbhdZeroLibsStoneGroups,
        oppNbhdZeroLibsStoneGroups.totalSize)

def GameState.updateCaptures {s} (gs : GameState s) (captures : Nat)
    : GameState s :=
  match gs.toMove with
  | .B => {gs with capturedW := captures + gs.capturedW}
  | .W => {gs with capturedB := captures + gs.capturedB}

def GameState.moveP {s} (gs : GameState s) (p : Point s)
    : GameState s :=
  match gs.board.isEmptyPoint p with
  | false => {gs with msg := "Error: Point not empty!"}
  | true =>
    match gs.isKo p with
    | true => {gs with msg := "Illegal: Ko!"}
    | false =>
    match gs.board.playCaptures p gs.toMove with
    | Except.error msg => {gs with msg := msg}
    | Except.ok (new_board, captures) =>
      let new_gs := {gs with board       := new_board,
                             toMove      := nextTurn gs.toMove,
                             prev_board? := some gs.board,
                             msg         := defaultMsg,
                             moveNum     := gs.moveNum + 1}
      new_gs.updateCaptures captures

def GameState.moveN {s} (gs : GameState s) (r c : Nat)
    : GameState s :=
  if h1 : r < s.rl then
    if h2 : c < s.cl then
      let p := Point.mk r c h1 h2
      gs.moveP p
    else
      {gs with msg := "Error: Move outside board!"}
  else
    {gs with msg := "Error: Move outside board!"}

def ltrToNum (ch : Char) : Except String Nat :=
  let num := ch.toNat
  if 97 <= num && num <= 122 then
    .ok <| num - 97
  else
    if 65 <= num && num <= 90 then
      .ok <| num - 65
    else
      .error "Error: Invalid Notation!"

def GameState.moveC {s} (gs : GameState s) (r_ch c_ch : Char)
    : GameState s :=
  match ltrToNum r_ch with
  | .error msg => {gs with msg := msg}
  | .ok r_num  =>
    match ltrToNum c_ch with
    | .error msg => {gs with msg := msg}
    | .ok c_num =>
      gs.moveN r_num c_num

/-- Pass only changes `toMove`; the board remains the same -/
def GameState.pass {s} (gs : GameState s)
    : GameState s :=
  {gs with toMove := nextTurn gs.toMove}

inductive Place (s : Size) where
  | num (r : Nat) (c : Nat)
  | char (r : Char) (c : Char)

inductive Move (s : Size) where
  | pass
  | place (pl : Place s)

structure Turn (s : Size) where
  color : Color
  move : Move s

def GameState.move {s} (gs : GameState s) (move : Move s)
    : GameState s :=
  match move with
  | .pass     => gs.pass
  | .place pl =>
    match pl with
    | .num r c  => gs.moveN r c
    | .char r c => gs.moveC r c

def GameState.playGame {s} (gs : GameState s) (moves : List <| Move s)
    : GameState s :=
  moves.foldl move gs

def printOptColor : Option Color → String
| some .B => "○"
| some .W => "●"
| none =>    "+"

def printRow {n} (vec : Vector (Option Color) n) : String :=
  String.intercalate "" (vec.map printOptColor).toList

def printBoard {s} (board : Board s) : String :=
  String.intercalate "\n" (board.map printRow).toList

instance {s} : Repr <| GameState s where
  reprPrec gs _ :=
    let moveNum := s!"Move Number: {gs.moveNum}\n"
    let toMove := s!"To Move: {printColor gs.toMove}\n"
    let msg := s!"Messages: {gs.msg}\n"
    let captures := s!"Captures: B = {gs.capturedB}, W = {gs.capturedW}\n"
    let brd := printBoard gs.board
    (moveNum ++ toMove ++ msg ++ captures ++ brd).toFormat



def game0 : GameState s[19,19] :=
  let s := s[19,19]
  dfltGameState.moveP p[0,0,s]
  |>.moveP p[1,0,s]
  |>.moveP p[0,1,s]
  |>.moveP p[1,1,s]
  |>.moveP p[3,3,s]
  |>.moveP p[0,2,s]

def game1 : GameState s[19,19] :=
  let s := s[19,19]
  dfltGameState.moveN 0 0
  |>.moveN 1 0
  |>.moveN 0 1
  |>.moveN 1 1
  |>.moveN 3 3
  |>.moveN 0 2

#eval game1

def game2 : GameState s[19,19] :=
  let s := s[19,19]
  dfltGameState.moveP p[0,0,s]
  |>.moveP p[3,4,s]
  |>.moveP p[4,4,s]
  |>.moveP p[0,1,s]
  |>.moveP p[5,5,s]
  |>.moveP p[1,0,s]

def game3 : GameState s[19,19] :=
  let s := s[19,19]
  dfltGameState.moveN 0 0
  |>.moveN 3 4
  |>.moveN 4 4
  |>.moveN 0 1
  |>.moveN 5 5
  |>.moveN 1 0

#eval game3

notation "n[" r "," c "]" => Move.place <| Place.num r c
notation "pass" => Move.pass
notation "c[" r "," c "]" => Move.place <| Place.char r c

open GameState Move Place

def game4 : GameState s[19,19] :=
  startGame.playGame [place <| num 1 1]

#eval game4

def game5 : GameState s[19,19] :=
  startGame.playGame [ n[1,1], n[3,4], c['a','b'] ]

#eval game5
