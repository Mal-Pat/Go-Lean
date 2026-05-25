/-
Authors : Malhar A. Patel
-/

import Lean

/-- `Color` Type -/
inductive Color
  | B
  | W
  deriving DecidableEq, Repr, Inhabited

/-- Prints `Color`'s color -/
def printColor : Color → String
  | .B => "Black"
  | .W => "White"

/-- Next Turn -/
def nextTurn : Color → Color
  | .B => .W
  | .W => .B

/-- Opposite color -/
abbrev oppColor := nextTurn

/-- Size of board -/
structure Size where
  rl : Nat
  cl : Nat
  two_le_rl : 2 ≤ rl := by decide
  two_le_cl : 2 ≤ cl := by decide

/-- Notation for `Size` -/
notation "s[" rl "," cl "]" => Size.mk rl cl

/-- `Board` -/
abbrev Board (s : Size) := Vector (Vector (Option Color) s.cl) s.rl

def defaultSize : Size := s[19,19]

/--
The Game State, containing the board, next color to move,
previous board to check for ko, number of captured pieces,
the move number and any messages for the players.
-/
structure GameState (s : Size) where
  board : Board s
  turn : Color
  prev_board? : Option <| Board s
  capturedW : Nat
  capturedB : Nat
  moveNum : Nat
  msg : String

/--
`Point` specifies a point by row and column, and
the proof that both are less than `s.rl` and `s.cl` respectively
-/
structure Point (s : Size) where
  r : Fin s.rl
  c : Fin s.cl
  deriving DecidableEq, Repr

/-- Notation for `Point` -/
notation "p[" a "," b "," s "]" => @Point.mk s a b (by decide) (by decide)

/-- `Value` contains a `Point` and an `Option Color` -/
structure Value (s : Size) where
  color? : Option Color
  point : Point s

/-- `Stone` contains a `Point` and a `Color` -/
structure Stone (s : Size) where
  color : Color
  point : Point s

/-- Get the value of a stone -/
def Stone.getValue {s} (st : Stone s)
    : Value s :=
  ⟨some st.color, st.point⟩

/-- Get (opt) stone from a value -/
def Value.getStone? {s} (v : Value s)
    : Option <| Stone s :=
  match v.color? with
  | none => none
  | some color => some ⟨color, v.point⟩

/-- Create an empty board (filled with `none`)
    (size will be inferred from context) -/
def emptyBoard {s : Size} : Board s :=
  let row : Vector (Option Color) s.cl :=
    ⟨Array.replicate s.cl none, by simp⟩
  ⟨Array.replicate s.rl row, by simp⟩

/-- Default Message to display -/
def defaultMsg : String := "Valid Move"

/-- Inhabited GameState -/
instance {s} : Inhabited (GameState s) where
  default := {
    board := emptyBoard,
    turn := Color.B,
    prev_board? := none,
    capturedW := 0,
    capturedB := 0,
    moveNum := 0,
    msg := defaultMsg
    }

/-- Create a `GameState` with an empty board and black to start
    (size will be inferred from context) -/
def startGame {s : Size} : GameState s :=
  default

abbrev PointsArr (s : Size) := Array <| Point s
abbrev PointsList (s : Size) := List <| Point s
abbrev ValuesArr (s : Size) := Array <| Value s
abbrev StonesArr (s : Size) := Array <| Stone s

/-- Get some color or none at a point on board -/
def Board.getColorAt? {s} (board : Board s) (p : Point s)
    : Option Color :=
  board[p.r][p.c]

/-- Check if a point on board is empty -/
def Board.isEmptyPoint {s} (board : Board s) (p : Point s)
    : Bool :=
  match board.getColorAt? p with
  | none => true
  | some _ => false

/-- Get value at a point on board -/
def Board.getValueAt {s} (board : Board s) (p : Point s)
    : Value s :=
  ⟨board.getColorAt? p, p⟩

/-- Get (opt) stone at a point on board -/
def Board.getStoneAt? {s} (board : Board s) (p : Point s)
    : Option <| Stone s :=
  match board.getColorAt? p with
  | none => none
  | some color => some ⟨color, p⟩

/-- Get values at points on board -/
def Board.getValuesAt {s} (board : Board s) (parr : PointsArr s)
    : ValuesArr s :=
  parr.map fun p => board.getValueAt p

/-- Get (opt) stones at points on board -/
def Board.getStonesAt? {s} (board : Board s) (parr : PointsArr s)
    : Option <| StonesArr s :=
  parr.mapM fun p => board.getStoneAt? p -- Ensure that this works correctly

/-- Get points from stones -/
def StonesArr.getPointsFrom {s} (starr : StonesArr s) -- Ensure that `StonesArr.` works
    : PointsArr s :=
  starr.map fun st => st.point

/-- Get points from values -/
def ValuesArr.getPointsFrom {s} (varr : ValuesArr s)
    : PointsArr s :=
  varr.map fun v => v.point

/-- Convert array of values to array of stones -/
def ValuesArr.toStoneArr {s} (varr : ValuesArr s)
    : StonesArr s :=
  varr.filterMap Value.getStone?

/-- Filter an array of stones w.r.t a color -/
def StonesArr.filterColor {s} (starr : StonesArr s) (color : Color)
    : StonesArr s :=
  starr.filter (fun st => st.color == color)

/-- Check if all points have same (opt) color -/
def Board.checkSame {s} (board : Board s) (color? : Option Color) (points : PointsList s)
    : Bool :=
  match points with
  | [] => true
  | p :: rest =>
    if board.getColorAt? p == color? then
      board.checkSame color? rest
    else
      false

/-- A group of points with same (opt) color -/
structure ValueGroup (s : Size) where
  color? : Option Color
  points : PointsArr s
  liberties : PointsArr s
  deriving Repr, DecidableEq

/-- Check if a ValueGroup is valid on board,
    that is, every point in the ValueGroup must have same (opt) color -/
def ValueGroup.check {s} (vg : ValueGroup s) (board : Board s)
    : Bool :=
  board.checkSame vg.color? vg.points.toList

/-- Get number of liberties of a ValueGroup -/
def ValueGroup.getNumLibs {s} (vg : ValueGroup s)
    : Nat :=
  vg.liberties.size

/-- A group of stones with same color -/
structure StoneGroup (s : Size) where
  color : Color
  points : PointsArr s
  liberties : PointsArr s
  deriving Repr, DecidableEq

/-- Check if two StoneGroups are equal -/
def StoneGroup.isEqualTo {s} (stg1 stg2 : StoneGroup s)
    : Bool :=
  let b1 := stg1.color == stg2.color
  let b2 := List.Perm stg1.points.toList stg2.points.toList
  b1 && b2

abbrev StoneGroupsArr (s : Size) := Array <| StoneGroup s
abbrev StoneGroupsList (s : Size) := List <| StoneGroup s

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

/-- Check if a StoneGroup is valid -/
def StoneGroup.check {s} (stg : StoneGroup s) (board : Board s)
    : Bool :=
  board.checkSame stg.color stg.points.toList

/-- Get number of liberties of a StoneGroup -/
def StoneGroup.getNumLibs {s} (stg : StoneGroup s)
    : Nat :=
  stg.liberties.size

/-- Get size of a StoneGroup (number of stones in it) -/
def StoneGroup.size {s} (stg : StoneGroup s)
    : Nat :=
  stg.points.size

/-- Get number of stones in total among an array of StoneGroups -/
def StoneGroupsArr.totalSize {s} (stgarr : StoneGroupsArr s)
    : Nat :=
  stgarr.foldl (fun n stg => n + stg.size) 0

/-- Convert a ValueGroup to a StoneGroup if possible -/
def ValueGroup.getStoneGroup? {s} (vg : ValueGroup s)
    : Option <| StoneGroup s :=
  match vg.color? with
  | none => none
  | some color => some ⟨color, vg.points, vg.liberties⟩

/-- Convert a StoneGroup to a ValueGroup -/
def StoneGroup.getValueGroup {s} (stg : StoneGroup s)
    : ValueGroup s :=
  ⟨some stg.color, stg.points, stg.liberties⟩

/-- Get the neighboring points of a point -/
def Point.getNbhdPoints {s} (p : Point s)
    : PointsArr s :=
  #[up, down, left, right].filterMap id
  where
    up :=
      if p.r == ⟨0, by grind[s.two_le_rl]⟩ then none
      else some ⟨⟨p.r - 1, by grind⟩, p.c⟩
    down :=
      if row_eq_n : p.r == s.rl - 1 then none
      else some ⟨⟨p.r + 1, by grind⟩, p.c⟩
    left :=
      if p.c == ⟨0, by grind[s.two_le_cl]⟩ then none
      else some ⟨p.r, ⟨p.c - 1, by grind⟩⟩
    right :=
      if row_eq_n : p.c == s.cl - 1 then none
      else some ⟨p.r, ⟨p.c + 1, by grind⟩⟩

/-- Get the neighboring values of a point on board -/
def Board.getNbhdValuesAt {s} (board : Board s) (p : Point s)
    : ValuesArr s :=
  let nbhdpoints := p.getNbhdPoints
  board.getValuesAt nbhdpoints

/-- Get the neighboring stones of a point on board -/
def Board.getNbhdStonesAt {s} (board : Board s) (p : Point s)
    : StonesArr s :=
  let nbhdValues := board.getNbhdValuesAt p
  nbhdValues.toStoneArr

/-- Delete duplicates in a list -/
def deldups {α} [DecidableEq α] (l : List α) : List α :=
  l.foldl (fun unql a => if a ∈ unql then unql else a :: unql) []

/-- Helper for floodfill algorithm -/
def floodFillHelper {s} (board : Board s) (queue : PointsList s)
  (visited : PointsList s) (liberties : PointsList s) (empty : Bool)
  (fuel : Nat)
    : (PointsList s) × (PointsList s) :=
  match fuel with
  | 0 => (visited, deldups liberties)
  | f + 1 => match queue with
    | [] => (visited, deldups liberties)
    | cur :: rest =>
      if cur ∈ visited then
        floodFillHelper board rest visited liberties empty f
      else
        let (same, diff) := cur.getNbhdPoints.partition
          fun p => (board.getColorAt? cur == board.getColorAt? p)
        let libs :=
          if empty then diff
          else diff.filter fun p => (board.getColorAt? p == none)
        floodFillHelper board (rest ++ same.toList) (cur :: visited) (liberties ++ libs.toList) empty f

/-- The floodfill algorithm -/
def floodFill {s} (board : Board s) (point : Point s) (empty : Bool)
    : (PointsList s) × (PointsList s) :=
  let fuel := (s.rl * s.cl) + 1
  floodFillHelper board [point] [] [] empty fuel

/-- Get the ValueGroup at point `p` on `board` -/
def Board.getValueGroupAt {s} (board : Board s) (p : Point s)
    : ValueGroup s :=
  let empty := board.isEmptyPoint p
  let (points, liberties) := floodFill board p empty
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
  let (points, liberties) := floodFill board st.point false
  ⟨st.color, points.toArray, liberties.toArray⟩

def Board.getStoneGroupsFrom {s} (board : Board s) (starr : StonesArr s)
    : StoneGroupsArr s :=
  starr.map fun st => board.getStoneGroupFrom st

/-- Set point `p` to `col?` on `board` -/
def Board.setAt {s} (board : Board s) (p : Point s) (col? : Option Color)
    : Board s :=
  let row := board[p.r]
  let modified_row := row.set p.c col?
  let modified_board := board.set p.r modified_row
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
  let new_board := gs.board.placeForceAt p (gs.turn)
  new_board == gs.prev_board?

/-- Check if StoneGroup `stg` has zero libs -/
def StoneGroup.hasZeroLibs {s} (stg : StoneGroup s)
    : Bool :=
  stg.getNumLibs == 0

def StoneGroupsArr.filterZeroLibsGroups {s} (stgarr : StoneGroupsArr s)
    : StoneGroupsArr s :=
  stgarr.filter fun stg => stg.hasZeroLibs

/-- Return the StoneGroups that get captured on playing `turn` at `p`.
    Ensure you give the new board with `p` set at `turn` already. -/
def Board.getNbhdGroupCapturesAt {s} (board : Board s) (p : Point s) (turn : Color)
    : StoneGroupsArr s :=
  let nbhdStones := board.getNbhdStonesAt p
  let oppNbhdStones := nbhdStones.filterColor (oppColor turn)
  let oppNbhdStoneGroups := board.getStoneGroupsFrom oppNbhdStones
  let oppNbhdZeroLibsStoneGroups := oppNbhdStoneGroups.filterZeroLibsGroups
  oppNbhdZeroLibsStoneGroups.deldups

def Board.hasZeroLibsFrom {s} (board : Board s) (st : Stone s)
    : Bool :=
  let stg := board.getStoneGroupFrom st
  stg.hasZeroLibs

def Board.playCaptures {s} (board : Board s) (p : Point s) (turn : Color)
    : Except String <| Board s × Nat :=
  let new_board := board.placeForceAt p turn
  let oppNbhdZeroLibsStoneGroups := new_board.getNbhdGroupCapturesAt p turn
  if oppNbhdZeroLibsStoneGroups.isEmpty then
    if new_board.hasZeroLibsFrom ⟨turn, p⟩ then
      Except.error "Illegal: Self-Capture!"
    else
      Except.ok (new_board, 0)
  else
    Except.ok (new_board.captureStoneGroups oppNbhdZeroLibsStoneGroups,
      oppNbhdZeroLibsStoneGroups.totalSize)

def GameState.updateCaptures {s} (gs : GameState s) (captures : Nat)
    : GameState s :=
  match gs.turn with
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
    match gs.board.playCaptures p gs.turn with
    | Except.error msg => {gs with msg := msg}
    | Except.ok (new_board, captures) =>
      let new_gs :=
        {gs with board       := new_board,
                 turn      := nextTurn gs.turn,
                 prev_board? := some gs.board,
                 msg         := defaultMsg,
                 moveNum     := gs.moveNum + 1}
      new_gs.updateCaptures captures

def GameState.moveN {s} (gs : GameState s) (r c : Nat)
    : GameState s :=
  if h : r < s.rl ∧ c < s.cl then
      let p := Point.mk ⟨r,h.1⟩ ⟨c,h.2⟩
      gs.moveP p
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

/-- Pass only changes `turn`; the board remains the same -/
def GameState.pass {s} (gs : GameState s)
    : GameState s :=
  {gs with turn := nextTurn gs.turn}

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

def printGameState {s} (gs : GameState s) : String :=
  let moveNum := s!"Move Number: {gs.moveNum}\n"
  let turn := s!"To Move: {printColor gs.turn}\n"
  let msg := s!"Messages: {gs.msg}\n"
  let captures := s!"Captures: B = {gs.capturedB}, W = {gs.capturedW}\n"
  let brd := printBoard gs.board
  moveNum ++ turn ++ msg ++ captures ++ brd

instance {s} : ToString <| GameState s where
  toString gs := printGameState gs

instance {s} : Repr <| GameState s where
  reprPrec gs _ := printGameState gs

notation "n[" r "," c "]" => Move.place <| Place.num r c
notation "pass" => Move.pass
notation "c[" r "," c "]" => Move.place <| Place.char r c
