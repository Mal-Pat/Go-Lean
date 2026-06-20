/-
Authors : Malhar A. Patel
-/

section Color

/-- `Color` Type -/
inductive Color
  | B
  | W
  deriving DecidableEq, Repr, Inhabited

instance : ToString Color where
  toString
  | .B => "Black"
  | .W => "White"

/-- Opposite Color -/
def Color.oppColor : Color → Color
  | .B => .W
  | .W => .B

end Color

section Size

/-- Size of board -/
structure Size where
  rl : Nat
  cl : Nat
  two_le_rl : 2 ≤ rl := by decide
  two_le_cl : 2 ≤ cl := by decide

/-- Notation for `Size` -/
notation "s[" rl "," cl "]" => Size.mk rl cl

instance : Inhabited Size where
  default := s[19,19]

end Size

section Point

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

abbrev PointsArr (s : Size) := Array <| Point s
abbrev PointsList (s : Size) := List <| Point s

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

end Point

section Stone

inductive Stone where
  | col (c : Color)
  | empty
  deriving Repr, DecidableEq

inductive ScoreStone where
  | alive (c : Color)
  | dead  (c : Color)
  | area  (s : Stone)

end Stone

section Place

structure Place (s : Size) where
  stone : Stone
  point : Point s

abbrev PlaceArr (s : Size) := Array <| Place s
abbrev PlaceList (s : Size) := List <| Place s

def PlaceArr.getPoints {s} (plarr : PlaceArr s)
    : PointsArr s :=
  plarr.map fun pl => pl.point

/-- Filter places w.r.t a stone -/
def PlaceArr.filterStone {s} (plarr : PlaceArr s) (stone : Stone)
    : PlaceArr s :=
  plarr.filter (fun st => st.stone == stone)

end Place

section Group

structure Group (s : Size) where
  stone : Stone
  points : PointsArr s
  liberties : PointsArr s
  deriving Repr, DecidableEq

abbrev GroupsArr (s : Size) := Array <| Group s
abbrev GroupsList (s : Size) := List <| Group s

/-- Check if two StoneGroups are equal -/
def Group.isEqualTo {s} (g1 g2 : Group s)
    : Bool :=
  let b1 := g1.stone == g2.stone
  let b2 := List.Perm g1.points.toList g2.points.toList
  b1 && b2

/-- Check if a list of StoneGroups contains a particular Group -/
def GroupsList.contains {s} (gl : GroupsList s) (target_g : Group s)
    : Bool :=
  match gl with
  | [] => false
  | g :: rest =>
    match target_g.isEqualTo g with
    | true => true
    | false => rest.contains target_g

/-- Delete duplicate StoneGroups from Array of StoneGroups -/
def GroupsArr.deldups {s} (garr : GroupsArr s)
    : GroupsArr s :=
  let gl := garr.toList
  let unqstgl := gl.foldl (fun unql g =>
    if unql.contains g then unql else g :: unql) []
  unqstgl.toArray

def GroupsArr.filterZeroLibs {s} (garr : GroupsArr s)
    : GroupsArr s :=
  garr.filter fun g => g.liberties.size == 0

def GroupsArr.totalSize {s} (garr : GroupsArr s)
    : Nat :=
  garr.foldl (fun n g => n + g.points.size) 0

end Group

section Board

/-- `Board` -/
abbrev Board (s : Size) := Vector (Vector (Stone) s.cl) s.rl

/-- Create an empty board (filled with `Stone.empty`)
    (size will be inferred from context) -/
def emptyBoard {s : Size} : Board s :=
  let row : Vector Stone s.cl :=
    ⟨Array.replicate s.cl .empty, by simp⟩
  ⟨Array.replicate s.rl row, by simp⟩

/-- Get stone at a point on board -/
def Board.getStoneAt {s} (board : Board s) (p : Point s)
    : Stone :=
  board[p.r][p.c]

/-- Check if a point on board is empty -/
def Board.isEmptyPoint {s} (board : Board s) (p : Point s)
    : Bool :=
  match board.getStoneAt p with
  | .empty => true
  | .col _ => false

/-- Get the Option Color at a point on the board-/
def Board.getColorAt? {s} (board : Board s) (p : Point s)
    : Option Color :=
  match board.getStoneAt p with
  | .empty => none
  | .col c => c

/-- Set point `p` to `col?` on `board` -/
def Board.setAt {s} (board : Board s) (p : Point s) (stone : Stone)
    : Board s :=
  let row := board[p.r]
  let modified_row := row.set p.c stone
  let modified_board := board.set p.r modified_row
  modified_board

/-- Set all points in `parr` to `col?` on `board` -/
def Board.setManyAt {s} (board : Board s) (parr : PointsArr s) (stone : Stone)
    : Board s :=
  parr.foldl (fun b p => b.setAt p stone) board

def Board.captureStoneGroup {s} (board : Board s) (stg : Group s)
    : Board s :=
  board.setManyAt stg.points .empty

def Board.captureStoneGroups {s} (board : Board s) (stgarr : GroupsArr s)
    : Board s :=
  stgarr.foldl (fun b stg => b.captureStoneGroup stg) board

/-- Get values at points on board -/
def Board.getPlacesAt {s} (board : Board s) (parr : PointsArr s)
    : PlaceArr s :=
  parr.map fun p => ⟨board.getStoneAt p, p⟩

/-- Get the neighboring values of a point on board -/
def Board.getNbhdPlacesAt {s} (board : Board s) (p : Point s)
    : PlaceArr s :=
  let nbhdpoints := p.getNbhdPoints
  board.getPlacesAt nbhdpoints

end Board

section GameState

structure Captures where
  white : Nat := 0
  black : Nat := 0

inductive InvalidMoveReason where
  | outOfBoard
  | occupied
  | selfCapture
  | ko
  | invalidNotation

inductive MoveResult where
  | valid
  | invalid (reason : InvalidMoveReason)

structure GameDetails where
  player1  : String := "Player 1"
  player2  : String := "Player 2"
  handicap : Nat    := 0
  komi     : Float  := 6.5

inductive SetDetailsResult where
  | valid
  | invalid

structure Score where
  white : Nat
  Black : Nat

inductive GameStatus where
  | ongoing
  | score (s : Score)
  | finish (s : Score)

/--
The Game State - containing the board, current turn,
previous board to check for ko, number of captured stones,
move number, move result, the game result and game details.
-/
structure GameState (s : Size) where
  board       : Board s           := emptyBoard
  turn        : Color             := .B
  prev_board? : Option <| Board s := none
  captures    : Captures          := {}
  moveNum     : Nat               := 0
  moveResult  : MoveResult        := .valid
  gameStatus  : GameStatus        := .ongoing
  gameDetails : GameDetails       := {}
  setDetails  : SetDetailsResult  := .valid

def GameState.isKo {s} (gs : GameState s) (board : Board s)
    : Bool :=
  gs.prev_board? == board

end GameState
