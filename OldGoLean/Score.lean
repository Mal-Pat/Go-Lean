import GoLean.Play

section ScoreStone

inductive ScoreStone where
  | undecided
  | alive (c : Color)
  | dead  (c : Color)
  | area  (s : Stone)
  deriving Repr, DecidableEq

end ScoreStone

section ScorePlace

structure ScorePlace (s : Size) where
  scst : ScoreStone
  point : Point s

abbrev ScorePlaceArr (s : Size) := Array <| ScorePlace s
abbrev ScorePlaceList (s : Size) := List <| ScorePlace s

def ScorePlaceArr.getPoints {s} (plarr : ScorePlaceArr s)
    : PointsArr s :=
  plarr.map fun pl => pl.point

/-- Filter places w.r.t a stone -/
def ScorePlaceArr.filterStone {s} (splarr : ScorePlaceArr s) (scst : ScoreStone)
    : ScorePlaceArr s :=
  splarr.filter (fun spl => spl.scst == scst)

end ScorePlace

section ScoreGroup

structure ScoreGroup (s : Size) where
  scst : ScoreStone
  points : PointsArr s
  liberties : PointsArr s
  deriving Repr, DecidableEq

abbrev ScoreGroupsArr (s : Size) := Array <| ScoreGroup s
abbrev ScoreGroupsList (s : Size) := List <| ScoreGroup s

/-- Check if two StoneGroups are equal -/
def ScoreGroup.isEqualTo {s} (sg1 sg2 : ScoreGroup s)
    : Bool :=
  let b1 := sg1.scst == sg2.scst
  let b2 := List.Perm sg1.points.toList sg2.points.toList
  b1 && b2

/-- Check if a list of StoneGroups contains a particular Group -/
def ScoreGroupsList.contains {s} (sgl : ScoreGroupsList s) (target_sg : ScoreGroup s)
    : Bool :=
  match sgl with
  | [] => false
  | sg :: rest =>
    match target_sg.isEqualTo sg with
    | true => true
    | false => rest.contains target_sg

/-- Delete duplicate StoneGroups from Array of StoneGroups -/
def ScoreGroupsArr.deldups {s} (sgarr : ScoreGroupsArr s)
    : ScoreGroupsArr s :=
  let sgl := sgarr.toList
  let unqsgl := sgl.foldl (fun unql sg =>
    if unql.contains sg then unql else sg :: unql) []
  unqsgl.toArray

def ScoreGroupsArr.filterZeroLibs {s} (sgarr : ScoreGroupsArr s)
    : ScoreGroupsArr s :=
  sgarr.filter fun sg => sg.liberties.size == 0

def ScoreGroupsArr.totalSize {s} (sgarr : ScoreGroupsArr s)
    : Nat :=
  sgarr.foldl (fun n sg => n + sg.points.size) 0

end ScoreGroup

section ScoreBoard

/-- `ScoreBoard` -/
abbrev ScoreBoard (s : Size) := Vector (Vector (ScoreStone) s.cl) s.rl

/-- Create an empty score board (filled with `.area .empty`)
    (size will be inferred from context) -/
def emptyScoreBoard {s : Size} : ScoreBoard s :=
  let row : Vector ScoreStone s.cl :=
    ⟨Array.replicate s.cl (.area .empty), by simp⟩
  ⟨Array.replicate s.rl row, by simp⟩

/-- Get score stone at a point on score board -/
def ScoreBoard.getScoreStoneAt {s} (sboard : ScoreBoard s) (p : Point s)
    : ScoreStone :=
  sboard[p.r][p.c]

/-- Set point `p` to `scst` on `sboard` -/
def ScoreBoard.setAt {s} (sboard : ScoreBoard s) (p : Point s) (scst : ScoreStone)
    : ScoreBoard s :=
  let row := sboard[p.r]
  let modified_row := row.set p.c scst
  let modified_board := sboard.set p.r modified_row
  modified_board

/-- Set all points in `parr` to `col?` on `board` -/
def ScoreBoard.setManyAt {s} (sboard : ScoreBoard s) (parr : PointsArr s) (scst : ScoreStone)
    : ScoreBoard s :=
  parr.foldl (fun b p => b.setAt p scst) sboard

end ScoreBoard

section FloodFill

/-- Get the StoneGroup at point `p` on `board` -/
def ScoreBoard.getScoreGroupAt {s} (sboard : ScoreBoard s) (p : Point s)
    : ScoreGroup s :=
  let empty := board.isEmptyPoint p
  let (points, liberties) := floodFill board p empty
  -- maybe add check for StoneGroup here
  ⟨board.getStoneAt p, points.toArray, liberties.toArray⟩

/-- Get all StoneGroups from array of points -/
def ScoreBoard.getScoreGroupsAt {s} (board : Board s) (parr : PointsArr s)
    : GroupsArr s :=
  parr.map fun point => board.getGroupAt point

end FloodFill

section ScoreState

structure Score where
  white : Float
  black : Float

structure ScoreState extends GameState where
  sboard : ScoreBoard size
  score  : Score

end ScoreState
