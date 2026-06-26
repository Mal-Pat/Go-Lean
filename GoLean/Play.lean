import GoLean.FloodFill

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

/--
The Game State - containing the board, current turn,
previous board to check for ko, number of captured stones,
move number, move result, the game result and game details.
-/
structure GameState extends SetUp where
  turn        : Color                := .B
  prev_board? : Option <| Board size := none
  captures    : Captures             := {}
  moveNum     : Nat                  := 0
  moveResult  : MoveResult           := .valid

def GameState.isKo (gs : GameState) (board : Board gs.size)
    : Bool :=
  gs.prev_board? == board

end GameState

section Play

/-- Return the StoneGroups that get captured on playing `turn` at `p`.
    Ensure you give the new board with `p` set at `turn` already. -/
def Board.getNbhdGroupCapturesAt {s} (board : Board s) (p : Point s) (turn : Color)
    : GroupsArr s :=
  let nbhdPlaces := board.getNbhdPlacesAt p
  let oppNbhdPlaces := nbhdPlaces.filterStone <| .col turn.oppColor
  let oppNbhdGroups := board.getStoneGroupsAt oppNbhdPlaces.getPoints
  let oppNbhdZeroLibsGroups := oppNbhdGroups.filterZeroLibs
  oppNbhdZeroLibsGroups.deldups

def Board.playCaptures {s} (board : Board s) (p : Point s) (turn : Color)
    : Except InvalidMoveReason <| Board s × Nat :=
  let new_board := board.setAt p (.col turn)
  let oppNbhdZeroLibsGroups := new_board.getNbhdGroupCapturesAt p turn
  if oppNbhdZeroLibsGroups.isEmpty then
    if (new_board.getGroupAt p).liberties.size == 0 then
      Except.error <| .selfCapture
    else
      Except.ok (new_board, 0)
  else
    Except.ok (new_board.captureStoneGroups oppNbhdZeroLibsGroups,
      oppNbhdZeroLibsGroups.totalSize)

def Captures.updateFor (captures : Captures) (col : Color) (capNum : Nat)
    : Captures :=
  match col with
  | .B => {captures with black := capNum + captures.black}
  | .W => {captures with white := capNum + captures.white}

/-- Play at point `p` in GameState `gs` and return the new GameState -/
def GameState.moveP (gs : GameState) (p : Point gs.size)
    : GameState :=
  /-  The order of steps is important:
      1. Check if `p` is empty
      2. Play captures
      3. Check for ko -/
  match gs.board.isEmptyPoint p with
  | false => {gs with moveResult := .invalid .occupied}
  | true  =>
    match gs.board.playCaptures p gs.turn with
    | Except.error reason => {gs with moveResult := .invalid reason}
    | Except.ok (new_board, capNum) =>
      match gs.isKo new_board with
      | true  => {gs with moveResult := .invalid .ko}
      | false => {gs with
        board       := new_board,
        turn        := gs.turn.oppColor,
        prev_board? := some gs.board,
        captures    := gs.captures.updateFor gs.turn capNum
        moveNum     := gs.moveNum + 1
        moveResult  := .valid }

/-- Pass only changes `turn`; the board remains the same -/
def GameState.pass (gs : GameState)
    : GameState :=
  {gs with turn := gs.turn.oppColor, moveNum := gs.moveNum + 1}

end Play
