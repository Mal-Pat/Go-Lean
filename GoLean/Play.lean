import GoLean.FloodFill

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
def GameState.moveP {s} (gs : GameState s) (p : Point s)
    : GameState s :=
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
