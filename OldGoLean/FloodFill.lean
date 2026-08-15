import GoLean.Basic

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
