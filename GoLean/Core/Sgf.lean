/-
Authors: Malhar A. Patel
-/

import GoLean.Core.Game

/-!
# SGF export

Convert a `Game` into an SGF (Smart Game Format, FF[4]) string:
`Game.toSgf`. Because a `Game` is event-sourced, the export is a
straightforward walk of the action log: fixed-handicap stones become `AB`
setup properties, stone placements and passes become `;B[..]`/`;W[..]`
move nodes (free-handicap placements appear as consecutive Black moves,
which FF[4] permits), and a finished game gets an `RE` result.

Scoring actions (`toggleDead`/`accept`/`resume`) and `resign` produce no
move nodes — resignation is reflected in `RE` instead.
-/

namespace GoLean

/-- SGF coordinate letter: `0`–`25` → `a`–`z`, `26`–`51` → `A`–`Z`
(SGF supports boards up to 52×52). -/
def sgfLetter (n : Nat) : Char :=
  if n < 26 then Char.ofNat ('a'.toNat + n)
  else if n < 52 then Char.ofNat ('A'.toNat + (n - 26))
  else '?'

/-- SGF point: column letter first, then row letter (`aa` = top left). -/
def sgfCoord (r c : Nat) : String :=
  String.ofList [sgfLetter c, sgfLetter r]

/-- Escape an SGF text property value (`]` and `\` need a backslash). -/
def sgfEscape (str : String) : String :=
  str.foldl (init := "") fun acc ch =>
    if ch == ']' || ch == '\\' then (acc.push '\\').push ch else acc.push ch

/-- The SGF `RU` (rules) value: a standard name when the toggles match a
preset (komi aside), otherwise a parseable `Custom …` description so that
export/import round trips preserve every toggle. -/
def Ruleset.sgfName (rs : Ruleset) : String :=
  let same (a b : Ruleset) : Bool :=
    a.ko == b.ko && a.scoring == b.scoring
      && a.selfCaptureAllowed == b.selfCaptureAllowed
      && a.passesToScore == b.passesToScore
  if same rs .japanese then "Japanese"
  else if same rs .chinese then "Chinese"
  else if same rs .trompTaylor then "Tromp-Taylor"
  else if same rs .aga then "AGA"
  else
    s!"Custom ko={rs.ko.wireName} scoring={rs.scoring.wireName} " ++
    s!"selfcapture={if rs.selfCaptureAllowed then "yes" else "no"} " ++
    s!"passes={rs.passesToScore}"

private def sgfProp (key val : String) : String := s!"{key}[{val}]"

/-- Join move nodes with a line break every `chunk` nodes, for readability. -/
private def joinChunked (chunk : Nat) (nodes : Array String) : String :=
  nodes.toList.zipIdx.foldl (init := "") fun acc (node, i) =>
    acc ++ (if i % chunk == 0 then "\n" else "") ++ node

/-- Serialize the game to SGF (FF[4]). Works in every phase: an unfinished
game simply has no `RE` property. -/
def Game.toSgf (g : Game) : String :=
  let cfg := g.config
  let s := cfg.size
  -- SGF's SZ is `columns:rows` for non-square boards.
  let szVal := if s.rows == s.cols then toString s.cols else s!"{s.cols}:{s.rows}"
  let reProp :=
    match g.phase with
    | .finished _ r => sgfProp "RE" (if r.format == "Draw" then "0" else r.format)
    | _ => ""
  let haProp := if cfg.handicap ≥ 2 then sgfProp "HA" (toString cfg.handicap) else ""
  -- A forced first mover (SGF imports) is recorded as PL.
  let plProp :=
    match cfg.firstToMove with
    | some .black => sgfProp "PL" "B"
    | some .white => sgfProp "PL" "W"
    | none => ""
  -- Stones already on the initial board (handicap or explicit setup) → AB/AW.
  let setupProps :=
    match cfg.initialPlayState with
    | .error _ => ""  -- unreachable: `g` was built from this config
    | .ok ps0 =>
      let mk (col : Color) (id : String) : String :=
        let pts := s.points.toList.filter fun p => ps0.board.get p == some col
        if pts.isEmpty then ""
        else id ++ String.join (pts.map fun p => s!"[{sgfCoord p.r.val p.c.val}]")
      mk .black "AB" ++ mk .white "AW"
  -- Replay the log; each `play`/`pass` becomes a move node colored by
  -- whoever was to move at that point.
  let moveNodes :=
    match Game.new cfg with
    | .error _ => ""  -- unreachable: `g` was built from this config
    | .ok g0 =>
      let (nodes, _) := g.actions.foldl (init := ((#[] : Array String), g0))
        fun (nodes, cur) a =>
          let colLetter := if cur.curPlayState.toMove == Color.black then "B" else "W"
          let nodes :=
            match a with
            | .play r c => nodes.push s!";{colLetter}[{sgfCoord r c}]"
            | .pass => nodes.push s!";{colLetter}[]"
            | _ => nodes
          match cur.step a with
          | .ok g' => (nodes, g')
          | .error _ => (nodes, cur)  -- unreachable: logged actions replay
      joinChunked 10 nodes
  "(;" ++ sgfProp "GM" "1" ++ sgfProp "FF" "4" ++ sgfProp "CA" "UTF-8"
    ++ sgfProp "AP" "GoLean"
    ++ sgfProp "SZ" szVal
    ++ sgfProp "KM" (formatHalfInt cfg.komi2)
    ++ sgfProp "RU" cfg.ruleset.sgfName
    ++ sgfProp "PB" (sgfEscape cfg.blackName)
    ++ sgfProp "PW" (sgfEscape cfg.whiteName)
    ++ haProp ++ plProp ++ reProp ++ setupProps
    ++ moveNodes
    ++ ")"

end GoLean
