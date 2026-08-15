/-
Authors: Malhar A. Patel
-/

import GoLean.Core.Sgf
import Tests.Core

/-!
# SGF export tests

Exact-string checks of `Game.toSgf` across: plain games, finished games
(`RE`), resignation, draws, fixed handicap (`HA` + `AB`), free handicap
(consecutive Black moves), non-square boards (`SZ[cols:rows]`), passes,
coordinates, escaping, and the `RU` preset naming.
-/

namespace GoLean.Tests.Sgf

open GoLean GoLean.Tests

def sgfOf (eg : Except IllegalAction Game) : String :=
  match eg with
  | .ok g => g.toSgf
  | .error _ => "ERROR"

/-! ## Units: coordinates, escaping, rules names -/

#guard sgfCoord 0 0 == "aa"
-- The classic upper-right star point (3,15) on 19×19 is `pd`.
#guard sgfCoord 3 15 == "pd"
#guard sgfCoord 18 18 == "ss"
#guard sgfCoord 30 27 == "BE"  -- big-board uppercase range

#guard sgfEscape "we]ird\\na]me" == "we\\]ird\\\\na\\]me"
#guard sgfEscape "plain" == "plain"

#guard Ruleset.japanese.sgfName == "Japanese"
#guard Ruleset.chinese.sgfName == "Chinese"
#guard Ruleset.trompTaylor.sgfName == "Tromp-Taylor"
#guard Ruleset.aga.sgfName == "AGA"
#guard (Ruleset.sgfName { ko := .none }) == "Custom"
-- Komi alone must not make a preset "Custom" (it is stored separately).
#guard (Ruleset.sgfName { defaultKomi2 := 99 }) == "Japanese"

/-! ## Whole games -/

def header5 : String :=
  "(;GM[1]FF[4]CA[UTF-8]AP[GoLean]SZ[5]KM[6.5]RU[Japanese]PB[Black]PW[White]"

-- Moves and passes, correct colors and coordinates.
#guard sgfOf (run cfg5 [.play 2 2, .play 1 1, .pass, .pass])
  == header5 ++ "\n;B[cc];W[bb];B[];W[])"

-- A finished game gets an RE property (scoring actions emit no nodes).
#guard sgfOf tScore == header5 ++ "RE[B+17.5]\n;B[cc];W[];B[])"

-- Resignation: RE only, no move node for the resign itself.
#guard sgfOf (run cfg5 [.play 2 2, .resign]) == header5 ++ "RE[B+R]\n;B[cc])"

-- A draw is RE[0] in SGF.
#guard sgfOf (run cfgDraw [.play 2 2, .pass, .pass, .accept .black, .accept .white])
  == "(;GM[1]FF[4]CA[UTF-8]AP[GoLean]SZ[5]KM[24]RU[Japanese]PB[Black]PW[White]"
      ++ "RE[0]\n;B[cc];W[];B[])"

-- Fixed handicap: HA + AB setup stones, and White moves first.
#guard sgfOf (run cfgH2 [])
  == "(;GM[1]FF[4]CA[UTF-8]AP[GoLean]SZ[9]KM[6.5]RU[Japanese]PB[Black]PW[White]"
      ++ "HA[2]AB[gc][cg])"
#guard (sgfOf (run cfgH2 [.play 4 4])).endsWith "AB[gc][cg]\n;W[ee])"

-- Free handicap on a nonstandard board: SZ[cols:rows], no AB, and the
-- placements appear as consecutive Black moves (legal in FF[4]).
#guard sgfOf (run cfgFree [.play 0 0, .play 0 2])
  == "(;GM[1]FF[4]CA[UTF-8]AP[GoLean]SZ[7:5]KM[6.5]RU[Japanese]PB[Black]PW[White]"
      ++ "HA[3]\n;B[aa];B[ca])"

-- Undo is invisible in the export (the log was truncated).
#guard sgfOf tUndo == sgfOf tOne

-- Names are escaped in PB/PW.
def cfgNames : GameConfig := { size := size5, blackName := "Br[a]cket", whiteName := "Back\\slash" }
#guard sgfOf (run cfgNames [])
  == "(;GM[1]FF[4]CA[UTF-8]AP[GoLean]SZ[5]KM[6.5]RU[Japanese]PB[Br[a\\]cket]PW[Back\\\\slash])"

-- Long games break lines every 10 nodes.
def tLong := run { size := size9 } ((List.range 12).map fun i => Action.play (i / 9) (i % 9))
#guard ((sgfOf tLong).splitOn "\n").length == 3

end GoLean.Tests.Sgf
