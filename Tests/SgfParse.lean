/-
Authors: Malhar A. Patel
-/

import GoLean.Protocol
import Tests.Core

/-!
# SGF import tests

Covers: parsing (coordinates, passes, escapes, defaults, variations →
main line only), export/import round trips, the forgiving-import policies
(HA-with-no-AB, ko degradation), error cases, and the wire-level
`importSgf` path.
-/

namespace GoLean.Tests.SgfParse

open GoLean GoLean.Tests

/-- Local convenience: compare `Except` results in `#guard`s. -/
local instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e, .error f => e == f
    | _, _ => false

/-! ## Basic parsing -/

def imp1 := Sgf.load "(;GM[1]FF[4]SZ[9];B[ee];W[cc])"
#guard (imp1.map (·.moves)) == .ok #[.play 4 4, .play 2 2]
#guard (imp1.map (·.config.size.rows)) == .ok 9
#guard (imp1.map (·.config.size.cols)) == .ok 9
#guard (imp1.map (·.warnings.isEmpty)) == .ok true

-- Defaults: 19×19, Japanese, komi 6.5.
def impDef := Sgf.load "(;GM[1])"
#guard (impDef.map (·.config.size.rows)) == .ok 19
#guard (impDef.map (·.config.komi2)) == .ok 13
#guard (impDef.map (·.moves.size)) == .ok 0

-- Passes: both `[]` and (on boards ≤ 19) `[tt]`.
#guard (Sgf.load "(;SZ[9];B[ee];W[];B[tt])" |>.map (·.moves))
  == .ok #[.play 4 4, .pass, .pass]

-- Non-square boards: SZ[cols:rows].
def impNsq := Sgf.load "(;SZ[7:5];B[fa])"
#guard (impNsq.map (·.config.size.rows)) == .ok 5
#guard (impNsq.map (·.config.size.cols)) == .ok 7
#guard (impNsq.map (·.moves)) == .ok #[.play 0 5]

-- Names, rules, komi.
def impMeta := Sgf.load "(;SZ[9]RU[Chinese]KM[7.5]PB[A \\] B]PW[C])"
#guard (impMeta.map (·.config.blackName)) == .ok "A ] B"
#guard (impMeta.map (·.config.whiteName)) == .ok "C"
#guard (impMeta.map (·.config.komi2)) == .ok 15
#guard (impMeta.map (·.config.ruleset.scoring)) == .ok .area

-- Komi format variants.
#guard parseKomi2? "6.5" == some 13
#guard parseKomi2? "7" == some 14
#guard parseKomi2? "0,5" == some 1
#guard parseKomi2? "-2.5" == some (-5)
#guard parseKomi2? "x" == none

/-! ## The sample fixture: realistic header, comment with escaped bracket,
and two variations (only the first — the main line — is followed). -/

def fixture : String :=
  "(;GM[1]FF[4]CA[UTF-8]AP[GoLean sample]SZ[19]KM[6.5]RU[Japanese]\n" ++
  "PB[Black Pro]PW[White Pro]C[A sample game record with an escaped \\] bracket.]\n" ++
  ";B[pd];W[dp];B[pq];W[dd];B[qk]\n" ++
  "(;W[nc];B[pf];W[jd])\n" ++
  "(;W[mp];B[po]))"

def impFix := Sgf.load fixture
#guard (impFix.map (·.moves)) == .ok
  #[.play 3 15, .play 15 3, .play 16 15, .play 3 3, .play 10 16,
    .play 2 13, .play 5 15, .play 3 9]
#guard (impFix.map (·.config.blackName)) == .ok "Black Pro"
#guard (impFix.map (·.config.komi2)) == .ok 13
#guard (impFix.map (·.warnings.isEmpty)) == .ok true

/-! ## Export/import round trips -/

/-- Strict round trip: reimporting the export rebuilds a game with the
same SGF and the same board. -/
def rtSgfEq (eg : Except IllegalAction Game) : Bool :=
  match eg with
  | .error _ => false
  | .ok g =>
    match Sgf.load g.toSgf with
    | .error _ => false
    | .ok imp =>
      match Game.ofRecord imp.config imp.moves with
      | .error _ => false
      | .ok g' => g'.toSgf == g.toSgf && g'.curBoard.toStrings == g.curBoard.toStrings

/-- Board-only round trip (for games whose export normalizes information
away: finished results, free-handicap placements). -/
def rtBoardEq (eg : Except IllegalAction Game) : Bool :=
  match eg with
  | .error _ => false
  | .ok g =>
    match Sgf.load g.toSgf with
    | .error _ => false
    | .ok imp =>
      match Game.ofRecord imp.config imp.moves with
      | .error _ => false
      | .ok g' => g'.curBoard.toStrings == g.curBoard.toStrings

#guard rtSgfEq tCorner
#guard rtSgfEq tGroup
#guard rtSgfEq (run cfgH2 [.play 4 4])          -- fixed handicap: HA + AB
#guard rtSgfEq (run (cfgKo .positionalSuperko) koMoves)
#guard rtBoardEq tScore                          -- finished: RE not reimported
#guard rtBoardEq (run cfgFree [.play 0 0, .play 0 2, .play 0 4, .play 2 2])
                                                 -- free handicap → AB on reimport

/-! ## Forgiving-import policies -/

-- HA with no AB: leading Black moves become handicap stones.
def impHa := Sgf.load "(;SZ[9]HA[2];B[cc];B[gg];W[ee])"
#guard (impHa.map (·.config.setupBlack.length)) == .ok 2
#guard (impHa.map (·.moves)) == .ok #[.play 4 4]
#guard (impHa.map (·.warnings.length)) == .ok 1

-- A ko-rule violation degrades the ko rule (with a warning) instead of
-- failing: this game ends with an immediate ko recapture.
def koSgf : String :=
  "(;SZ[5]RU[Chinese];B[ba];W[ca];B[ab];W[db];B[bc];W[cc];B[cb];W[bb];B[cb])"
def impKo := Sgf.load koSgf
#guard (impKo.map (·.config.ruleset.ko)) == .ok .none
#guard (impKo.map (·.moves.size)) == .ok 9
#guard (impKo.map (·.warnings.length)) == .ok 1

-- PL forces the first mover and survives export.
def impPl := Sgf.load "(;SZ[9]PL[W])"
#guard (impPl.map (·.config.firstToMove)) == .ok (some .white)
#guard (impPl.map fun imp =>
    match Game.ofRecord imp.config imp.moves with
    | .ok g => g.curPlayState.toMove == .white && g.toSgf.endsWith "PL[W])"
    | .error _ => false)
  == .ok true

/-! ## Errors -/

def isLoadError (s : String) : Bool := (Sgf.load s) matches .error _

#guard isLoadError "(;SZ[9];B[aa];B[bb])"      -- non-alternating colors
#guard isLoadError "(;SZ[9];B[aa];W[aa])"      -- illegal move (occupied)
#guard isLoadError "(;SZ[9];B[aa]"             -- unbalanced parens
#guard isLoadError "(;SZ[bad])"                -- bad SZ
#guard isLoadError "(;SZ[5]AB[jj])"            -- setup stone off the board
#guard isLoadError "(;SZ[9];B[aa];AB[cc])"     -- mid-game setup stones
#guard isLoadError "hello"                     -- not SGF at all
#guard isLoadError "(;SZ[9];B[zz])"            -- move off the board

/-! ## The wire-level import path -/

def impResp := handleUpdate { game := { config := {} }, importSgf := some fixture }
#guard impResp.error.isNone
#guard (impResp.view.map (·.phase)) == some "playing"
#guard (impResp.view.map (·.totalMoves)) == some 8
#guard impResp.game.actions.size == 8
#guard (impResp.view.map (·.blackName)) == some "Black Pro"

-- The returned wire state is self-sufficient: it rebuilds to the same game.
#guard (impResp.game.build.toOption.map Game.toSgf)
  == ((Sgf.load fixture).toOption.bind fun imp =>
        (Game.ofRecord imp.config imp.moves).toOption.map Game.toSgf)

-- Warnings surface on the wire.
def impRespKo := handleUpdate { game := { config := {} }, importSgf := some koSgf }
#guard impRespKo.warning.isSome
#guard impRespKo.error.isNone

-- A bad SGF yields an error and no view (client stays on the setup screen).
def impRespBad := handleUpdate { game := { config := {} }, importSgf := some "nope" }
#guard impRespBad.error.isSome
#guard impRespBad.view.isNone

end GoLean.Tests.SgfParse
