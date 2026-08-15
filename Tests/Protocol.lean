/-
Authors: Malhar A. Patel
-/

import GoLean.Protocol

/-!
# Protocol tests

Headless checks of `handleUpdate` — the exact function behind the RPC
method — covering the wire contract: log advances only on success, undo
truncates, config errors return no view.
-/

namespace GoLean.Tests.Protocol

open GoLean

def baseCfg : ConfigDto := { rows := 5, cols := 5 }

def req (g : GameDto) (a : Option ActionDto) : UpdateRequest :=
  { game := g, action := a }

def play (r c : Nat) : ActionDto := { kind := "play", r, c }

-- Initial render (no action) succeeds.
def r0 := handleUpdate (req { config := baseCfg } none)
#guard r0.error.isNone && r0.view.isSome
#guard (r0.view.map (·.phase)) == some "playing"

-- A legal move advances the log and the view.
def r1 := handleUpdate (req r0.game (some (play 2 2)))
#guard r1.error.isNone
#guard r1.game.actions.size == 1
#guard (r1.view.map (·.moveNum)) == some 1
#guard (r1.view.map (·.toMove)) == some "white"
-- The SGF export rides along on every view.
#guard (r1.view.map (·.sgf)) ==
  some "(;GM[1]FF[4]CA[UTF-8]AP[GoLean]SZ[5]KM[6.5]RU[Japanese]PB[Black]PW[White]\n;B[cc])"

-- An illegal move reports an error and leaves the log unchanged.
def r2 := handleUpdate (req r1.game (some (play 2 2)))
#guard r2.error.isSome
#guard r2.game.actions.size == 1

-- Undo truncates the wire log (the response log is authoritative).
def r3 := handleUpdate (req r1.game (some { kind := "undo" }))
#guard r3.error.isNone
#guard r3.game.actions.size == 0

-- An unknown action kind is rejected gracefully.
def r4 := handleUpdate (req r1.game (some { kind := "teleport" }))
#guard r4.error.isSome && r4.game.actions.size == 1

-- A bad config is rejected with no view (client stays on the setup screen).
def rBad := handleUpdate (req { config := { baseCfg with rows := 1 } } none)
#guard rBad.view.isNone && rBad.error.isSome

-- Full flow to a finished game over the wire.
def finish :=
  [play 2 2, { kind := "pass" }, { kind := "pass" },
   { kind := "accept", who := "black" }, { kind := "accept", who := "white" }]
def rEnd := finish.foldl (fun r a => handleUpdate (req r.game (some a))) r0
#guard (rEnd.view.map (·.phase)) == some "finished"
#guard (rEnd.view.bind (·.result)) == some "B+17.5"
#guard (rEnd.view.map (·.scoreCard.isSome)) == some true

/-! ## Review mode -/

-- A 3-move game (two stones, one pass) over the wire.
def rMoves : List ActionDto := [play 2 2, play 1 1, { kind := "pass" }]
def rLive := rMoves.foldl (fun r a => handleUpdate (req r.game (some a))) r0

def rv (k : Nat) : UpdateResponse :=
  handleUpdate { game := rLive.game, review := some k }

def stonesIn (v : Option ViewDto) : Nat :=
  match v with
  | some view =>
    view.board.foldl (init := 0) fun n row =>
      row.foldl (init := n) fun n cell => if cell.stone != "" then n + 1 else n
  | none => 0

-- The live view advertises the move count.
#guard (rLive.view.map (·.totalMoves)) == some 3

-- Review renders phase "review" with the right counters…
#guard ((rv 0).view.map (·.phase)) == some "review"
#guard ((rv 0).view.map (·.reviewMove)) == some 0
#guard ((rv 0).view.map (·.totalMoves)) == some 3
-- …and never touches the event log.
#guard (rv 0).game.actions.size == 3

-- Stepping through the positions: empty board, then one stone, two stones,
-- and the pass leaves the board unchanged.
#guard stonesIn (rv 0).view == 0
#guard stonesIn (rv 1).view == 1
#guard stonesIn (rv 2).view == 2
#guard stonesIn (rv 3).view == 2

-- Counters and turn alternation are consistent at each step.
#guard ((rv 1).view.map (·.moveNum)) == some 1
#guard ((rv 1).view.map (·.toMove)) == some "white"
#guard ((rv 2).view.map (·.toMove)) == some "black"

-- Out-of-range indices clamp to the last move.
#guard ((rv 99).view.map (·.reviewMove)) == some 3

-- The SGF riding on a review view is still the FULL game's SGF.
#guard ((rv 1).view.map (·.sgf)) == (rLive.view.map (·.sgf))

-- Reviewing a finished game works and suppresses result/score panels.
def rvEnd := handleUpdate { game := rEnd.game, review := some 1 }
#guard (rvEnd.view.map (·.phase)) == some "review"
#guard (rvEnd.view.bind (·.result)) == none
#guard (rvEnd.view.map (·.scoreCard.isNone)) == some true
-- …and the last review position of the finished game shows the final board.
#guard stonesIn (handleUpdate { game := rEnd.game, review := some 3 }).view == 1

end GoLean.Tests.Protocol
