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

end GoLean.Tests.Protocol
