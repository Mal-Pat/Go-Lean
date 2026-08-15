# Go-Lean

The game of Go/Baduk/Weiqi in Lean 4, with an interactive board in the VS Code infoview.

## Build & test

```sh
lake build         # library (core + protocol + widget)
lake build Tests   # run tests
```

Tests cover captures, ko and both superkos, self-capture per ruleset,
pass→scoring, dead marks and both scoring methods, undo/replay, handicap
(fixed and free placement), resignation, and the wire protocol.

## Play

Open [Sandbox.lean](Sandbox.lean) (or write `import GoLean` + `#go` in any
file) and put the cursor on the `#go` line. The board appears in the
infoview with three phases:

1. **Setup:** Before starting the game, set
    * Board Size
    * Player names
    * Handicap
    * Komi
    * Rules:
      * Presets (Japanese, Chinese, Tromp–Taylor, AGA)
      * Individual toggles (ko/superko, self-capture, territory/area scoring)
2. **Play:** To play,
    * Click on the board to place stones
    * Click the buttons for pass, undo, resign
    * Captures, move number and last-move marker are displayed
    * Illegal moves (occupied, ko, superko, self-capture) are refused with a message
3. **Scoring:** After consecutive passes, 
    * Click chains to mark them dead/alive
    * The live score card is displayed
    * Both players accept (or resume play on a dispute)
    * The final score and winner are displayed

## Architecture

- `GoLean/Core/` contains a pure rules engine
  (`Game.step : Game → Action → Except IllegalAction Game`). 
  One generic flood fill (`Board.region`) works for
  chains, captures and territory.
- `GoLean/Protocol.lean` contains JSON DTOs. The wire state held by the client is
  the event log (config + actions), which is rebuilt server-side by folding `step`.
- `GoLean/Widget.lean` + `GoLean/widget/goBoard.js` contains one RPC method and a
  plain-JS React component (no npm build step). The JS renders the view and reports clicks.

`OldGoLean/` is the previous prototype, kept for reference. It is not part
of the build.