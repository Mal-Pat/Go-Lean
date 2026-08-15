# Go-Lean

The game of Go/Baduk/Weiqi in Lean 4, with an interactive board in the VS Code infoview.

![GoLeanSandbox](./images/GoLeanSandbox.png)

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
file) and put the cursor on the `#go` line. 

A game can also be pre-loaded from SGF (Smart Game Format) and opens in review mode:

- `#go "games/sample.sgf"`, from a file (path relative to the current file)
- `#go from mySgfString`, from a `String`-valued SGF term
- `#go`, and paste an SGF into the **Load from SGF** box on the setup screen

The board appears in the infoview with three phases:

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

In any phase, 
- **Review moves** switches to a read-only replay of the game.
  Step through the positions with ⏮ ◀ ▶ ⏭ or the slider. Click
  **Back to game** to return to the live game (which is not affected in the review mode).
- **Copy SGF** exports the game so far in Smart Game Format 
  (paste into a `.sgf` file to open it in any Go program)
- **Copy JSON** exports the raw game record so far

## Architecture

- `GoLean/Core/` contains a pure rules engine
  (`Game.step : Game → Action → Except IllegalAction Game`). 
  One generic flood fill (`Board.region`) works for
  chains, captures and territory.
- `GoLean/Core/Sgf.lean` serializes a game to SGF FF[4] (Smart Game Format File Format 4)
- `GoLean/Core/SgfParse.lean` parses SGF back into a game (`Sgf.load`),
  validated by replaying every move through the rules engine, ensuring a loaded game
  is legal-by-construction. It is also forgiving when real files need it (HA with no
  AB, ko rules laxer than the engine's), with each case reported as a warning.
- `GoLean/Protocol.lean` contains JSON DTOs. The wire state held by the client is
  the event log (config + actions), which is rebuilt server-side by folding `step`.
- `GoLean/Widget.lean` + `GoLean/widget/goBoard.js` contains one RPC method and a
  plain-JS React component (no npm build step). The JS renders the view and reports clicks.

`OldGoLean/` is the previous prototype, kept for reference. It is not part
of the build.