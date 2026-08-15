import GoLean

/-!
Open this file in VS Code (with the infoview visible) and put your cursor
on the `#go` line below: the interactive Go board appears in the infoview.

Set up the game (size, names, handicap, komi, ruleset presets + toggles).
Click on the board to place stones or the buttons for pass/undo/resign.
After two passes, click chains to mark them dead.
The game finishes when both players accept the score.
-/

#go

/-!
A game can also be pre-loaded from SGF — it opens in review mode so you
can step through the moves (and continue playing via "Back to game"):

- from a file (path relative to this file): `#go "games/sample.sgf"`
- from a string: `#go from "(;GM[1]FF[4]SZ[9];B[ee];W[cc])"`

There is also a "Load from SGF" box on the setup screen for pasting.
-/

#go "games/sample.sgf"

#go "games/sjs_katago_game2.sgf"

#go from "(;GM[1]FF[4]SZ[9];B[ee];W[cc])"
