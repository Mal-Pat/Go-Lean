import GoLean

/-!
Ensure the infoview is open, and put your cursor on the `#go` line.
An interactive dashboard to set up a Go game will appear in the infoview.
Set up the game, and then click on the "Start Game" button.
Place stones by clicking on the board or pass/undo/resign using the buttons.
After two passes, the game enters the "scoring" phase.
Mark chains of stones as dead or alive by clicking on them.
The game finishes when both players accept the score.
Export the game in SGF or JSON format from the buttons below.
Enter review mode by clicking on the "Review Game" button.
-/

#go

/-!
A game can also be pre-loaded from SGF.
It opens in review mode so you can step through the moves.
You can continue playing via the "Back to game" button.

There are three ways to do this:

- from a file (path relative to this file): `#go "games/sample.sgf"`
- from a string: `#go from "(;GM[1]FF[4]SZ[9];B[ee];W[cc])"`
- from a string pasted in the "Load from SGF" box on the setup screen of `#go`
-/

#go "games/sample.sgf"

#go "games/sjs_katago_game2.sgf"

#go from "(;GM[1]FF[4]SZ[9];B[ee];W[cc])"
