/-
Authors: Malhar A. Patel
-/

import Lean
import GoLean.Protocol

/-!
# The infoview widget

One RPC method (`GoLean.update`) running the pure `handleUpdate`, one
widget module (plain-JS React component), and a `#go` command that displays it.
All rules logic stays in Lean; the JS renders the `ViewDto` and reports clicks.

Usage: write `#go` in any file importing this module and place the cursor
on it.
-/

namespace GoLean

open Lean Elab Command Server

/-- The single RPC entry point for the Go board widget. -/
@[server_rpc_method]
def update (req : UpdateRequest) : RequestM (RequestTask UpdateResponse) :=
  RequestM.asTask do
    return handleUpdate req

/-- The Go board React component (plain JavaScript, no build step). -/
@[widget_module]
def GoBoardWidget : Widget.Module where
  javascript := include_str "widget" / "goBoard.js"

/-- Display the interactive Go board in the infoview.
Place the cursor on this command to play.

- `#go` — start at the setup screen.
- `#go "path/to/game.sgf"` — load a game from an SGF file (path relative
  to the file containing the command) and open it in review mode.
- `#go from sgfString` — same, from any `String`-valued term. -/
syntax (name := goCmd) "#go" (ppSpace str)? : command

/-- `#go from sgfString`: load a game from an SGF string term. -/
syntax (name := goFromCmd) "#go" ppSpace "from" ppSpace term : command

private unsafe def evalStringTermUnsafe (t : Term) : TermElabM String :=
  Term.evalTerm String (mkConst ``String) t

@[implemented_by evalStringTermUnsafe]
private opaque evalStringTerm : Term → TermElabM String

/-- Elaborate a `#go` command, optionally preloading an SGF game: it is
parsed and validated at elaboration time (errors appear on the command)
and handed to the widget as props. -/
def elabGo (stx : Syntax) (sgfText? : Option String) : CommandElabM Unit := do
  let props ←
    match sgfText? with
    | none => pure (Json.mkObj [])
    | some text =>
      match Sgf.load text with
      | .error e => throwError e
      | .ok imp =>
        for w in imp.warnings do
          logWarning w
        pure <| Json.mkObj
          [("game", toJson imp.toGameDto),
           ("warnings", toJson imp.warnings.toArray)]
  liftCoreM <| Widget.savePanelWidgetInfo
    (hash GoBoardWidget.javascript)
    (return props)
    stx

@[command_elab goCmd]
def elabGoCmd : CommandElab := fun stx => do
  let arg := stx[1]
  if arg.getNumArgs == 0 then
    elabGo stx none
  else
    let some pathLit := arg[0].isStrLit?
      | throwError "#go: expected a string literal path"
    let srcDir := (System.FilePath.mk (← read).fileName).parent.getD "."
    let path : System.FilePath :=
      if System.FilePath.isAbsolute pathLit then pathLit else srcDir / pathLit
    let text ←
      try
        IO.FS.readFile path
      catch e =>
        throwError "#go: cannot read '{path}': {e.toMessageData}"
    elabGo stx (some text)

@[command_elab goFromCmd]
def elabGoFromCmd : CommandElab := fun stx => do
  let text ← liftTermElabM <| evalStringTerm ⟨stx[2]⟩
  elabGo stx (some text)

end GoLean
