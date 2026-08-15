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
Place the cursor on this command to play. -/
syntax (name := goCmd) "#go" : command

@[command_elab goCmd]
def elabGoCmd : CommandElab := fun stx => do
  liftCoreM <| Widget.savePanelWidgetInfo
    (hash GoBoardWidget.javascript)
    (return Json.mkObj [])
    stx

end GoLean
