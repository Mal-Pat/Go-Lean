import Lean
import ProofWidgets
import GoLean.Go

open Lean Meta Tactic

inductive ReflTransClosure {α} (r : α → α → Prop) (a : α) : α → Prop
  | refl : ReflTransClosure r a a
  | tail {b c : α} : ReflTransClosure r a b → r b c → ReflTransClosure r a c

inductive GsRel {s} : GameState s → GameState s → Prop where
  | move (r c : Nat) (gs : GameState s) : GsRel gs (gs.moveN r c)
  | pass (gs : GameState s) : GsRel gs gs.pass
  | setP1 (p1 : String) (gs : GameState s) : GsRel gs
    {gs with gameDetails := {gs.gameDetails with player1 := p1}}
  | setP2 (p2 : String) (gs : GameState s) : GsRel gs
    {gs with gameDetails := {gs.gameDetails with player2 := p2}}

abbrev GsReachable {s} : GameState s → GameState s → Prop :=
  ReflTransClosure GsRel

def Game (s : Size) {gs : GameState s} (_ : GsReachable {} gs) : Prop :=
  ∃ end_gs : GameState s, GsReachable default end_gs

theorem Game.play {s} {gs : GameState s} {path : GsReachable {} gs} (r c : Nat) :
  Game s (ReflTransClosure.tail path (GsRel.move r c gs)) → Game s path := id

theorem Game.pass {s} {gs : GameState s} {path : GsReachable {} gs} :
  Game s (ReflTransClosure.tail path (GsRel.pass gs)) → Game s path := id

theorem Game.close {s} {gs : GameState s} {path : GsReachable {} gs} :
  Game s path := ⟨gs, path⟩

macro "play" row:num col:num : tactic =>
  `(tactic| apply Game.play $row $col)

macro "close" : tactic =>
  `(tactic| exact Game.close)

def t1 : Game s[5,5] .refl := by
  play 0 0
  play 1 1
  close

-- [Insert your existing Go implementation here...]

open Lean Elab Meta Tactic ProofWidgets Server Jsx

section Widget

-- 1. Derive TypeName for Color so it can be evaluated by the widget
deriving instance TypeName for Color

-- 2. Define a monomorphic version of the game state to safely evaluate via `evalExpr`
structure SimpleGameState where
  rl : Nat
  cl : Nat
  board : List (List (Option Color))
  turn : Color
deriving TypeName

-- 3. Conversion function to strip the dependent size types for the widget
def GameState.toSimple {s} (gs : GameState s) : SimpleGameState :=
  { rl := s.rl,
    cl := s.cl,
    board := gs.board.toList.map (fun row => row.toList),
    turn := gs.turn }

@[server_rpc_method]
def Renderer.rpcMethod (props : PanelWidgetProps) : RequestM (RequestTask Html) := RequestM.asTask do
  let docMeta := (← read).doc.meta
  if props.goals.isEmpty then
    return <span>No goals.</span>

  let some g := props.goals[0]? | unreachable!

  g.ctx.val.runMetaM {} do
    let md ← g.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      let goal := md.type
      match goal with
      -- Matches: Game s gs path
      | .app (.app (.app (.const ``Game _) _) gsExpr) _ =>
        -- Convert the dependently typed GameState into our SimpleGameState
        let simpleGsExpr ← Meta.mkAppM ``GameState.toSimple #[gsExpr]
        let simpleGs ← unsafe Meta.evalExpr SimpleGameState (.const ``SimpleGameState []) simpleGsExpr
        return renderBoard docMeta simpleGs
      | _ => return <span>Goal is not a `Game` goal.</span>
  where
    renderCell (docMeta : DocumentMeta) (cell : Option Color) (r c : Nat) : Html :=
      let stoneColor := match cell with
        | some .B => "black"
        | some .W => "white"
        | none => "transparent"

      let stoneShadow := match cell with
        | none => "none"
        | _ => "1px 1px 3px rgba(0,0,0,0.5)"

      -- 1. Build the JSON objects directly to avoid json% macro interpolation bugs
      let stoneStyle := Json.mkObj [
        ("width", "1.5em"),
        ("height", "1.5em"),
        ("borderRadius", "50%"),
        ("backgroundColor", stoneColor),
        ("boxShadow", stoneShadow),
        ("margin", "auto")
      ];

      let cellStyle := Json.mkObj [
        ("width", "2em"),
        ("height", "2em"),
        ("background", "linear-gradient(to right, transparent 48%, #333 48%, #333 52%, transparent 52%), linear-gradient(to bottom, transparent 48%, #333 48%, #333 52%, transparent 52%)"),
        ("cursor", "pointer"),
        ("padding", "0")
      ];

      let range : Lsp.Range := ⟨props.pos, props.pos⟩;
      let editProps := MakeEditLinkProps.ofReplaceRange' docMeta range s!"\n  play {r} {c}";

      -- 2. Use explicit type annotations and semicolons to keep the parser perfectly aligned
      let stoneHtml : Html := <div style={stoneStyle}></div>;
      let editHtml : Html := Html.ofComponent MakeEditLink editProps #[stoneHtml];

      <td style={cellStyle}>{editHtml}</td>

    renderRow (docMeta : DocumentMeta) (row : List (Option Color)) (r : Nat) : Html :=
      let cells := (List.zip (List.range row.length) row).map fun (c, cell) => renderCell docMeta cell r c;
      -- Construct the <tr> natively to accept the Array Html without JSX confusion
      Html.element "tr" #[] cells.toArray

    renderBoard (docMeta : DocumentMeta) (state : SimpleGameState) : Html :=
      let rows := (List.zip (List.range state.board.length) state.board).map fun (r, row) => renderRow docMeta row r;
      -- Construct the <tbody> natively
      let tbody := Html.element "tbody" #[] rows.toArray;

      <div style={json% {display: "flex", flexDirection: "column", alignItems: "center", marginTop: "1em", fontFamily: "sans-serif"}}>
        <table style={json% {borderCollapse: "collapse", backgroundColor: "#dcab6b", boxShadow: "0 4px 6px rgba(0,0,0,0.3)"}}>
          {tbody}
        </table>
        <div style={json% {marginTop: "1em", fontSize: "1.2em", padding: "0.2em"}}>
          <strong>{Html.text "To Move: "}</strong>
          {Html.text (toString state.turn)}
        </div>
        <div style={json% {marginTop: "0.1em", fontSize: "1.2em", padding: "0.2em"}}>
          <strong>{Html.text "To Move: "}</strong>
          {Html.text (toString state.turn)}
        </div>
      </div>

@[widget_module]
def Renderer : Component PanelWidgetProps :=
  mk_rpc_widget% Renderer.rpcMethod

-- Activate the widget
show_panel_widgets [Renderer]

example : Game s[9,9] .refl := by
  play 0 0
  play 0 1
  play 1 0
  play 1 1
  play 2 1
  play 2 0
  close

example : Game s[9,9] .refl := by
  play 1 2
  play 1 1
  play 2 1
  play 0 3
  play 0 1
  play 1 4
  close

example : Game s[19,19] .refl := by
  play 2 2
  play 1 1
  play 1 2
  play 2 1
  play 3 1
  play 0 1
  play 0 2
  play 2 0
  play 3 0
  play 0 0
  play 1 0
  close


-- Test it out! Click the board in the infoview to play moves.
def t2 : Game s[5,5] .refl := by
  play 1 0
  play 0 1
  play 1 1
  play 0 0
  play 0 2
  play 1 2
  play 1 3
  play 2 0
  play 2 2
  play 2 1
  play 3 1
  play 3 0
  play 4 0
  close

example : Game s[19,19] .refl := by

  play 2 2
  play 1 6
  play 1 4
  play 17 16
  play 16 16
  play 13 4
  play 13 2
  play 16 4
  play 16 2
  play 15 15
  play 16 15
  play 2 16
  play 1 14
  play 10 2
  play 16 6
  play 6 2
  play 8 2
  play 4 2
  play 3 1
  play 13 16
  play 14 17
  play 5 16
  play 2 12
  close

example : Game s[9,9] .refl := by

  play 5 3
  play 2 6
  play 4 6
  play 2 3
  play 2 1
  play 1 1
  play 2 2
  play 1 2
  play 3 3
  play 6 2
  play 6 3
  play 2 4
  play 7 2
  play 6 6
  play 6 5
  play 7 4
  play 7 5
  play 3 7
  play 4 7
  play 3 5
  play 6 7
  play 8 5
  play 7 6
  play 7 7
  play 6 1
  play 5 6
  play 5 5
  play 5 7
  play 5 8
  play 4 3
  play 4 2
  play 5 2
  play 5 1
  play 3 4
  play 4 4
  play 8 6
  play 3 8
  play 2 8
  play 4 8
  play 1 0
  play 2 0
  play 7 8
  play 6 8
  play 8 7
  play 7 3
  play 6 4
  play 5 4
  play 8 4
  play 8 3
  play 3 6
  play 8 8
  close

example : Game s[9,9] .refl := by
  play 3 3
  play 4 4
  play 4 3
  play 3 4
  play 6 6
  play 5 7
  play 5 6
  play 6 4
  play 4 7
  play 6 7
  play 7 7
  play 6 2
  play 5 3
  play 6 3
  play 5 4
  play 5 5
  play 4 5
  play 6 5
  play 2 4
  play 3 5
  play 4 6
  play 3 6
  play 3 7
  play 2 5
  play 1 5
  play 2 6
  play 1 6
  play 2 7
  play 1 7
  play 3 8
  play 2 8
  play 4 1
  play 3 1
  play 3 2
  play 4 2
  play 2 2
  play 5 1
  play 2 1
  play 4 0
  play 6 1
  play 6 0
  play 7 0
  play 5 0
  play 7 6
  play 7 5
  play 8 6
  play 7 4
  play 7 3
  play 8 7
  play 8 4
  play 8 5
  play 5 8
  play 7 1
  play 8 1
  play 8 0
  play 7 2
  play 8 2
  play 5 2
  play 8 3
  close

example : Game s[13,13] .refl := by
  play 2 2
  play 1 1
  play 1 2
  play 0 1
  play 0 2
  play 1 0
  play 2 1
  play 2 0
  play 3 0
  play 3 1
  play 0 0
  close

example : Game s[13,13] .refl := by
  play 1 1
  play 1 0
  play 2 0
  play 0 0
  play 0 1
  play 2 1
  play 3 1
  play 3 0
  play 3 2
  play 1 0
  play 2 2
  play 1 2
  play 1 3
  play 0 2
  play 0 4
  play 0 0
  close
