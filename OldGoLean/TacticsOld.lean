import Lean
import GoLean.Go

open Lean Meta Elab Command Tactic PrettyPrinter Syntax

def game0 : GameState s[19,19] :=
  startGame.playGame [ n[1,1], n[0,0], n[0,2], n[0,1], n[1,0] ]

def game1 : GameState s[19,19] :=
  startGame.playGame [ n[1,1], n[0,0], n[0,2], n[0,1], n[1,0] ]

/-- Helper to find the 'gs' variable in the current local context -/
def getDeclFromName (goal : MVarId) (name : Name) : TacticM LocalDecl := do
  goal.withContext do
    let lctx ← getLCtx
    match lctx.findFromUserName? name with
    | some decl => return decl
    | none => throwError "No game in progress. Call 'empty' first."

instance {s} : ToFormat (GameState s) where
  format gs := .text s!"{gs}"

def createHyp (hypType : Expr) (hypProof : Expr) (hypName := `h) : TacticM Unit := do
  unless ← isDefEq hypType (← inferType hypProof) do
    throwError
      "The value of the hypothesis does not match the type"
  let hyp : Hypothesis := {
    userName := hypName,
    type := hypType,
    value := hypProof
  }
  let (_, new_goal) ← (← getMainGoal).assertHypotheses (
    List.toArray [hyp]
  )
  setGoals [new_goal]

/-- Helper to evaluate and print GameState -/
def displayGameStateFromDecl (ldecl : LocalDecl) : TacticM Unit := do
  let args := ldecl.type.getAppArgs
  let sizeExpr := args[0]!
  let s ← unsafe evalExpr Size (mkConst ``Size) sizeExpr
  match ldecl.value? true with
  | none => throwError "value not accessible"
  | some value =>
    let gs ← unsafe evalExpr (GameState s) ldecl.type value
    logInfo m!"{gs}"

def displayGameState (type value : Expr) : TacticM Unit := do
  let args := type.getAppArgs
  let sizeExpr := args[0]!
  let s ← unsafe evalExpr Size (mkConst ``Size) sizeExpr
  let gs ← unsafe evalExpr (GameState s) type value
  logInfo m!"{gs}"

def GameStateExpr : TacticM Expr := do
  let mvar ← mkFreshExprMVar (Expr.const ``Size [])
  return .app (.const ``GameState []) mvar

#print instantiateMVars

syntax (name := emptyTactic) "empty" ("at" ident)? : tactic
@[tactic emptyTactic]
def evalEmpty : Tactic := fun stx => do
  let goal ← getMainGoal
  goal.withContext do
    let goalType ← goal.getType
    unless ← isDefEq goalType (← GameStateExpr) do
      throwError "Goal must be GameState s"
    let args := goalType.getAppArgs
    let sizeExpr := args[0]!
    logInfo s!"sizeExpr: {sizeExpr}"
    let startExpr ← mkAppOptM ``startGame #[sizeExpr]
    logInfo s!"startExpr: {startExpr}"
    logInfo s!"startExpr: {← Meta.ppExpr startExpr}"
    logInfo s!"inst startExpr: {← Meta.ppExpr <| ← instantiateMVars startExpr}"
    displayGameState goalType startExpr
    let name := stx[1][1]
    createHyp goalType startExpr name.getId

def findDeclOfGoalType (goal : MVarId) : TacticM LocalDecl := do
  let goalType ← goal.getType
  goal.withContext do
    let matchingDecl? ← (← getLCtx).findDeclM? fun ldecl => do
      if ldecl.isImplementationDetail then return none
      let declExpr := ldecl.toExpr
      let declType ← inferType declExpr
      if ← isExprDefEq goalType declType then
        return some ldecl
      else return none
    match matchingDecl? with
    | none => throwError m!"no matching local decl"
    | some decl => return decl

def mkIdentForDeclOfGoalType (goal : MVarId) : TacticM Ident := do
  return mkIdent (← findDeclOfGoalType goal).userName

-- syntax (name := playTactic) "play" num num ("at" ident)? ("to" ident)? : tactic
-- @[tactic playTactic]
-- def evalPlay : Tactic := fun stx => do
--   let r := mkNumLit (toString stx[1].isNatLit?.get!)
--   let c := mkNumLit (toString stx[2].isNatLit?.get!)
--   let at_stx := stx[3][1]
--   let to_stx := stx[4][1]
--   let goal ← getMainGoal
--   let goalType ← goal.getType
--   -- goal.withContext do
--   -- let decl ← getDeclFromName goal `g
--   -- logInfo s!"{decl.value}"
--   goal.withContext do
--   match at_stx, to_stx with
--   | `($atId:ident), `($toId:ident) =>
--     let newGs ← `(GameState.moveN $atId $r $c)
--     evalTactic (← `(tactic| let $toId := $newGs))
--   | `($atId:ident), _ =>
--     let newGs ← `(GameState.moveN $atId $r $c)
--     evalTactic (← `(tactic| replace $atId := $newGs))
--   | _ , `($toId:ident) =>
--     let declId ← mkIdentForDeclOfGoalType goal
--     let newGs ← `(GameState.moveN $declId $r $c)
--     evalTactic (← `(tactic| let $toId := $newGs))
--   | _ , _ =>
--     let declId ← mkIdentForDeclOfGoalType goal
--     let newGs ← `(GameState.moveN $declId $r $c)
--     --displayGameStateFromDecl decl
--     evalTactic (← `(tactic| replace $declId := $newGs))
--     goal.withContext do
--     let decl ← getDeclFromName goal declId.getId
--     logInfo "here"
--     displayGameStateFromDecl decl
--     logInfo s!"{← inferType decl.toExpr}"

syntax (name := doneTactic) "done" : tactic
@[tactic doneTactic]
def evalDone : Tactic := fun _ => do
  let goal ← getMainGoal
  goal.withContext do
    let gsDecl ← findDeclOfGoalType goal
    goal.assign gsDecl.toExpr

syntax (name := playTactic) "play" num num : tactic
@[tactic playTactic]
def evalPlay : Tactic := fun stx => do
  let r := stx[1].isNatLit?.get!
  let c := stx[2].isNatLit?.get!
  let goal ← getMainGoal
  goal.withContext do
    let decl ← findDeclOfGoalType goal
    logInfo s!"decl name: {decl.userName}"
    logInfo s!"decl value?: {decl.value? true}"
    logInfo s!"decl value: {← instantiateMVars decl.value}"
    let value ← instantiateMVars decl.value
    let goalType ← goal.getType
    unless ← isDefEq goalType (← GameStateExpr) do
      throwError "Goal must be GameState s"
    let args := goalType.getAppArgs
    let sizeExpr := args[0]!
    logInfo s!"sizeExpr: {sizeExpr}"
    let newGs ← mkAppOptM ``GameState.moveN #[sizeExpr, value, mkNatLit r, mkNatLit c]
    decl.setValue

#print MVarId.define
#print MVarId.change
#print getLocalDeclFromUserName
#print MVarId.clear

#print LocalDecl.setValue
#print MVarId.replaceLocalDeclDefEq

#print withLetDecl

def myGame : GameState s[5,5] := by
  empty at g    -- Initializes and prints empty board
  play 0 0   -- Black plays at 0,0 and prints board
  play 1 1   -- White plays at 1,1 and prints board
  play 2 2   -- Black plays at 2,2 and prints board
  done     -- Closes the goal by returning the final 'gs'

#eval myGame

def game : GameState s[5,5] := by
  let g : GameState s[5,5] := startGame
  replace g := g.moveN 0 0
  replace g := g.moveN 0 1
  done

#eval game

def game2 : GameState s[5,5] := by
  let h : GameState s[5,5] := startGame
  play 0 0
  done

#eval game2

#print LocalDecl.setValue

elab "show_hyps" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let lctx ← getLCtx
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      logInfo s!"expr: {ldecl.toExpr}"
      logInfo s!"type: {ldecl.type}"
      logInfo s!"value: {ldecl.value? true}"
      logInfo s!"name: {ldecl.userName}"
      logInfo s!"------------------------"

def f : Nat := by
  let h : Nat := 2
  show_hyps
  replace h := 3
  show_hyps
  replace h := 4
  exact h

#eval f
