import NumLean.Tactic.ApplyRuleSets.Types
import Lean.Elab.Tactic.ElabTerm

namespace NumLean.Tactic.ApplyRuleSets

open Lean Meta Elab Term

abbrev RuleProc := Array Expr -> ArgOrigin -> Expr -> ApplyRuleSetsM (Option Expr)

structure RuleProcDecl where
  declName : Name
  pattern : Expr
  levelParams : Array Name := #[]
  defaultProc? : Option Expr := none
deriving Inhabited

initialize ruleProcDeclExt : SimpleScopedEnvExtension RuleProcDecl (Std.HashMap Name RuleProcDecl) <-
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun s e => s.insert e.declName e
  }

def registerRuleProcPattern (declName : Name) (pattern : Expr) (levelParams : Array Name := #[])
    (defaultProc? : Option Expr := none) : MetaM Unit := do
  if pattern.hasExprMVar then
    throwError "invalid ruleproc pattern for `{.ofConstName declName}` contains expression metavariables"
  let levelParams := levelParams ++ (exprLevelParams pattern).filter (!levelParams.contains ·)
  modifyEnv fun env => ruleProcDeclExt.addEntry env { declName, pattern, levelParams, defaultProc? }

def getRuleProcDecl? (declName : Name) : CoreM (Option RuleProcDecl) := do
  return (ruleProcDeclExt.getState (← getEnv)).get? declName

unsafe def evalRuleProcImpl (proc : Expr) : MetaM RuleProc := do
  Meta.evalExpr RuleProc (mkConst ``RuleProc) proc (safety := .unsafe)

@[implemented_by evalRuleProcImpl]
opaque evalRuleProc (proc : Expr) : MetaM RuleProc

def explicitRuleProcRule? (origin : Origin) (proc : Expr) : MetaM (Option Rule) := do
  let some declName := proc.getAppFn.constName? | return none
  let some decl ← getRuleProcDecl? declName | return none
  unless ← isDefEq (← inferType proc) (mkConst ``RuleProc) do
    return none
  let rule : Rule := { origin, type := .proc proc, pattern := decl.pattern, levelParams := decl.levelParams }
  if rule.hasExprMVar then
    throwError "explicit ruleproc `{.ofConstName declName}` contains expression metavariables"
  return some rule

private def removeUnusedForallBinders (e : Expr) (keepPrefix : Nat := 0) : MetaM Expr := do
  forallTelescope e fun xs body => do
    let mut result := body
    for _h : i in [:xs.size] do
      let i := xs.size - 1 - i
      let x := xs[i]!
      if i < keepPrefix || result.containsFVar x.fvarId! then
        let decl ← x.fvarId!.getDecl
        result := Expr.forallE decl.userName decl.type (result.abstract #[x]) decl.binderInfo
    return result

private def closeRuleProcPattern (pat : Term) : TermElabM (Expr × Array Name × Array (Nat × Name)) := do
  let pattern ← Term.withAutoBoundImplicit <| Term.elabType pat
  Term.synthesizeSyntheticMVars
  let pattern ← abstractMVars (← instantiateMVars pattern)
  let levelParams := pattern.paramNames
  let pattern ← lambdaTelescope pattern.expr fun xs pattern => mkForallFVars xs pattern
  let pattern ← removeUnusedForallBinders pattern
  let names ← forallTelescope pattern fun xs _ => do
    let mut names := #[]
    for h : i in [:xs.size] do
      let name ← xs[i].fvarId!.getUserName
      unless name.isAnonymous do
        names := names.push (i, name)
    return names
  return (pattern, levelParams, names)

private def mkRuleProcBody (xs : Ident) (names : Array (Nat × Name)) (body : Term) : MacroM Term := do
  let mut result := body
  for i in [0:names.size] do
    let i := names.size - 1 - i
    let (argIdx, name) := names[i]!
    let id := mkIdentFrom body name
    let idx := quote argIdx
    result ← `(let $id:ident : Lean.Expr := $xs[$idx]!; $result)
  return result

private def attrInstancesOfAttributes (attrs : TSyntax ``Lean.Parser.Term.attributes) :
    Array (TSyntax ``Lean.Parser.Term.attrInstance) :=
  attrs.raw[1].getArgs.filterMap fun stx =>
    if stx.isOfKind ``Lean.Parser.Term.attrInstance then
      some ⟨stx⟩
    else
      none

syntax (name := ruleprocCmd) (docComment)? (Lean.Parser.Term.attributes)? "ruleproc " ident
  (ppSpace bracketedBinder)* "," (ppSpace bracketedBinder)* " : " term " := " term : command

@[command_elab ruleprocCmd]
def elabRuleProc : Command.CommandElab := fun stx => do
  let `(command| $[$doc?:docComment]? $[$attrs?:attributes]? ruleproc $n:ident $procBs*,
      $patternBs* : $pat:term := $body:term) := stx
    | throwUnsupportedSyntax
  let (pattern, levelParams, names) ← Command.liftTermElabM <|
    closeRuleProcPattern (← `(∀ $patternBs*, $pat))
  let xs := mkIdent `__ruleprocArgs
  let body ← liftMacroM <| mkRuleProcBody xs names body
  let cmd ← `($[$doc?:docComment]? unsafe def $n $procBs* :
    NumLean.Tactic.ApplyRuleSets.RuleProc := fun $xs:ident => $body)
  Command.elabCommand cmd
  Command.liftTermElabM do
    let declName ← realizeGlobalConstNoOverload n
    let info ← getConstInfo declName
    registerRuleProcPattern declName pattern levelParams (some <| mkConst declName (info.levelParams.map Level.param))
  if let some attrs := attrs? then
    for attr in attrInstancesOfAttributes attrs do
      Command.elabCommand (← `(command| attribute [$attr:attrInstance] $n:ident))

end NumLean.Tactic.ApplyRuleSets
