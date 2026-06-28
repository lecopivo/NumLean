module

public import NumLean.Tactic.ApplyRuleSets.Core
public meta import NumLean.Tactic.ApplyRuleSets.Core
public import Lean.Elab.Tactic.ElabTerm

@[expose] public section

namespace NumLean.Tactic.ApplyRuleSets

open Lean Meta Elab Tactic Term
open Lean.Parser.Tactic

syntax applyRuleSetErase := "-" term:max
syntax applyRuleSetArg := applyRuleSetErase <|> term
syntax applyRuleSetArgs := "[" applyRuleSetArg,* "]"

unsafe def evalApplyRuleSetsConfigUnsafe (e : Expr) : TermElabM Config :=
  Meta.evalExpr' (safety := .unsafe) Config ``Config e

@[implemented_by evalApplyRuleSetsConfigUnsafe]
meta opaque evalApplyRuleSetsConfigExpr (e : Expr) : TermElabM Config

meta def elabApplyRuleSetsConfig (optConfig : Syntax) : TacticM Config := do
  let recover := (← read).recover
  let go : TermElabM Config := withRef optConfig do
    let items := mkConfigItemViews (getConfigItems optConfig)
    if items.isEmpty then
      return {}
    let c ← elabConfig recover ``Config items
    if c.hasSyntheticSorry then
      return {}
    if c.hasSorry then
      throwError m!"Configuration contains an unresolved placeholder"
    evalApplyRuleSetsConfigExpr c
  go

syntax (name := applyRuleSetsTac) "apply_rulesets" optConfig (ppSpace applyRuleSetArgs)? : tactic

meta def parseApplyRuleSetArgs (args : TSyntax ``applyRuleSetArgs) : Array (TSyntax ``applyRuleSetArg) :=
  match args with
  | `(applyRuleSetArgs| [$xs,*]) => xs.getElems
  | _ => #[]

meta def explicitRuleId (order : Nat) : Name :=
  `apply_rulesets.explicit ++ Name.num Name.anonymous order

meta def explicitOrigin (order : Nat) (ref : Syntax) (expr : Expr) : Origin :=
  match expr with
  | .fvar fvarId => .fvar fvarId
  | _ => match expr.constName? with
    | some declName => .decl declName
    | none => .stx (explicitRuleId order) ref

meta def mkExplicitExprRule (origin : Origin) (order : Nat) (e : Expr) : TacticM Rule := do
  let (e, pattern, levelParams) ←
    if e.isLambda then
      pure (e, ← inferType e, #[])
    else
      let e ← abstractMVars e
      pure (e.expr, ← inferType e.expr, e.paramNames)
  let rule : Rule := { origin, type := .expr e, pattern, levelParams, order }
  if rule.hasExprMVar then
    throwError "explicit rule contains expression metavariables"
  return rule

@[tactic applyRuleSetsTac]
meta def evalApplyRuleSets : Tactic := fun stx => do
  let `(tactic| apply_rulesets $cfgStx:optConfig $[$argsStx?:applyRuleSetArgs]?) := stx
    | throwUnsupportedSyntax
  let cfg ← elabApplyRuleSetsConfig cfgStx
  let args := argsStx?.map parseApplyRuleSetArgs |>.getD #[]
  let mut rulesets := #[]
  let mut explicitTerms : Array Term := #[]
  let mut erased : Std.HashSet Name := {}
  for arg in args do
    match arg with
    | `(applyRuleSetArg| - $t:term) =>
      match t.raw with
      | .ident .. => erased := erased.insert (← realizeGlobalConstNoOverload t.raw)
      | _ => throwErrorAt t "apply_rulesets only supports removals by name"
    | `(applyRuleSetArg| $t:term) =>
      match t.raw with
      | .ident _ _ val _ =>
        if ← isRuleSetName val then rulesets := rulesets.push val else explicitTerms := explicitTerms.push t
      | _ => explicitTerms := explicitTerms.push t
    | _ => throwUnsupportedSyntax
  withMainContext do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let mut explicitRules := #[]
    for h : i in [:explicitTerms.size] do
      let e ← Term.elabTerm explicitTerms[i].raw none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let origin := explicitOrigin i explicitTerms[i].raw e
      if let some rule ← explicitRuleProcRule? origin e then
        explicitRules := explicitRules.push { rule with order := i }
      else
        explicitRules := explicitRules.push (← mkExplicitExprRule origin i e)
    let ctx : Context := { config := cfg, rulesets, explicitRules, erased }
    let (proof?, _) ← (applyRuleSets { ruleName := Name.anonymous } goalType).run ctx |>.run {}
    match proof? with
    | some proof => goal.assign proof; replaceMainGoal []
    | none => throwError "apply_rulesets failed"

end NumLean.Tactic.ApplyRuleSets
