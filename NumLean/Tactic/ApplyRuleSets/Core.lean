module

public import NumLean.Tactic.ApplyRuleSets.Attr
public meta import NumLean.Tactic.ApplyRuleSets.Attr

@[expose] public section

namespace NumLean.Tactic.ApplyRuleSets

open Lean Meta

meta def checkStep : ApplyRuleSetsM Unit := do
  let n := (← get).numSteps
  if n >= (← read).config.maxSteps then
    throwError "apply_rulesets failed, maximum number of steps exceeded"
  modify fun s => { s with numSteps := n + 1 }

meta def withIncreasedSearchDepth {α} (x : ApplyRuleSetsM α) : ApplyRuleSetsM α := do
  let depth := (← get).depth
  modify fun s => { s with depth := depth + 1 }
  try
    let a ← x
    modify fun s => { s with depth := depth }
    return a
  catch e =>
    modify fun s => { s with depth := depth }
    throw e

meta def sortRules (rules : Array Rule) : Array Rule :=
  rules.qsort fun a b =>
    if a.priority != b.priority then a.priority > b.priority else a.order < b.order

meta def Rule.instantiate (rule : Rule) : MetaM (RuleType × Expr) := do
  let levelParams := rule.allLevelParams
  let us ← levelParams.mapM fun _ => mkFreshLevelMVar
  let pattern := rule.pattern.instantiateLevelParamsArray levelParams us
  let type := match rule.type with
    | .expr proof => .expr (proof.instantiateLevelParamsArray levelParams us)
    | .proc proc => .proc (proc.instantiateLevelParamsArray levelParams us)
  return (type, pattern)

mutual

meta partial def applyRuleSets (origin : ArgOrigin) (goalType : Expr) : ApplyRuleSetsM (Option Expr) :=
  applyRuleSetsCoreSearch origin goalType

meta partial def applyRuleSetsCoreSearch (origin : ArgOrigin) (goalType : Expr) : ApplyRuleSetsM (Option Expr) := do
  checkStep
  if (← get).depth > (← read).config.maxDepth then
    return none
  if (← read).config.assumption then
    if let some prf ← assumption? goalType then
      return some prf
  if (← read).config.intro then
    let some proof ← forallTelescopeReducing goalType fun xs body => do
      if xs.isEmpty then
        return none
      let some proof ← withIncreasedSearchDepth <| applyRuleSetsCoreSearch origin body | return none
      return some (← mkLambdaFVars xs proof)
      | pure ()
    return some proof
  let mut rules := #[]
  for rsName in (← read).rulesets do
    rules := rules ++ (← getRuleSet rsName).entries
  rules := sortRules rules
  for rule in (← read).explicitRules do
    if let some proof ← tryRule? origin rule goalType then
      return some proof
  for rule in rules do
    unless (← read).erased.contains rule.name do
      if let some proof ← tryRule? origin rule goalType then
        return some proof
  return none

meta partial def assumption? (goalType : Expr) : ApplyRuleSetsM (Option Expr) := do
  unless ← isProp goalType do
    return none
  for localDecl in ← getLCtx do
    unless localDecl.isAuxDecl do
      if ← isProp localDecl.type then
        if ← withTransparency (← read).config.transparency <| isDefEq localDecl.type goalType then
          return some (mkFVar localDecl.fvarId)
  return none

meta partial def synthesizeArgs (ruleName : Name) (args : Array Expr) : ApplyRuleSetsM Bool := do
  let mut ok := true
  for h : i in [:args.size] do
    let arg ← instantiateMVars args[i]
    if arg.isMVar then
      let type ← inferType arg
      if (← isClass? type).isSome then
        if let .some inst ← trySynthInstance type then
          if ← isDefEq arg inst then
            continue
      if ← isProp type then
        let origin := { ruleName, argIndex := some i }
        if let some proof ← withIncreasedSearchDepth <| applyRuleSetsCoreSearch origin type then
          if ← isDefEq arg proof then
            continue
        ok := false
  return ok

meta partial def tryRule? (origin : ArgOrigin) (rule : Rule) (goalType : Expr) : ApplyRuleSetsM (Option Expr) := do
  if rule.hasExprMVar then
    return none
  let (ruleType, pattern) ← rule.instantiate
  let (args, _, conclusion) ← forallMetaTelescope pattern
  unless ← withTransparency (← read).config.transparency <| isDefEq conclusion goalType do
    return none
  match ruleType with
  | .expr expr =>
    unless ← synthesizeArgs rule.name args do
      return none
    let proof ← instantiateMVars (mkAppN expr args)
    if proof.hasExprMVar then return none
    return some proof
  | .proc procExpr =>
    unless ← synthesizeArgs rule.name args do
      return none
    let args ← args.mapM instantiateMVars
    let proc ← evalRuleProc procExpr
    proc args origin goalType

end

end NumLean.Tactic.ApplyRuleSets
