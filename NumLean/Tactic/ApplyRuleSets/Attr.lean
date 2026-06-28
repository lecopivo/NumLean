module

public import NumLean.Tactic.ApplyRuleSets.RuleProc
public meta import NumLean.Tactic.ApplyRuleSets.RuleProc

@[expose] public section

namespace NumLean.Tactic.ApplyRuleSets

open Lean Meta Elab

meta initialize ruleSetsExt : SimpleScopedEnvExtension RuleSetExtEntry RuleSets <-
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun s e =>
      let rule := { e.rule with order := s.nextOrder }
      let rs := s.ruleSets.getD e.ruleSetName {}
      let rs := { rs with entries := rs.entries.push rule }
      { ruleSets := s.ruleSets.insert e.ruleSetName rs, nextOrder := s.nextOrder + 1 }
  }

meta def isRuleSetName (name : Name) : CoreM Bool := do
  return (ruleSetsExt.getState (← getEnv)).ruleSets.contains name

meta def getRuleSet (name : Name) : CoreM RuleSet := do
  return (ruleSetsExt.getState (← getEnv)).ruleSets.getD name {}

meta def addTheoremRule (ruleSetName declName : Name) (kind : AttributeKind)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  let info ← getConstInfo declName
  let value := mkConst declName (info.levelParams.map Level.param)
  let rule : Rule := {
    origin := .decl declName
    type := .expr value
    pattern := info.type
    levelParams := info.levelParams.toArray
    priority := prio
  }
  if rule.hasExprMVar then
    throwError "invalid theorem rule `{.ofConstName declName}` contains expression metavariables"
  ruleSetsExt.add { ruleSetName, rule } kind
  trace[Meta.Tactic.apply_rulesets.attr] "added theorem rule {declName} to {ruleSetName}"

meta def addProcRule (ruleSetName declName : Name) (kind : AttributeKind)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  let some decl ← getRuleProcDecl? declName
    | throwError "invalid ruleproc attribute: `{.ofConstName declName}` has no registered pattern"
  let some proc := decl.defaultProc?
    | throwError "invalid ruleproc attribute: `{.ofConstName declName}` has no default proc"
  let rule : Rule := {
    origin := .decl declName
    type := .proc proc
    pattern := decl.pattern
    levelParams := decl.levelParams
    priority := prio
  }
  if rule.hasExprMVar then
    throwError "invalid ruleproc rule `{.ofConstName declName}` contains expression metavariables"
  ruleSetsExt.add { ruleSetName, rule } kind
  trace[Meta.Tactic.apply_rulesets.attr] "added ruleproc {declName} to {ruleSetName}"

meta def registerRuleSetAttr (ruleSetName : Name) (descr : String) : IO Unit := do
  registerBuiltinAttribute {
    name := ruleSetName
    descr := descr
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun decl stx kind => discard <| MetaM.run do
      let prio ← getAttrParamOptPrio stx[1]
      if (← getRuleProcDecl? decl).isSome then
        addProcRule ruleSetName decl kind prio
      else
        addTheoremRule ruleSetName decl kind prio
    erase := fun _ => throwError "can't remove ruleset attributes"
  }

macro (name := registerRulesetCmd) doc:(docComment)? "register_ruleset " id:ident : command => do
  let str := id.getId.toString
  let idParser := mkIdentFrom id (`Parser.Attr ++ id.getId)
  let descr := quote ((doc.map (·.getDocString) |>.getD s!"ruleset {id.getId}").removeLeadingSpaces)
  `($[$doc:docComment]? meta initialize registerRuleSetAttr $(quote id.getId) $descr
    $[$doc:docComment]? syntax (name := $idParser:ident) $(quote str):str (prio)? : attr)

end NumLean.Tactic.ApplyRuleSets
