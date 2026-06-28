module

public import Lean.Elab.Tactic.Config
public import Lean.Meta.Tactic.SolveByElim

@[expose] public section

namespace NumLean.Tactic.ApplyRuleSets

open Lean Meta

initialize registerTraceClass `Meta.Tactic.apply_rulesets

initialize registerTraceClass `Meta.Tactic.apply_rulesets.attr

structure Config extends ApplyConfig where
  maxDepth : Nat := 50
  maxSteps : Nat := 10000
  transparency : TransparencyMode := .reducible
  assumption : Bool := true
  intro : Bool := true

instance : Inhabited Config := ⟨{}⟩

structure ArgOrigin where
  ruleName : Name
  argIndex : Option Nat := none
  argName : Option Name := none
deriving Inhabited, BEq

inductive Origin where
  | decl (declName : Name)
  | fvar (fvarId : FVarId)
  | stx (id : Name) (ref : Syntax)
  | other (name : Name)
deriving Inhabited, Repr

def Origin.name : Origin -> Name
  | .decl declName => declName
  | .fvar fvarId => fvarId.name
  | .stx id _ => id
  | .other name => name

inductive RuleType where
  | expr (proof : Expr)
  | proc (proc : Expr)
deriving Inhabited

structure Rule where
  origin : Origin
  type : RuleType
  pattern : Expr
  levelParams : Array Name := #[]
  priority : Nat := eval_prio default
  order : Nat := 0
deriving Inhabited

def Rule.name (rule : Rule) : Name :=
  rule.origin.name

def exprLevelParams (e : Expr) : Array Name :=
  (Lean.collectLevelParams {} e).params

def Rule.allLevelParams (rule : Rule) : Array Name :=
  let params := rule.levelParams ++ exprLevelParams rule.pattern
  match rule.type with
  | .expr proof => params ++ (exprLevelParams proof).filter (!params.contains ·)
  | .proc proc => params ++ (exprLevelParams proc).filter (!params.contains ·)

def Rule.hasExprMVar (rule : Rule) : Bool :=
  rule.pattern.hasExprMVar ||
    match rule.type with
    | .expr proof => proof.hasExprMVar
    | .proc proc => proc.hasExprMVar

structure State where
  numSteps : Nat := 0
  depth : Nat := 0

structure Context where
  config : Config := {}
  rulesets : Array Name := #[]
  explicitRules : Array Rule := #[]
  erased : Std.HashSet Name := {}

abbrev ApplyRuleSetsM := ReaderT Context <| StateT State MetaM

structure RuleSet where
  entries : Array Rule := #[]
deriving Inhabited

structure RuleSets where
  ruleSets : Std.HashMap Name RuleSet := {}
  nextOrder : Nat := 0
deriving Inhabited

structure RuleSetExtEntry where
  ruleSetName : Name
  rule : Rule
deriving Inhabited

end NumLean.Tactic.ApplyRuleSets
