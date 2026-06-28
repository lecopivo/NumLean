module

public import NumLean.Data.FinHTuple.Basic
public import Mathlib.Tactic.DeclarationNames
public meta import Mathlib.Tactic.DeclarationNames

@[expose] public section

open Lean Elab Command Meta

namespace NumLean

namespace GetElemSetElemLinter

register_option linter.getElemSetElemLhs : Bool := {
  defValue := true
  descr := "warn when equality theorem left-hand sides use GetElem/SetElem adapter instances"
}

meta def getTheoremNames (stx : Syntax) : CommandElabM (Array Name) := do
  let ids ← Mathlib.Linter.getNamesFrom (stx.getPos?.getD default)
  let env ← getEnv
  let mut names := #[]
  for id in ids do
    let declName := id.getId
    if let some (.thmInfo _) := env.find? declName then
      names := names.push declName
  return names

meta def adapterInstanceNames : NameSet :=
  [``HTuple.instGetElemLeafToScalar,
   ``HTuple.instSetElemLeafToScalar,
   `Fin.instGetElemFinVal,
   ``instSetElemFinValOfNat].foldl (init := {}) fun s n => s.insert n

meta def lhsOfEq? (type : Expr) : MetaM (Option Expr) := do
  forallTelescopeReducing type fun _ body => do
    let body ← whnf body
    if body.isAppOfArity ``Eq 3 then
      return some body.getAppArgs[1]!
    else
      return none

meta def getElemSetElemLhsLinter : Linter where
  run := fun stx => do
    unless (← getOptions).getBool `linter.getElemSetElemLhs true do
      return
    for declName in ← getTheoremNames stx do
      let some info := (← getEnv).find? declName | continue
      let some lhs ← liftTermElabM <| lhsOfEq? info.type | continue
      if lhs.containsConst (fun n => adapterInstanceNames.contains n) then
        logWarningAt stx (.tagged `linter.getElemSetElemLhs
          m!"The left-hand side of equality theorem `{declName}` get or set element syntax in non simp-normal form. This likely means that the index is of type `Fin n` or `HTuple ℕ hp(•)`. You can fix it by writting `xs[(i : Nat)]` or `setElem xs (i : Nat) x h`. This linter can be disabled with `set_option linter.getElemSetElemLhs false`")

meta initialize addLinter getElemSetElemLhsLinter

end GetElemSetElemLinter
end NumLean
