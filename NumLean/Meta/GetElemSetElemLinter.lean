import NumLean.Data.FinHTuple.Basic
import Mathlib.Tactic.DeclarationNames

open Lean Elab Command Meta

namespace NumLean

namespace GetElemSetElemLinter

register_option linter.getElemSetElemLhs : Bool := {
  defValue := true
  descr := "warn when equality theorem left-hand sides use GetElem/SetElem adapter instances"
}

def getTheoremNames (stx : Syntax) : CommandElabM (Array Name) := do
  let ids ← Mathlib.Linter.getNamesFrom (stx.getPos?.getD default)
  let env ← getEnv
  let mut names := #[]
  for id in ids do
    let declName := id.getId
    if let some (.thmInfo _) := env.find? declName then
      names := names.push declName
  return names

def adapterInstanceNames : NameSet :=
  [``HTuple.instGetElemLeafToScalar,
   ``HTuple.instSetElemLeafToScalar,
   `Fin.instGetElemFinVal,
   ``instSetElemFinValOfNat].foldl (init := {}) fun s n => s.insert n

def lhsOfEq? (type : Expr) : MetaM (Option Expr) := do
  forallTelescopeReducing type fun _ body => do
    let body ← whnf body
    if body.isAppOfArity ``Eq 3 then
      return some body.getAppArgs[1]!
    else
      return none

def getElemSetElemLhsLinter : Linter where
  run := fun stx => do
    unless linter.getElemSetElemLhs.get (← getOptions) do
      return
    for declName in ← getTheoremNames stx do
      let some info := (← getEnv).find? declName | continue
      let some lhs ← liftTermElabM <| lhsOfEq? info.type | continue
      if lhs.containsConst (fun n => adapterInstanceNames.contains n) then
        Linter.logLint linter.getElemSetElemLhs stx
          m!"The left-hand side of equality theorem `{declName}` get or set element syntax in non simp-normal form. This likely means that the index is of type `Fin n` or `HTuple ℕ hp(•)`. You can fix it by writting `xs[(i : Nat)]` or `setElem xs (i : Nat) x h`."

initialize addLinter getElemSetElemLhsLinter

end GetElemSetElemLinter
end NumLean
