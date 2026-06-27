import Lean.Elab.Deriving.Util
import Mathlib.Tactic.ProxyType
import NumLean.Interfaces.Algebra.Equiv
import NumLean.Data.Sigma
import NumLean.Meta.RewriteBy

namespace NumLean

open Lean Elab Command Term Meta
open Lean.Elab.Deriving

namespace Algebra.Deriving

private def checkSupported (indVal : InductiveVal) : CommandElabM Unit := do
  if indVal.isRec then
    throwError "deriving algebra ops only supports non-recursive structures"
  if indVal.numIndices != 0 then
    throwError "deriving algebra ops only supports types without indices"
  if indVal.numCtors != 1 then
    throwError "deriving algebra ops only supports structures/single-constructor inductives"

private def hasPropField (indVal : InductiveVal) : TermElabM Bool := do
  forallBoundedTelescope indVal.type indVal.numParams fun params _ => do
    let ctorInfo ← getConstInfoCtor indVal.ctors[0]!
    let ctorType ← inferType <|
      mkAppN (mkConst ctorInfo.name (indVal.levelParams.map Level.param)) params
    forallBoundedTelescope ctorType ctorInfo.numFields fun xs _ => do
      xs.anyM fun x => do
        isProp (← inferType x)

private def checkNoPropFields (indVal : InductiveVal) : CommandElabM Unit := do
  if ← liftTermElabM <| hasPropField indVal then
    throwError "deriving algebra ops does not support structures with proof fields"

private def mkInstanceCmd
    (className ofEquivName : Name) (indVal : InductiveVal) : TermElabM Command := do
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let instBinders : Array (TSyntax ``Parser.Term.instBinder) :=
    (← mkInstImplicitBinders className indVal argNames).map fun stx => ⟨stx⟩
  let indType ← mkInductiveApp indVal argNames
  let proxyEquivName := indVal.name.mkStr "proxyTypeEquiv"
  `(command|
    instance $binders:implicitBinder* $instBinders:instBinder* : $(mkCIdent className) $indType :=
      ($(mkCIdent ofEquivName) (proxy_equiv% $indType)) rewrite_by
        dsimp only [$(mkCIdent ofEquivName):ident, $(mkCIdent proxyEquivName):ident,
          Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
        simp only [Sigma.mk_zero_mk, Sigma.mk_one_mk, Sigma.mk_add_mk, Sigma.mk_sub_mk,
          Sigma.neg_mk, Sigma.mk_mul_mk, Sigma.mk_div_mk, Sigma.inv_mk,
          Sigma.nat_smul_mk, Sigma.int_smul_mk, Sigma.mk_npow, Sigma.mk_zpow])

private def mkAddGroupOpsCmds (indVal : InductiveVal) : TermElabM (Array Command) := do
  return #[]
    |>.push (← mkInstanceCmd ``Add ``Add.ofEquiv indVal)
    |>.push (← mkInstanceCmd ``Sub ``Sub.ofEquiv indVal)
    |>.push (← mkInstanceCmd ``Neg ``Neg.ofEquiv indVal)
    |>.push (← mkInstanceCmd ``Zero ``Zero.ofEquiv indVal)
    |>.push (← mkInstanceCmd ``AddGroupOps ``AddGroupOps.ofEquiv indVal)

private def mkGroupOpsCmds (indVal : InductiveVal) : TermElabM (Array Command) := do
  return #[]
    |>.push (← mkInstanceCmd ``Mul ``Mul.ofEquiv indVal)
    |>.push (← mkInstanceCmd ``Div ``Div.ofEquiv indVal)
    |>.push (← mkInstanceCmd ``Inv ``Inv.ofEquiv indVal)
    |>.push (← mkInstanceCmd ``One ``One.ofEquiv indVal)
    |>.push (← mkInstanceCmd ``GroupOps ``GroupOps.ofEquiv indVal)

private def mkOpsInstances
    (typeName : Name) (mkCmds : InductiveVal → TermElabM (Array Command)) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct typeName
  checkSupported indVal
  checkNoPropFields indVal
  liftTermElabM <|
    Mathlib.ProxyType.ensureProxyEquiv (Mathlib.ProxyType.ProxyEquivConfig.default indVal) indVal
  let cmds ← liftTermElabM <| mkCmds indVal
  trace[Elab.Deriving.Algebra] "instance commands:\n{cmds}"
  elabCommand <| mkNullNode cmds

def addGroupOpsDerivingHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  mkOpsInstances declNames[0]! mkAddGroupOpsCmds
  return true

def groupOpsDerivingHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  mkOpsInstances declNames[0]! mkGroupOpsCmds
  return true

initialize
  registerDerivingHandler ``AddGroupOps addGroupOpsDerivingHandler
  registerDerivingHandler ``GroupOps groupOpsDerivingHandler
  registerTraceClass `Elab.Deriving.Algebra

end Algebra.Deriving
end NumLean
