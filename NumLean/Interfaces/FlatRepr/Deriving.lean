import Lean.Elab.Deriving.Util
import Mathlib.Tactic.ProxyType
import NumLean.Interfaces.FlatRepr.Equiv
import NumLean.Interfaces.FlatRepr.Sigma
import NumLean.Meta.RewriteBy

namespace NumLean

open Lean Elab Command Term Meta

namespace FlatRepr

instance instUnit {K : Type v} : FlatRepr Unit K 0 where
  toVector _ := #v[]
  fromVector _ := ()
  left_inv := by intro x; cases x; rfl
  right_inv := by
    intro x
    ext i hi
    omega
  getComp _ i h := by omega
  getComp_spec := by intro _ i h; omega
  setComp _ i _ h := by omega
  setComp_spec := by intro _ i _ h; omega

namespace Deriving

open Lean.Elab.Deriving

private def checkSupported (indVal : InductiveVal) : CommandElabM Unit := do
  if indVal.isRec then
    throwError "deriving FlatRepr only supports non-recursive structures"
  if indVal.numIndices != 0 then
    throwError "deriving FlatRepr only supports types without indices"
  if indVal.numCtors != 1 then
    throwError "deriving FlatRepr only supports structures/single-constructor inductives"

private def typeParamIndices (indVal : InductiveVal) : TermElabM (Array Nat) := do
  forallBoundedTelescope indVal.type indVal.numParams fun xs _ => do
    let mut indices := #[]
    for h : i in *...xs.size do
      if (← whnf (← inferType xs[i])).isSort then
        indices := indices.push i
    return indices

private def ctorFieldTypesForParams
    (indVal : InductiveVal) (params : Array Expr) : TermElabM (Array Expr) := do
  let ctorInfo ← getConstInfoCtor indVal.ctors[0]!
  let ctorType ← inferType <|
    mkAppN (mkConst ctorInfo.name (indVal.levelParams.map Level.param)) params
  forallBoundedTelescope ctorType ctorInfo.numFields fun xs _ => do
    xs.mapM fun x => inferType x

private def findSubst? (subst : Array (FVarId × Term)) (id : FVarId) : Option Term := Id.run do
  for (id', stx) in subst do
    if id == id' then
      return some stx
  return none

partial def natExprToSyntax (subst : Array (FVarId × Term)) (e : Expr) : TermElabM Term := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``Nat.add 2 then
    let args := e.getAppArgs
    let a ← natExprToSyntax subst args[0]!
    let b ← natExprToSyntax subst args[1]!
    return ← `($a + $b)
  if e.getAppFn.constName? == some ``HAdd.hAdd then
    let args := e.getAppArgs
    if args.size >= 2 then
      let a ← natExprToSyntax subst args[args.size - 2]!
      let b ← natExprToSyntax subst args[args.size - 1]!
      return ← `($a + $b)
  match e with
  | .fvar id =>
      if let some stx := findSubst? subst id then
        return stx
      else
        exprToSyntax e
  | .lit (.natVal n) => `($(quote n))
  | _ => exprToSyntax e

private def sumNatExprList : List Expr → MetaM Expr
  | [] => pure (mkRawNatLit 0)
  | [n] => pure n
  | n :: ns => do
      let rest ← sumNatExprList ns
      mkAppM ``Nat.add #[n, rest]

private def sumNatExprs (ns : Array Expr) : MetaM Expr :=
  if ns.all (·.rawNatLit?.isSome) then
    pure <| mkRawNatLit <| ns.foldl (fun acc n => acc + n.rawNatLit?.get!) 0
  else
    sumNatExprList ns.toList

private def mkFlatReprLength (x k : Expr) : TermElabM Expr := do
  let n ← mkFreshExprMVar (some (mkConst ``Nat))
  let instType ← mkAppM ``FlatRepr #[x, k, n]
  let inst ← synthInstance instType
  let instType ← whnf (← inferType inst)
  if instType.isAppOfArity ``FlatRepr 3 then
    let n := instType.getAppArgs[2]!
    if !(← instantiateMVars n).hasExprMVar then
      return n
  instantiateMVars n

private def mkConcreteFlatReprLength (x k : Expr) : TermElabM Expr := do
  let same ← isDefEq x k
  if same then
    return mkRawNatLit 1
  for i in [0:257] do
    try
      let n := mkRawNatLit i
      let instType ← mkAppM ``FlatRepr #[x, k, n]
      discard <| synthInstance instType
      return n
    catch _ => pure ()
  let n ← mkFlatReprLength x k
  if !(← instantiateMVars n).hasExprMVar then
    return n
  throwError "could not infer concrete FlatRepr length for{indentExpr x}"

private def mkFieldLengthSum (fieldTypes : Array Expr) (k : Expr) : TermElabM Expr := do
  let ns ← fieldTypes.mapM fun fieldType => mkFlatReprLength fieldType k
  sumNatExprs ns

private def mkConcreteFieldLengthSum (fieldTypes : Array Expr) (k : Expr) : TermElabM Expr := do
  let ns ← fieldTypes.mapM fun fieldType => mkConcreteFlatReprLength fieldType k
  sumNatExprs ns

private def scalarCandidates : Array Name :=
  #[`Float, `Float32, `UInt8, `Real]

private def chooseConcreteScalarAndLength
    (indVal : InductiveVal) (argNames : Array Name) : TermElabM (Term × Term) := do
  forallBoundedTelescope indVal.type indVal.numParams fun params _ => do
    let fieldTypes ← ctorFieldTypesForParams indVal params
    let subst ← params.mapIdxM fun i param => do
      let stx : Term := mkIdent argNames[i]!
      return (param.fvarId!, stx)
    let env ← getEnv
    for scalarName in scalarCandidates do
      if env.contains scalarName then
        try
          let k := Lean.mkConst scalarName
          let n ← mkConcreteFieldLengthSum fieldTypes k
          let kStx ← `($(mkCIdent scalarName):ident)
          return (kStx, ← natExprToSyntax subst n)
        catch _ => pure ()
    throwError "deriving FlatRepr could not synthesize field representations \
      for any candidate scalar"

private def mkFlatReprInstanceNoTypeParam (indVal : InductiveVal) : TermElabM Command := do
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let indType ← mkInductiveApp indVal argNames
  let (k, n) ← chooseConcreteScalarAndLength indVal argNames
  let proxyEquivName := indVal.name.mkStr "proxyTypeEquiv"
  `(command|
    instance $binders:implicitBinder*
        : $(mkCIdent ``FlatRepr) $indType $k $n :=
      ($(mkCIdent ``FlatRepr.ofEquiv) $k (proxy_equiv% $indType)) rewrite_by
        dsimp only [$(mkCIdent ``FlatRepr.ofEquiv):ident, $(mkCIdent proxyEquivName):ident,
          Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk])

private def mkFlatReprInstanceOneTypeParam
    (indVal : InductiveVal) (typeParamIdx : Nat) : TermElabM Command := do
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let xName := argNames[typeParamIdx]!
  if xName.eraseMacroScopes != `X then
    throwError "deriving FlatRepr expects the single type parameter to be named `X`"
  let kName ← mkFreshUserName `K
  let nName ← mkFreshUserName `n
  let indType ← mkInductiveApp indVal argNames
  let proxyEquivName := indVal.name.mkStr "proxyTypeEquiv"
  let n ← forallBoundedTelescope indVal.type indVal.numParams fun params _ => do
    withLocalDeclD kName (mkSort levelOne) fun k => do
      withLocalDeclD nName (mkConst ``Nat) fun nX => do
        let x := params[typeParamIdx]!
        let instType ← mkAppM ``FlatRepr #[x, k, nX]
        withLocalDeclD `inst instType fun inst => do
          let instDecl ← inst.fvarId!.getDecl
          let fieldTypes ← ctorFieldTypesForParams indVal params
          let mut subst ← params.mapIdxM fun i param => do
            let stx : Term := mkIdent argNames[i]!
            return (param.fvarId!, stx)
          let nXStx : Term := mkIdent nName
          subst := subst.push (nX.fvarId!, nXStx)
          let n ← withLocalInstances [instDecl] <| mkFieldLengthSum fieldTypes k
          natExprToSyntax subst n
  `(command|
    instance $binders:implicitBinder*
        {$(mkIdent kName):ident : Type} {$(mkIdent nName):ident : Nat}
        [$(mkCIdent ``FlatRepr) $(mkIdent xName) $(mkIdent kName) $(mkIdent nName)]
        : $(mkCIdent ``FlatRepr) $indType $(mkIdent kName) $n :=
      ($(mkCIdent ``FlatRepr.ofEquiv) $(mkIdent kName) (proxy_equiv% $indType)) rewrite_by
        dsimp only [$(mkCIdent ``FlatRepr.ofEquiv):ident, $(mkCIdent proxyEquivName):ident,
          Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk])

private def mkFlatReprInstance (typeName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct typeName
  checkSupported indVal
  liftTermElabM <|
    Mathlib.ProxyType.ensureProxyEquiv (Mathlib.ProxyType.ProxyEquivConfig.default indVal) indVal
  let cmd ← liftTermElabM do
    let typeParams ← typeParamIndices indVal
    if h : typeParams.size = 0 then
      mkFlatReprInstanceNoTypeParam indVal
    else if h : typeParams.size = 1 then
      mkFlatReprInstanceOneTypeParam indVal typeParams[0]
    else
      throwError "deriving FlatRepr supports at most one type parameter"
  trace[Elab.Deriving.FlatRepr] "instance command:\n{cmd}"
  elabCommand cmd

def flatReprDerivingHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  mkFlatReprInstance declNames[0]!
  return true

initialize
  registerDerivingHandler ``FlatRepr flatReprDerivingHandler
  registerTraceClass `Elab.Deriving.FlatRepr

end Deriving
end FlatRepr
end NumLean
