module

public import Lean.Elab.Deriving.Util
public import Mathlib.Tactic.ProxyType
public meta import Mathlib.Tactic.ProxyType
public meta import NumLean.Meta.ExposedProxyType
public import NumLean.Interfaces.HasFlatRepr.Equiv
public import NumLean.Interfaces.HasFlatRepr.Sigma

@[expose] public section

syntax (name := deriveHasFlatReprCmd) "#derive_has_flat_repr " ident : command

namespace NumLean

open Lean Elab Command Term Meta

namespace HasFlatRepr

instance instUnit {K : Type v} {Ks : Nat → Type w} [VectorType Ks K] : HasFlatRepr Unit Ks 0 where
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
  get _ _ _ := ()
  getComp_get_eq_vector_get := by intro _ _ _ i _ hi; omega
  set ks _ _ _ := ks
  vector_get_set_eq := by intro _ _ _ _ _ _ hi; omega
  vector_get_set_ne := by intro _ _ _ _ _ _ _ hi'; rfl
  push {n} ks _ := by
    simpa using ks
  vector_get_push_lt := by
    intro n ks _ i hi
    rfl
  vector_get_push_eq := by intro _ _ _ i hi; omega
  toFlatVector _ := VectorType.emptyWithCapacity (As := Ks) 0
  get_toFlatVector_eq_getComp := by intro _ i hi; omega
  replicate _ _ := VectorType.emptyWithCapacity (As := Ks) 0
  get_replicate := by intro _ _ _ j _ hj; omega

namespace Deriving

open Lean.Elab.Deriving

meta def checkSupported (indVal : InductiveVal) : CommandElabM Unit := do
  if indVal.isRec then
    throwError "deriving HasFlatRepr only supports non-recursive structures"
  if indVal.numIndices != 0 then
    throwError "deriving HasFlatRepr only supports types without indices"
  if indVal.numCtors != 1 then
    throwError "deriving HasFlatRepr only supports structures/single-constructor inductives"

meta def typeParamIndices (indVal : InductiveVal) : TermElabM (Array Nat) := do
  forallBoundedTelescope indVal.type indVal.numParams fun xs _ => do
    let mut indices := #[]
    for h : i in *...xs.size do
      if (← whnf (← inferType xs[i])).isSort then
        indices := indices.push i
    return indices

meta def ctorFieldTypesForParams
    (indVal : InductiveVal) (params : Array Expr) : TermElabM (Array Expr) := do
  let ctorInfo ← getConstInfoCtor indVal.ctors[0]!
  let ctorType ← inferType <|
    mkAppN (mkConst ctorInfo.name (indVal.levelParams.map Level.param)) params
  forallBoundedTelescope ctorType ctorInfo.numFields fun xs _ => do
    xs.mapM fun x => inferType x

meta def findSubst? (subst : Array (FVarId × Term)) (id : FVarId) : Option Term := Id.run do
  for (id', stx) in subst do
    if id == id' then
      return some stx
  return none

meta partial def natExprToSyntax (subst : Array (FVarId × Term)) (e : Expr) : TermElabM Term := do
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

meta def sumNatExprList : List Expr → MetaM Expr
  | [] => pure (mkRawNatLit 0)
  | [n] => pure n
  | n :: ns => do
      let rest ← sumNatExprList ns
      mkAppM ``Nat.add #[n, rest]

meta def sumNatExprs (ns : Array Expr) : MetaM Expr :=
  if ns.all (·.rawNatLit?.isSome) then
    pure <| mkRawNatLit <| ns.foldl (fun acc n => acc + n.rawNatLit?.get!) 0
  else
    sumNatExprList ns.toList

meta def mkHasFlatReprType (x ks n k : Expr) : TermElabM Expr := do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let w ← mkFreshLevelMVar
  let vectorTypeInst ← synthInstance (← mkAppM ``VectorType #[ks, k])
  return mkAppN (mkConst ``HasFlatRepr [u, v, w]) #[x, ks, n, k, vectorTypeInst]

meta def mkHasFlatReprLength (x ks k : Expr) : TermElabM Expr := do
  let n ← mkFreshExprMVar (some (mkConst ``Nat))
  let instType ← mkHasFlatReprType x ks n k
  let inst ← synthInstance instType
  let instType ← whnf (← inferType inst)
  if instType.isAppOfArity ``HasFlatRepr 5 then
    let n := instType.getAppArgs[2]!
    if !(← instantiateMVars n).hasExprMVar then
      return n
  instantiateMVars n

meta def mkConcreteHasFlatReprLength (x k : Expr) : TermElabM Expr := do
  let ks ← mkAppM ``Vector #[k]
  let same ← isDefEq x k
  if same then
    return mkRawNatLit 1
  for i in [0:257] do
    try
      let n := mkRawNatLit i
      let instType ← mkHasFlatReprType x ks n k
      discard <| synthInstance instType
      return n
    catch _ => pure ()
  let n ← mkHasFlatReprLength x ks k
  if !(← instantiateMVars n).hasExprMVar then
    return n
  throwError "could not infer concrete HasFlatRepr length for{indentExpr x}"

meta def mkFieldLengthSum (fieldTypes : Array Expr) (ks k : Expr) : TermElabM Expr := do
  let ns ← fieldTypes.mapM fun fieldType => mkHasFlatReprLength fieldType ks k
  sumNatExprs ns

meta def mkFieldLengthSumWithBase
    (fieldTypes : Array Expr) (base baseN ks k : Expr) : TermElabM Expr := do
  let ns ← fieldTypes.mapM fun fieldType => do
    if ← isDefEq fieldType base then
      return baseN
    else
      mkHasFlatReprLength fieldType ks k
  sumNatExprs ns

meta def mkConcreteFieldLengthSum (fieldTypes : Array Expr) (k : Expr) : TermElabM Expr := do
  let ns ← fieldTypes.mapM fun fieldType => mkConcreteHasFlatReprLength fieldType k
  sumNatExprs ns

meta def scalarCandidates : Array Name :=
  #[`Float, `Float32, `UInt8, `Real]

meta def chooseConcreteScalarAndLength
    (indVal : InductiveVal) (argNames : Array Name) : TermElabM (Term × Term × Term) := do
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
          return (kStx, ← `(Vector $kStx), ← natExprToSyntax subst n)
        catch _ => pure ()
    throwError "deriving HasFlatRepr could not synthesize field representations \
      for any candidate scalar"

meta def mkHasFlatReprInstanceNoTypeParam (indVal : InductiveVal) : TermElabM Command := do
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let indType ← mkInductiveApp indVal argNames
  let (_k, ks, n) ← chooseConcreteScalarAndLength indVal argNames
  `(command|
    instance $binders:implicitBinder*
        : $(mkCIdent ``HasFlatRepr) $indType $ks $n :=
      $(mkCIdent ``HasFlatRepr.ofEquiv) $ks (proxy_equiv% $indType))

meta def mkHasFlatReprInstanceOneTypeParam
    (indVal : InductiveVal) (typeParamIdx : Nat) : TermElabM Command := do
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let xName := argNames[typeParamIdx]!
  if xName.eraseMacroScopes != `X then
    throwError "deriving HasFlatRepr expects the single type parameter to be named `X`"
  let ksName ← mkFreshUserName `Ks
  let kName ← mkFreshUserName `K
  let nName ← mkFreshUserName `n
  let indType ← mkInductiveApp indVal argNames
  let n ← forallBoundedTelescope indVal.type indVal.numParams fun params _ => do
    let ksTypeStx : Term ← `(Nat → Type)
    let ksType ← elabType ksTypeStx
    withLocalDeclD ksName ksType fun ks => do
      withLocalDeclD kName (mkSort Level.one) fun k => do
        withLocalDeclD nName (mkConst ``Nat) fun nX => do
          let x := params[typeParamIdx]!
          let fieldTypes ← ctorFieldTypesForParams indVal params
          let mut subst ← params.mapIdxM fun i param => do
            let stx : Term := mkIdent argNames[i]!
            return (param.fvarId!, stx)
          let nXStx : Term := mkIdent nName
          subst := subst.push (nX.fvarId!, nXStx)
          if ← fieldTypes.allM fun fieldType => isDefEq fieldType x then
            let n ← sumNatExprs (fieldTypes.map fun _ => nX)
            natExprToSyntax subst n
          else
            let vectorTypeInst ← mkAppM ``VectorType #[ks, k]
            withLocalDeclD `instVectorType vectorTypeInst fun instVectorType => do
              let instVectorTypeDecl ← instVectorType.fvarId!.getDecl
              let instType ← mkHasFlatReprType x ks nX k
              withLocalDeclD `inst instType fun inst => do
                let instDecl ← inst.fvarId!.getDecl
                let n ← withLocalInstances [instVectorTypeDecl, instDecl] <|
                  mkFieldLengthSumWithBase fieldTypes x nX ks k
                natExprToSyntax subst n
  `(command|
    instance $binders:implicitBinder*
        {$(mkIdent ksName):ident : Nat → Type} {$(mkIdent kName):ident : Type} {$(mkIdent nName):ident : Nat}
        [$(mkCIdent ``VectorType) $(mkIdent ksName) $(mkIdent kName)]
        [$(mkCIdent ``HasFlatRepr) $(mkIdent xName) $(mkIdent ksName) $(mkIdent nName) (K := $(mkIdent kName))]
        : $(mkCIdent ``HasFlatRepr) $indType $(mkIdent ksName) $n (K := $(mkIdent kName)) :=
      $(mkCIdent ``HasFlatRepr.ofEquiv) $(mkIdent ksName) (proxy_equiv% $indType))

meta def mkHasFlatReprInstance (typeName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct typeName
  checkSupported indVal
  liftTermElabM <|
    NumLean.Meta.ExposedProxyType.ensureProxyEquivExposed
      (Mathlib.ProxyType.ProxyEquivConfig.default indVal) indVal
  let cmd ← liftTermElabM do
    let typeParams ← typeParamIndices indVal
    if h : typeParams.size = 0 then
      mkHasFlatReprInstanceNoTypeParam indVal
    else if h : typeParams.size = 1 then
      mkHasFlatReprInstanceOneTypeParam indVal typeParams[0]
    else
      throwError "deriving HasFlatRepr supports at most one type parameter"
  trace[Elab.Deriving.HasFlatRepr] "instance command:\n{cmd}"
  elabCommand cmd

meta def hasFlatReprDerivingHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  mkHasFlatReprInstance declNames[0]!
  return true

meta initialize
  registerDerivingHandler ``HasFlatRepr hasFlatReprDerivingHandler
  registerTraceClass `Elab.Deriving.HasFlatRepr

@[command_elab deriveHasFlatReprCmd]
meta def elabDeriveHasFlatRepr : CommandElab := fun stx => do
  let `(command| #derive_has_flat_repr $id:ident) := stx | throwUnsupportedSyntax
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  mkHasFlatReprInstance declName

end Deriving
end HasFlatRepr
end NumLean
