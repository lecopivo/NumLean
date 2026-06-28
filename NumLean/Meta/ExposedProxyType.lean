module

public meta import Mathlib.Tactic.ProxyType

@[expose] public meta section

namespace NumLean.Meta.ExposedProxyType

open Lean Elab Lean.Parser.Term

open Meta Command


def addAndCompileExposed (decl : Declaration) : CoreM Unit := do
  addDecl decl (forceExpose := true)
  compileDecl decl

partial def unpackProxyFields (fieldTypes : Array Expr) (proxy : Expr) : TermElabM (Array Expr) := do
  if h : fieldTypes.size = 0 then
    return #[]
  else if h : fieldTypes.size = 1 then
    let fieldType := fieldTypes[0]
    if ← isProp fieldType then
      return #[← mkAppM ``PLift.down #[proxy]]
    else
      return #[proxy]
  else
    let fieldType := fieldTypes[0]
    let fst ← mkAppM ``Sigma.fst #[proxy]
    let snd ← mkAppM ``Sigma.snd #[proxy]
    let field ← if ← isProp fieldType then
      mkAppM ``PLift.down #[fst]
    else
      pure fst
    return (#[field] ++ (← unpackProxyFields fieldTypes[1:] snd))

partial def packProxyFields (expectedType : Expr) (fieldTypes fields : Array Expr) : TermElabM Expr := do
  if fields.isEmpty then
    return mkConst ``Unit.unit
  else if fields.size = 1 then
    if ← isProp fieldTypes[0]! then
      mkAppM ``PLift.up #[fields[0]!]
    else
      return fields[0]!
  else
    let first ← if ← isProp fieldTypes[0]! then
      mkAppM ``PLift.up #[fields[0]!]
    else
      pure fields[0]!
    let expectedType ← whnf expectedType
    unless expectedType.isAppOfArity ``Sigma 2 do
      throwError "expected proxy type to be a Sigma expression{indentExpr expectedType}"
    let args := expectedType.getAppArgs
    let beta := args[1]!
    let restExpected := mkApp beta first
    let rest ← packProxyFields restExpected fieldTypes[1:] fields[1:]
    mkAppOptM ``Sigma.mk #[some args[0]!, some beta, some first, some rest]

def mkSingleCtorStructureEquiv?
    (indVal : InductiveVal) (params : Array Expr) (ctype equivType : Expr) : TermElabM (Option Expr) := do
  let some structInfo := getStructureInfo? (← getEnv) indVal.name | return none
  let ctorName := indVal.ctors[0]!
  let ctorInfo ← getConstInfoCtor ctorName
  let levels := indVal.levelParams.map Level.param
  let ctorType ← inferType <| mkAppN (mkConst ctorName levels) params
  forallBoundedTelescope ctorType ctorInfo.numFields fun xs _ => do
    let fieldTypes ← xs.mapM fun x => inferType x
    if fieldTypes.size != structInfo.fieldNames.size then
      return none
    let mut projFns := #[]
    for i in [0:fieldTypes.size] do
      let some projFn := structInfo.getProjFn? i | return none
      projFns := projFns.push projFn
    let indType := mkAppN (mkConst indVal.name levels) params
    let toFun ← withLocalDeclD `p ctype fun p => do
      let fields ← unpackProxyFields fieldTypes p
      mkLambdaFVars #[p] <| mkAppN (mkConst ctorName levels) (params ++ fields)
    let invFun ← withLocalDeclD `x indType fun x => do
      let mut fields := #[]
      for projFn in projFns do
        fields := fields.push (← mkAppM projFn #[x])
      mkLambdaFVars #[x] (← packProxyFields ctype fieldTypes fields)
    let rightInv ← withLocalDeclD `x indType fun x => do
      mkLambdaFVars #[x] (← mkEqRefl x)
    let leftInv ← withLocalDeclD `p ctype fun p => do
      mkLambdaFVars #[p] (← mkEqRefl p)
    let equivBody ← `(term| { toFun := $(← Term.exprToSyntax toFun),
                              invFun := $(← Term.exprToSyntax invFun),
                              right_inv := $(← Term.exprToSyntax rightInv)
                              left_inv := $(← Term.exprToSyntax leftInv) })
    return some (← Term.elabTerm equivBody equivType)

/--
Like `Mathlib.ProxyType.ensureProxyEquiv`, but force-exposes the generated declarations under the
module system so same-file reductions can inspect their bodies.
-/
def ensureProxyEquivExposed
    (config : Mathlib.ProxyType.ProxyEquivConfig) (indVal : InductiveVal) : TermElabM Unit := do
  if indVal.isRec then
    throwError
      "proxy equivalence: recursive inductive types are not supported (and are usually infinite)"
  if 0 < indVal.numIndices then
    throwError "proxy equivalence: inductive indices are not supported"

  let levels := indVal.levelParams.map Level.param
  forallBoundedTelescope indVal.type indVal.numParams fun params _sort => do
    let mut cdata := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let ctorType ← inferType <| mkAppN (mkConst ctorName levels) params
      cdata := cdata.push <| ←
        forallBoundedTelescope ctorType ctorInfo.numFields fun xs _itype => do
          let names ← xs.mapM (fun _ => mkFreshUserName `a)
          let (ty, ppatt) ← config.mkCtorProxyType (xs.zip names).toList
          let places := .replicate ctorInfo.numParams (← `(term| _))
          let argNames := names.map mkIdent
          let cpatt ← `(term| @$(mkIdent ctorName) $places* $argNames*)
          return (ctorName, ty, ppatt, cpatt)
    let (ctype, ppatts, pf) ← config.mkProxyType <|
      cdata.map (fun (ctorName, ty, ppatt, _) => (ctorName, ty, ppatt))
    let mut toFunAlts := #[]
    let mut invFunAlts := #[]
    for ppatt in ppatts, (_, _, _, cpatt) in cdata do
      toFunAlts := toFunAlts.push <| ← `(matchAltExpr| | $ppatt => $cpatt)
      invFunAlts := invFunAlts.push <| ← `(matchAltExpr| | $cpatt => $ppatt)

    trace[Elab.ProxyType] "proxy type: {ctype}"
    let ctype' ← mkLambdaFVars params ctype
    if let some const := (← getEnv).find? config.proxyName then
      unless ← isDefEq const.value! ctype' do
        throwError "Declaration {config.proxyName} already exists and it is not the proxy type."
      trace[Elab.ProxyType] "proxy type already exists"
    else
      addAndCompileExposed <| Declaration.defnDecl
        { name := config.proxyName
          levelParams := indVal.levelParams
          safety := DefinitionSafety.safe
          hints := ReducibilityHints.abbrev
          type := ← inferType ctype'
          value := ctype' }
      setReducibleAttribute config.proxyName
      setProtected config.proxyName
      addDocStringCore config.proxyName s!"A \"proxy type\" equivalent to `{indVal.name}` that is \
        constructed from `Unit`, `PLift`, `Sigma`, `Empty`, and `Sum`. \
        See `{config.proxyEquivName}` for the equivalence. \
        (Generated by the `proxy_equiv%` elaborator.)"
      trace[Elab.ProxyType] "defined {config.proxyName}"

    let equivType ← mkAppM ``Equiv #[ctype, mkAppN (mkConst indVal.name levels) params]
    if let some const := (← getEnv).find? config.proxyEquivName then
      unless ← isDefEq const.type (← mkForallFVars params equivType) do
        throwError "Declaration {config.proxyEquivName} already exists and has the wrong type."
      trace[Elab.ProxyType] "proxy equivalence already exists"
    else
      trace[Elab.ProxyType] "constructing proxy equivalence"
      let mut toFun ← `(term| fun $toFunAlts:matchAlt*)
      let mut invFun ← `(term| fun $invFunAlts:matchAlt*)
      if indVal.numCtors == 0 then
        toFun ← `(term| fun x => nomatch x)
        invFun ← `(term| fun x => nomatch x)
      let equiv ← if let some equiv ← mkSingleCtorStructureEquiv? indVal params ctype equivType then
        pure equiv
      else
        let equivBody ← `(term| { toFun := $toFun,
                                  invFun := $invFun,
                                  right_inv := by intro x; cases x <;> rfl
                                  left_inv := by intro x; $pf:tactic })
        withExporting <| Term.elabTerm equivBody equivType
      withExporting <| Term.synthesizeSyntheticMVarsNoPostponing
      trace[Elab.ProxyType] "elaborated equivalence{indentExpr equiv}"
      let equiv' ← mkLambdaFVars params (← instantiateMVars equiv)
      addAndCompileExposed <| Declaration.defnDecl
        { name := config.proxyEquivName
          levelParams := indVal.levelParams
          safety := DefinitionSafety.safe
          hints := ReducibilityHints.abbrev
          type := ← inferType equiv'
          value := equiv' }
      setProtected config.proxyEquivName
      addDocStringCore config.proxyEquivName s!"An equivalence between the \"proxy type\" \
        `{config.proxyName}` and `{indVal.name}`. The proxy type is a reducible definition \
        that represents the inductive type using `Unit`, `PLift`, `Sigma`, `Empty`, and `Sum` \
        (and whatever other inductive types appear within the inductive type), and the \
        intended use is to define typeclass instances uses pre-existing instances on these. \
        (Generated by the `proxy_equiv%` elaborator.)"
      trace[Elab.ProxyType] "defined {config.proxyEquivName}"

end NumLean.Meta.ExposedProxyType
