import NumLean.Meta.ForAll.Basic
import Lean.Elab.BuiltinDo.Basic
import Lean.Parser.Do

public section

namespace NumLean
namespace Meta.ForAll

open Lean Lean.Elab Lean.Elab.Do Lean.Meta Lean.Parser.Term

private def mkMProdMkN (es : Array Expr) (u : Level) : MetaM (Expr × Expr) := do
  if h : es.size > 0 then
    let mut tuple := es.back
    let mut tupleTy ← inferType tuple
    let mut es := es.pop
    for _ in 0...es.size do
      let e := es.back!
      let ty ← inferType e
      tuple := mkApp4 (mkConst ``MProd.mk [u]) ty tupleTy e tuple
      tupleTy := mkApp2 (mkConst ``MProd [u]) ty tupleTy
      es := es.pop
    return (tuple, tupleTy)
  else
    return (mkConst ``PUnit.unit [mkLevelSucc u], mkConst ``PUnit [mkLevelSucc u])

private def getMProdFields (tuple tupleTy : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  let tupleTy ← instantiateMVarsIfMVarApp tupleTy
  let_expr c@MProd fstTy sndTy := tupleTy
    | throwError "Internal error: Expected MProd, got {tuple} of type {tupleTy}"
  let fst := mkApp3 (mkConst ``MProd.fst c.constLevels!) fstTy sndTy tuple
  let snd := mkApp3 (mkConst ``MProd.snd c.constLevels!) fstTy sndTy tuple
  return (fst, fstTy, snd, sndTy)

private def bindMutVarsFromMProd (vars : List Name) (tupleVar : FVarId) (k : DoElabM Expr) : DoElabM Expr :=
  do go vars tupleVar (← tupleVar.getType) #[]
where
  go vars tupleVar tupleTy letFVars := do
    let tuple := mkFVar tupleVar
    match vars with
    | [] => mkLetFVars letFVars (← k)
    | [x] =>
        withLetDecl x tupleTy tuple fun x => do mkLetFVars (letFVars.push x) (← k)
    | x :: xs => do
        let (fst, fstTy, snd, sndTy) ← getMProdFields tuple tupleTy
        withLetDecl x fstTy fst fun x => do
        withLetDecl (← tupleVar.getUserName) sndTy snd fun rest => do
          go xs rest.fvarId! sndTy (letFVars |>.push x |>.push rest)

syntax (name := doForAll)
  "for_all " optional(ident " : ") term " in " termBeforeDo " do " doSeq : doElem

@[macro doForAll] def expandDoForAll : Macro := fun stx => do
  match stx with
  | `(doForAll| for_all $[$_ : ]? $_:ident in $_ do $_) =>
      Macro.throwUnsupported
  | `(doForAll| for_all $[$h? : ]? $pattern in $xs do $body) =>
      let mut body := body
      let x ←
        if pattern.raw.isIdent then
          pure ⟨pattern⟩
        else if pattern.raw.isOfKind ``Lean.Parser.Term.hole then
          Term.mkFreshIdent pattern
        else
          let x ← Term.mkFreshIdent pattern
          body ← `(doSeq| match $x:term with | $pattern => $body)
          pure x
      `(doElem| for_all $[$h? : ]? $x:ident in $xs do $body)
  | _ => Macro.throwUnsupported

@[builtin_doElem_control_info NumLean.Meta.ForAll.doForAll] def inferForAllControlInfo : ControlInfoHandler := fun stx => do
  let `(doForAll| for_all $[$_ : ]? $_:ident in $_ do $body) := stx | throwUnsupportedSyntax
  let info ← inferControlInfoSeq body
  if info.breaks then
    throwErrorAt stx "`for_all` does not support `break`; use `for` for early exit"
  if info.continues then
    throwErrorAt stx "`for_all` does not support `continue`; use `for` for early exit"
  if info.returnsEarly then
    throwErrorAt stx "`for_all` does not support `return` from the loop body"
  return { info with numRegularExits := 1, breaks := false, continues := false, returnsEarly := false }

@[doElem_elab NumLean.Meta.ForAll.doForAll] def elabDoForAll : DoElab := fun stx dec => do
  let `(doForAll| for_all $[$h? : ]? $x:ident in $xs do $body) := stx | throwUnsupportedSyntax
  checkMutVarsForShadowing #[x]

  let mi := (← read).monadInfo
  unless ← isDefEq mi.m (mkConst ``Id [mi.u]) do
    throwErrorAt stx "`for_all` is currently supported only in pure `Id` do-blocks"

  let xsTy ← mkFreshExprMVar (mkSort (mi.u.succ)) (userName := `ρ)
  let xs ← Term.elabTermEnsuringType xs xsTy

  let info ← inferForAllControlInfo stx
  let mutVars := (← read).mutVars
  let loopMutVars := mutVars.filter fun x => info.reassigns.contains x.getId
  let loopMutVarNames := (loopMutVars.map (·.getId)).toList

  unless ← isDefEq dec.resultType (← mkPUnit) do
    logError m!"Type mismatch. `for_all` loops have result type {← mkPUnit}, but the rest of the `do` sequence expected {dec.resultType}."

  let useLoopMutVars : TermElabM (Array Expr) := do
    let mut defs := #[]
    for x in loopMutVars do
      let defn ← getLocalDeclFromUserName x.getId
      Term.addTermInfo' x defn.toExpr
      discard <| Term.ensureHasType (mkSort (mi.u.succ)) defn.type
      defs := defs.push defn.toExpr
    return defs

  let (preS, σ) ← mkMProdMkN (← useLoopMutVars) mi.u

  let idxTy ←
    match (← whnf (← instantiateMVars xsTy)) with
    | .app (.const ``Std.Rco _) idxTy => pure idxTy
    | _ => mkFreshExprMVar (mkSort (mi.u.succ)) (userName := `α)
  let uIdx ← getDecLevel idxTy
  let memInst ← synthInstance (mkApp2 (mkConst ``Membership [uIdx, mi.u]) idxTy xsTy)
  let hxTy (idx : Expr) : Expr :=
    mkApp5 (mkConst ``Membership.mem [uIdx, mi.u]) idxTy xsTy memInst xs idx

  let s ← mkFreshUserName `__s
  let anonH ← mkFreshUserName `__h
  let xh : Array (Name × (Array Expr → DoElabM Expr)) := match h? with
    | some h => #[(x.getId, fun _ => pure idxTy), (h.getId, fun xs => pure (hxTy xs[0]!))]
    | none => #[(x.getId, fun _ => pure idxTy), (anonH, fun xs => pure (hxTy xs[0]!))]

  let bodyFn ←
    withLocalDeclsD xh fun xh => do
    withLocalDecl s .default σ (kind := .implDetail) fun loopS => do
    let bodyExpr ←
      bindMutVarsFromMProd loopMutVarNames loopS.fvarId! do
      let bodyResultType := σ
      let nextState : DoElabM Expr := do
        let (tuple, _tupleTy) ← mkMProdMkN (← useLoopMutVars) mi.u
        mkPureApp bodyResultType tuple
      withDoBlockResultType bodyResultType do
      withoutControl do
        elabDoSeq body { dec with k := nextState, kind := .duplicable }
    let bodyVal ← mkAppM ``Id.run #[bodyExpr]
    mkLambdaFVars (xh.push loopS) bodyVal

  let folded ← mkAppM ``NumLean.Meta.ForAll.ForAllIn'.forAllIn' #[xs, preS, bodyFn]
  let γ := (← read).doBlockResultType
  let rest ←
    withLocalDeclD s σ fun postS => do
    mkLambdaFVars #[postS] <| ← do
      bindMutVarsFromMProd loopMutVarNames postS.fvarId! do
        dec.continueWithUnit

  mkBindApp σ γ folded rest

end Meta.ForAll
end NumLean
