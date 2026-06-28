module

public import Batteries.Data.FloatArray
public import NumLean.Experimental.Data.KernelExpr.Basic
public import NumLean.Experimental.Data.KernelExpr.Register
public import NumLean.Tactic.ApplyRuleSets
public import NumLean.Tactic.ApplyRuleSets.RuleProc
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

namespace NumLean
#exit
/--
`HasKernelExpr x i ctx e kernel` records that the scalar/index expression `e` can be
represented by the typed kernel expression `kernel` when evaluating element `x` at global
index `i` with array context `ctx`.

This is intentionally `FloatArray`-specific for now. The shape mirrors the OpenCL version,
but the array context is plain `FloatArray`; it can later be generalized over a flat-array
interface.
-/
structure HasKernelExpr  (boundVars : Array ((t : KernelTypeTag) × KernelType R t)) (ctx : Array (Array R)) {t}
    (e : KernelType Float t) (kernel : KernelExpr Float t) : Prop where
  well_formed : kernel.WellFormed
  denote : kernel.eval (ctx.map (·.data)).toArray x i = e

structure HasContextIndex (ctx : List FloatArray) (xs : FloatArray) (i : Nat) : Prop where
  in_context : ctx[i]? = some xs

namespace HasKernelExpr

variable {x : Float} {i : Nat} {ctx : List FloatArray}

theorem expr_congr {ctx : List FloatArray} {t}
    {e : KernelType.denote Float t} {kernel kernel' : KernelExpr Float t}
    (h : HasKernelExpr x i ctx e kernel) (h' : kernel = kernel') :
    HasKernelExpr x i ctx e kernel' := by
  subst h'
  exact h

theorem expr_ctx_congr {ctx ctx' : List FloatArray} {t}
    {e : KernelType.denote Float t} {kernel kernel' : KernelExpr Float t}
    (h : HasKernelExpr x i ctx e kernel) (hctx : ctx = ctx') (h' : kernel = kernel') :
    HasKernelExpr x i ctx' e kernel' := by
  subst hctx
  subst h'
  exact h

open Lean Meta in
@[compile_kernel_expr high]
ruleproc collect_context , (x : Float) (i : Nat) (ctx : List FloatArray) {t}
    (e : KernelType.denote Float t) (kernel : KernelExpr Float t) :
    HasKernelExpr x i ctx e kernel :=
  fun argOrigin goal => do
    let ctx ← instantiateMVars ctx
    let e ← instantiateMVars e

    if ctx.isMVar && ¬e.isMVar then
      let fvars := (← (e.collectFVars.run {})).2.fvarIds
      let arrayTy := mkConst ``FloatArray

      let mut arrayFVars := #[]
      for id in fvars do
        let ty ← id.getType
        if ← isDefEq ty arrayTy then
          arrayFVars := arrayFVars.push id

      let mut xs ← mkAppOptM ``List.nil #[arrayTy]
      for id in arrayFVars.reverse do
        xs ← mkAppM ``List.cons #[.fvar id, xs]

      ctx.mvarId!.assign xs
      return ← NumLean.Tactic.ApplyRuleSets.applyRuleSets argOrigin goal

    return none

open Lean Meta in
@[compile_kernel_expr]
ruleproc has_context_index , (ctx : List FloatArray) (xs : FloatArray) (i : Nat) : HasContextIndex ctx xs i :=
  fun _ goal => do
    let ctx ← instantiateMVars ctx
    let xs ← instantiateMVars xs
    let i ← instantiateMVars i

    if ¬ctx.isMVar && xs.isFVar then
      let rec getContextFVars (ctx : Expr) (acc : Array FVarId) : Option (Array FVarId) := do
        match ctx with
        | mkApp3 (.const ``List.cons _) _ (.fvar id) ctx' =>
            getContextFVars ctx' (acc.push id)
        | Expr.app (Expr.const ``List.nil _) _ => some acc
        | _ => none
      let some ctxFVars := getContextFVars ctx #[] | return none
      let .fvar id := xs | return none
      let some n := ctxFVars.idxOf? id | return none
      if i.isMVar then
        i.mvarId!.assign (mkNatLit n)
      let prf ← mkFreshExprMVar goal
      let fields ← prf.mvarId!.constructor
      match fields with
      | [field] =>
        try field.refl catch _ => return none
        return prf
      | _ => return none
    return none

@[compile_kernel_expr]
theorem x_rule : HasKernelExpr x i ctx x .x := by
  constructor
  simp [KernelExpr.eval, KernelExpr.evalReal]

@[compile_kernel_expr]
theorem i_rule : HasKernelExpr x i ctx i .gid := by
  constructor
  simp [KernelExpr.eval, KernelExpr.evalNat]

theorem lit_rule_proof (v : Float) : HasKernelExpr x i ctx v (.lit v) := by
  constructor
  simp [KernelExpr.eval, KernelExpr.evalReal]

theorem nat_lit_rule_proof (v : Nat) : HasKernelExpr x i ctx v (.natLit v) := by
  constructor
  simp [KernelExpr.eval, KernelExpr.evalNat]

theorem int_lit_rule_proof (v : Int) : HasKernelExpr x i ctx v (.intLit v) := by
  constructor
  simp [KernelExpr.eval, KernelExpr.evalInt]

open Lean Meta in
@[compile_kernel_expr low]
ruleproc lit_rule , (x : Float) (i : Nat) (ctx : List FloatArray)
    (v : Float) (kernel : KernelExpr Float .real) : HasKernelExpr x i ctx v kernel :=
  fun _ _ => do
    let v ← instantiateMVars v
    let kernel ← instantiateMVars kernel
    if !kernel.isMVar then
      return none
    try
      discard <| Meta.evalExpr Float (mkConst ``Float) v
    catch _ =>
      return none
    kernel.mvarId!.assign (← mkAppOptM ``KernelExpr.lit #[some (mkConst ``Float), some v])
    return some (← mkAppOptM ``HasKernelExpr.lit_rule_proof #[some x, some i, some ctx, some v])

open Lean Meta in
@[compile_kernel_expr low]
ruleproc nat_lit_rule , (x : Float) (i : Nat) (ctx : List FloatArray)
    (v : Nat) (kernel : KernelExpr Float .nat) : HasKernelExpr x i ctx v kernel :=
  fun _ _ => do
    let v ← instantiateMVars v
    let kernel ← instantiateMVars kernel
    if !kernel.isMVar then
      return none
    try
      discard <| Meta.evalExpr Nat (mkConst ``Nat) v
    catch _ =>
      return none
    kernel.mvarId!.assign (← mkAppOptM ``KernelExpr.natLit #[some (mkConst ``Float), some v])
    return some (← mkAppOptM ``HasKernelExpr.nat_lit_rule_proof #[some x, some i, some ctx, some v])

open Lean Meta in
@[compile_kernel_expr low]
ruleproc int_lit_rule , (x : Float) (i : Nat) (ctx : List FloatArray)
    (v : Int) (kernel : KernelExpr Float .int) : HasKernelExpr x i ctx v kernel :=
  fun _ _ => do
    let v ← instantiateMVars v
    let kernel ← instantiateMVars kernel
    if !kernel.isMVar then
      return none
    try
      discard <| Meta.evalExpr Int (mkConst ``Int) v
    catch _ =>
      return none
    kernel.mvarId!.assign (← mkAppOptM ``KernelExpr.intLit #[some (mkConst ``Float), some v])
    return some (← mkAppOptM ``HasKernelExpr.int_lit_rule_proof #[some x, some i, some ctx, some v])

@[compile_kernel_expr]
theorem add_real {a b : Float} {ka kb : KernelExpr Float .real}
    (ha : HasKernelExpr x i ctx a ka) (hb : HasKernelExpr x i ctx b kb) :
    HasKernelExpr x i ctx (a + b) (ka + kb) := by
  constructor
  have hka : KernelExpr.evalReal (ctx.map (·.data)).toArray x i ka = a := by simpa [KernelExpr.eval] using ha.denote
  have hkb : KernelExpr.evalReal (ctx.map (·.data)).toArray x i kb = b := by simpa [KernelExpr.eval] using hb.denote
  change KernelExpr.evalReal (ctx.map (·.data)).toArray x i (KernelExpr.add ka kb) = a + b
  simp [KernelExpr.evalReal, hka, hkb]

@[compile_kernel_expr]
theorem sub_real {a b : Float} {ka kb : KernelExpr Float .real}
    (ha : HasKernelExpr x i ctx a ka) (hb : HasKernelExpr x i ctx b kb) :
    HasKernelExpr x i ctx (a - b) (ka - kb) := by
  constructor
  have hka : KernelExpr.evalReal (ctx.map (·.data)).toArray x i ka = a := by simpa [KernelExpr.eval] using ha.denote
  have hkb : KernelExpr.evalReal (ctx.map (·.data)).toArray x i kb = b := by simpa [KernelExpr.eval] using hb.denote
  change KernelExpr.evalReal (ctx.map (·.data)).toArray x i (KernelExpr.sub ka kb) = a - b
  simp [KernelExpr.evalReal, hka, hkb]

@[compile_kernel_expr]
theorem mul_real {a b : Float} {ka kb : KernelExpr Float .real}
    (ha : HasKernelExpr x i ctx a ka) (hb : HasKernelExpr x i ctx b kb) :
    HasKernelExpr x i ctx (a * b) (ka * kb) := by
  constructor
  have hka : KernelExpr.evalReal (ctx.map (·.data)).toArray x i ka = a := by simpa [KernelExpr.eval] using ha.denote
  have hkb : KernelExpr.evalReal (ctx.map (·.data)).toArray x i kb = b := by simpa [KernelExpr.eval] using hb.denote
  change KernelExpr.evalReal (ctx.map (·.data)).toArray x i (KernelExpr.mul ka kb) = a * b
  simp [KernelExpr.evalReal, hka, hkb]

@[compile_kernel_expr]
theorem div_real {a b : Float} {ka kb : KernelExpr Float .real}
    (ha : HasKernelExpr x i ctx a ka) (hb : HasKernelExpr x i ctx b kb) :
    HasKernelExpr x i ctx (a / b) (ka / kb) := by
  constructor
  have hka : KernelExpr.evalReal (ctx.map (·.data)).toArray x i ka = a := by simpa [KernelExpr.eval] using ha.denote
  have hkb : KernelExpr.evalReal (ctx.map (·.data)).toArray x i kb = b := by simpa [KernelExpr.eval] using hb.denote
  change KernelExpr.evalReal (ctx.map (·.data)).toArray x i (KernelExpr.div ka kb) = a / b
  simp [KernelExpr.evalReal, hka, hkb]

@[compile_kernel_expr]
theorem neg_real {a : Float} {ka : KernelExpr Float .real}
    (ha : HasKernelExpr x i ctx a ka) :
    HasKernelExpr x i ctx (-a) (-ka) := by
  constructor
  have hka : KernelExpr.evalReal (ctx.map (·.data)).toArray x i ka = a := by simpa [KernelExpr.eval] using ha.denote
  change KernelExpr.evalReal (ctx.map (·.data)).toArray x i (KernelExpr.neg ka) = -a
  simp [KernelExpr.evalReal, hka]

@[compile_kernel_expr]
theorem add_nat {a b : Nat} {ka kb : KernelExpr Float .nat}
    (ha : HasKernelExpr x i ctx a ka) (hb : HasKernelExpr x i ctx b kb) :
    HasKernelExpr x i ctx (a + b) (ka + kb) := by
  constructor
  have hka : KernelExpr.evalNat (ctx.map (·.data)).toArray x i ka = a := by simpa [KernelExpr.eval] using ha.denote
  have hkb : KernelExpr.evalNat (ctx.map (·.data)).toArray x i kb = b := by simpa [KernelExpr.eval] using hb.denote
  change KernelExpr.evalNat (ctx.map (·.data)).toArray x i (KernelExpr.add ka kb) = a + b
  simp [KernelExpr.evalNat, hka, hkb]

@[compile_kernel_expr]
theorem mul_nat {a b : Nat} {ka kb : KernelExpr Float .nat}
    (ha : HasKernelExpr x i ctx a ka) (hb : HasKernelExpr x i ctx b kb) :
    HasKernelExpr x i ctx (a * b) (ka * kb) := by
  constructor
  have hka : KernelExpr.evalNat (ctx.map (·.data)).toArray x i ka = a := by simpa [KernelExpr.eval] using ha.denote
  have hkb : KernelExpr.evalNat (ctx.map (·.data)).toArray x i kb = b := by simpa [KernelExpr.eval] using hb.denote
  change KernelExpr.evalNat (ctx.map (·.data)).toArray x i (KernelExpr.mul ka kb) = a * b
  simp [KernelExpr.evalNat, hka, hkb]

@[compile_kernel_expr]
theorem cast_real_of_nat {a : Nat} {ka : KernelExpr Float .nat}
    (ha : HasKernelExpr x i ctx a ka) :
    HasKernelExpr x i ctx (a • (1 : Float)) (KernelExpr.cast .real ka) := by
  constructor
  have hka : KernelExpr.evalNat (ctx.map (·.data)).toArray x i ka = a := by simpa [KernelExpr.eval] using ha.denote
  simp [KernelExpr.eval, KernelExpr.evalReal, KernelExpr.evalCastReal, hka]

@[compile_kernel_expr]
theorem ctx_get_elem (xs : FloatArray) (idx : Nat)
    {eidx} (hidx : HasKernelExpr x i ctx idx eidx)
    {ixs} (hxs : HasContextIndex ctx xs ixs) :
    HasKernelExpr x i ctx (xs.data[idx]?.getD 0) (.ctx ixs eidx) := by
  constructor
  have hh := hidx.denote
  simp [KernelExpr.eval] at hh
  simp [KernelExpr.eval, KernelExpr.evalReal, hxs.in_context, hh]

@[compile_kernel_expr]
theorem ctx_size (xs : FloatArray)
    {ixs} (hxs : HasContextIndex ctx xs ixs) :
    HasKernelExpr x i ctx xs.size (.ctxSize ixs) := by
  constructor
  simp [KernelExpr.eval, KernelExpr.evalNat, hxs.in_context]
  rfl

section Examples

private def one : Float := 1
private def two : Float := 2

variable (x : Float) (i : Nat) (xs ys : FloatArray)

example : HasKernelExpr x i [] (x + one) (KernelExpr.x + KernelExpr.lit one) := by
  apply HasKernelExpr.expr_congr
  apply_rulesets [compile_kernel_expr]
  rfl

example : HasKernelExpr x i [] (i • (1 : Float)) (KernelExpr.cast .real KernelExpr.gid) := by
  apply HasKernelExpr.expr_congr
  apply_rulesets [compile_kernel_expr]
  rfl

example : HasContextIndex [xs, ys] ys 1 := by
  apply_rulesets [compile_kernel_expr]

example : HasKernelExpr x i [xs] (xs.data[i]?.getD 0) (.ctx 0 KernelExpr.gid) := by
  apply HasKernelExpr.expr_ctx_congr
  apply_rulesets [compile_kernel_expr]
  rfl
  rfl

example : HasKernelExpr x i [ys] ys.size (.ctxSize 0) := by
  apply HasKernelExpr.expr_ctx_congr
  apply_rulesets [compile_kernel_expr]
  rfl
  rfl

end Examples

end HasKernelExpr

end NumLean
