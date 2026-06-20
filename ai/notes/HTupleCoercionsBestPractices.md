# `HTuple` and `FinHTuple` Coercion Best Practices

This document summarizes the current `HTuple α .leaf` / `α` and `FinHTuple h(n)` / `Fin n` / `Nat` situation in NumLean, compares it with Lean core and mathlib practice, and lists concrete API gaps.

## Current API

`HTuple α .leaf` already has the essential scalar bridge in `NumLean/Data/HTuple/Basic.lean`:

- `HTuple.toScalar : HTuple α .leaf → α`, marked `@[coe]`.
- `CoeOut (HTuple α .leaf) α`.
- `Coe α (HTuple α .leaf)` via `HTuple.leaf`.
- Round-trip and injectivity lemmas for `HTuple.leaf`/`HTuple.toScalar`.
- `GetElem` and `SetElem` bridge instances from `HTuple idx .leaf` to `idx`.
- `[simp]` lemmas `leaf_toScalar`, `getElem_leaf`, and `setElem_leaf`.

Elementwise order has leaf-specific bridge lemmas in `NumLean/Data/HTuple/Order.lean`:

- `elementwiseLE_leaf`, `elementwiseLE_leaf'`, `elementwiseLE_leaf''`.
- `elementwiseLT_leaf`, `elementwiseLT_leaf'`, `elementwiseLT_leaf''`.
- Product decomposition lemmas and `grind_htuple_order` attributes.

`HTuple` algebra has a pointwise `NatCast` through the semiring instance in `NumLean/Data/HTuple/Algebra.lean`:

- `natCast := fun n => HTuple.ofFn fun _ => n`.
- `natCast_eq_toScalar (n) : (n.cast : HTuple Nat .leaf).toScalar = n`.
- `[simp]`/`[norm_cast]` lemmas normalizing `(n : HTuple Nat .leaf)` back to `.leaf n` and to `n : Nat`.

`FinHTuple ns` already has the essential bounded tuple bridge in `NumLean/Data/FinHTuple/Basic.lean`:

- `CoeOut (FinHTuple ns) (HTuple Nat p)` via `.val`.
- `leafEquiv (n) : FinHTuple h(n) ≃ Fin n`.
- `toFin : FinHTuple h(n) → Fin n`, marked `@[coe]`.
- `toNat : FinHTuple h(n) → Nat`, marked `@[coe]`.
- `Coe (FinHTuple h(n)) (Fin n)` and `CoeOut (FinHTuple h(n)) Nat`.
- `[simp] theorem coe_coe (i : FinHTuple h(n)) : i.toFin.val = i.toNat`.
- `[simp]`/`[norm_cast]` lemmas for `((i : Fin n) : Nat) = (i : Nat)`, `(i : Nat) = i.toNat`, and `(i : Nat) = i.val.toScalar`.
- `ofFin`, `ofNatLt`, and `CanLift` instances from `Nat` to `FinHTuple h(n)` and from raw tuples to `FinHTuple ns`.
- Generic `GetElem` / `SetElem` through `.val`, plus leaf-specific `GetElem` / `SetElem` through `.toFin`.

`FinHTupleMap src dst` currently has in `NumLean/Data/FinHTuple/FinHTupleMap.lean`:

- An affine payload extending `HTupleMap Nat p q`.
- `inBounds : ∀ i, i <ₑ src → eval i <ₑ dst`.
- `eval : FinHTupleMap src dst → HTuple Nat p → HTuple Nat q`, marked `@[coe]`.
- `CoeFun` to raw functions `HTuple Nat p → HTuple Nat q`.
- `evalFin : FinHTupleMap src dst → FinHTuple src → FinHTuple dst` for bounded output.
- `GetElem` notation `f[i]'h` returning `FinHTuple dst` when `h : i <ₑ src`.
- `eval_lt` as the main boundedness theorem.

## Upstream Patterns

Lean core `Fin` is the closest model.

- `Fin` exposes the underlying natural as `Fin.val` and has `CoeOut (Fin n) Nat`.
- `Fin.toNat` exists only as a synonym; `simp` rewrites `i.toNat` to `i.val`.
- Extensionality is by the coerced natural value: `@[ext] theorem Fin.ext`.
- Constructor/projection lemmas are aggressively simp-normalized, for example `Fin.is_lt`, `Fin.eta`, `Fin.val_mk`, and `Fin.ofNat_val_eq_self`.
- Order on `Fin` is definitionally order on `.val`, with `[simp]` and `[norm_cast]` lemmas in mathlib such as `Fin.val_fin_lt` and `Fin.val_fin_le`.
- Lean deliberately does not make `NatCast (Fin n)` global. The core comment explains that a global `Nat → Fin n → Nat` loop makes expressions like `x < n` elaborate as `x < (n : Fin k)` rather than `(x : Nat) < n`, silently introducing modular arithmetic.

The function-object model is `LinearMap` / `ContinuousLinearMap` in mathlib.

- Bundled maps use `FunLike` when coercion-to-function is injective.
- They provide `MapClass` typeclasses for generic lemmas over bundled maps.
- They use `@[ext]` extensionality by pointwise equality.
- They provide `[simp]`/`[norm_cast]` coercion lemmas such as `coe_mk`, `coe_coe`, and coercion-injectivity theorems.
- They use `initialize_simps_projections` so generated simp lemmas are phrased in terms of application rather than internal fields.

This pattern should be copied only when extensional equality by application is actually true. For affine-map records, equality of evaluations on a bounded finite domain may not determine `offset` and `stride`, especially with empty or degenerate shapes. In that case use `CoeFun`, not `FunLike`.

## Recommended Normal Forms

Use these normal forms consistently:

- For `x : HTuple α .leaf`, scalar-facing expressions should simplify to `x.toScalar` or `(x : α)`.
- For `a : α`, tuple-facing scalar literals should simplify to `HTuple.leaf a`. The notation `h(a)` is only macro syntax for the same term, so it should not get separate API.
- For order facts on `HTuple α .leaf`, the final proposition should be scalar order on `α`, not order on wrappers.
- For `i : FinHTuple h(n)`, the canonical bounded value is `i.val : HTuple Nat .leaf`, the canonical finite index is `i.toFin : Fin n`, and the canonical natural is `i.toNat` or `(i : Nat)`.
- Any expression `((i : Fin n) : Nat)` should simplify to `(i : Nat)` for `i : FinHTuple h(n)`.
- For raw bounded tuple facts, prefer `i.val <ₑ ns` and `i.val ∈ 0...ns`; for scalar leaf facts, prefer `(i : Nat) < n`.
- For `GetElem`/`SetElem`, leaf tuple indices should normalize to the scalar or `Fin` index expected by the container.

## Coercion Policy

Safe global coercions:

- `HTuple α .leaf → α` via `CoeOut`.
- `α → HTuple α .leaf` via `Coe`.
- `FinHTuple ns → HTuple Nat p` via `CoeOut`.
- `FinHTuple h(n) → Fin n` via `Coe`.
- `FinHTuple h(n) → Nat` via `CoeOut`.

Avoid these global coercions:

- A global `NatCast (FinHTuple h(n))` or `Nat → FinHTuple h(n)` instance. This recreates the `Fin` coercion-loop problem and can make mixed scalar/index expressions elaborate with modular or bounded semantics unexpectedly.
- A global `Fin n → FinHTuple h(n)` coercion unless there is a very strong elaboration need. Prefer explicit `leafEquiv n |>.symm` or a named constructor/abbrev.
- A `FunLike` instance for `FinHTupleMap` unless evaluator injectivity is proved for the intended equality. `CoeFun` is enough for notation.

Useful non-instance constructions:

- `FinHTuple.ofNatLt {n} (i : Nat) (h : i < n) : FinHTuple h(n)`.
- `FinHTuple.ofFin {n} (i : Fin n) : FinHTuple h(n)`.
- `CanLift Nat (FinHTuple h(n)) (fun i => (i : Nat)) (· < n)`.
- `CanLift (HTuple Nat p) (FinHTuple ns) FinHTuple.val (· <ₑ ns)`.

## API Checklist And Remaining Gaps

### `HTuple α .leaf`

The following round-trip and injectivity lemmas should be part of the API and preserved by regression tests:

```lean
@[simp] theorem HTuple.toScalar_leaf (a : α) : (HTuple.leaf a).toScalar = a := rfl
@[simp] theorem HTuple.leaf_toScalar_eta (x : HTuple α .leaf) : HTuple.leaf x.toScalar = x := by cases x; rfl
@[simp] theorem HTuple.coe_leaf (a : α) : ((HTuple.leaf a : HTuple α .leaf) : α) = a := rfl
@[simp] theorem HTuple.leaf_coe (x : HTuple α .leaf) : (HTuple.leaf (x : α) : HTuple α .leaf) = x := by cases x; rfl
theorem HTuple.toScalar_injective : Function.Injective (HTuple.toScalar : HTuple α .leaf → α)
```

The current `natCast_eq_toScalar` is useful, and the expected simp shape should also be present. Do not duplicate these for `h(n)`: `h(n)` is just macro notation for `.leaf n`.

```lean
@[simp, norm_cast] theorem HTuple.coe_natCast_leaf (n : Nat) : ((n : HTuple Nat .leaf) : Nat) = n := rfl
@[simp] theorem HTuple.natCast_leaf (n : Nat) : (n : HTuple Nat .leaf) = .leaf n := rfl
```

Direct `[simp]` and `grind_htuple_order` lemmas for `Nat.cast` on either side are important because they let `a <ₑ b` for `a : HTuple Nat .leaf` and `b : Nat` normalize without manually unfolding `Nat.cast`:

```lean
@[simp, grind =, grind_htuple_order =]
theorem HTuple.elementwiseLT_natCast_right {a : HTuple Nat .leaf} {b : Nat} :
    a <ₑ (b : HTuple Nat .leaf) ↔ (a : Nat) < b := by cases a; rfl

@[simp, grind =, grind_htuple_order =]
theorem HTuple.elementwiseLE_natCast_right {a : HTuple Nat .leaf} {b : Nat} :
    a ≤ₑ (b : HTuple Nat .leaf) ↔ (a : Nat) ≤ b := by cases a; rfl
```

Keep both left- and right-sided versions; they catch different elaboration paths.

### `FinHTuple h(n)`

The direct Nat/Fin coercion theorem should exist in cast notation and be tagged for `norm_cast`:

```lean
@[simp, norm_cast] theorem FinHTuple.coe_toFin_nat (i : FinHTuple h(n)) :
    (((i : Fin n) : Nat) = (i : Nat)) := rfl
```

Keep simp lemmas tying all representations to `.val.toScalar`:

```lean
@[simp] theorem FinHTuple.toNat_eq_val_toScalar (i : FinHTuple h(n)) :
    i.toNat = i.val.toScalar := by cases i with | mk val h => cases val; rfl

@[simp] theorem FinHTuple.toFin_val_eq_val_toScalar (i : FinHTuple h(n)) :
    (i.toFin : Nat) = i.val.toScalar := by cases i with | mk val h => cases val; rfl
```

Extensionality should be discoverable by tactics:

```lean
@[ext] theorem FinHTuple.ext {i j : FinHTuple ns} (h : i.val = j.val) : i = j := ...
```

This is now tagged `@[ext]`; keep a regression test using `ext`.

Keep constructor and round-trip lemmas for `leafEquiv` in the names users will search for:

```lean
def FinHTuple.ofFin (i : Fin n) : FinHTuple h(n) := (FinHTuple.leafEquiv n).symm i

@[simp] theorem FinHTuple.toFin_ofFin (i : Fin n) : (FinHTuple.ofFin i).toFin = i := rfl
@[simp] theorem FinHTuple.ofFin_toFin (i : FinHTuple h(n)) : FinHTuple.ofFin i.toFin = i := by ext; rfl
```

Keep `CanLift` instances analogous to core `Fin`:

```lean
instance {p : Profile} {ns : HTuple Nat p} :
    CanLift (HTuple Nat p) (FinHTuple ns) FinHTuple.val (fun i => i <ₑ ns) := ...

instance {n : Nat} : CanLift Nat (FinHTuple h(n)) (fun i => (i : Nat)) (fun i => i < n) := ...
```

### `GetElem` and `SetElem`

Keep the current bridge direction: normalize richer index wrappers to the container’s native index.

Recommended simp lemmas:

- `xs[(i : HTuple idx .leaf)]` simplifies to `xs[(i : idx)]`.
- `xs[(i : FinHTuple h(n))]` simplifies to `xs[(i : Fin n)]` when the container has a `Fin n` index.
- `setElem xs (i : HTuple idx .leaf) x` simplifies to `setElem xs (i : idx) x`.
- `setElem xs (i : FinHTuple h(n)) x` simplifies to `setElem xs (i : Fin n) x`.

Most of these are already present. Add tests that check the exact elaborated type for `Vector` and `Array` indexing with `FinHTuple h(n)` and with `HTuple Nat .leaf`.

### `FinHTupleMap`

The historical docstring says the intended API is:

- `f x` for `x : FinHTuple src`.
- `f[x]` for `x : HTuple Nat p` when a proof of `x <ₑ src` is available.

The current `CoeFun` remains raw for compatibility with existing code:

```lean
CoeFun (FinHTupleMap src dst) (fun _ => HTuple Nat p → HTuple Nat q)
```

Use this bounded API when the output bound matters:

```lean
def FinHTupleMap.evalRaw (f : FinHTupleMap src dst) (i : HTuple Nat p) : HTuple Nat q :=
  f.toHTupleMap.eval i

def FinHTupleMap.evalFin (f : FinHTupleMap src dst) (i : FinHTuple src) : FinHTuple dst :=
  ⟨f.evalRaw i.val, f.inBounds i.val i.isLt⟩

@[simp] theorem FinHTupleMap.evalFin_val (f : FinHTupleMap src dst) (i : FinHTuple src) :
    (f.evalFin i).val = f.evalRaw i.val := rfl
```

`GetElem` for raw indices should return the bounded output:

```lean
instance : GetElem (FinHTupleMap src dst) (HTuple Nat p) (FinHTuple dst) (fun _ i => i <ₑ src) where
  getElem f i h := ⟨f.evalRaw i, f.inBounds i h⟩
```

For `dst = h(n)`, this means `f[i]'h` can coerce to `Fin n` and to `Nat` using the `FinHTuple h(n)` API. Function application `f i` still means raw affine evaluation.

Do not add `FunLike` unless evaluator injectivity is proved. If two different affine records can agree on all bounded inputs, `FunLike` is invalid.

### `HTupleMap`

`HTupleMap` is affine data, not merely a function. Recommended API:

- Keep a named raw evaluator, probably `HTupleMap.eval`.
- Add a `CoeFun` only for the common same-scalar case if it is ergonomically helpful and does not create inference loops.
- Add `[simp]` evaluation lemmas for constructors: `eval_id`, `eval_comp`, `eval_fst`, `eval_snd`, `eval_prod`, `eval_const`, `eval_linearize`.
- Avoid `FunLike` unless equality of maps is intended to be extensional by evaluation over all inputs and this is proved.

## Attribute Policy

Use `@[simp]` for structural projections and round-trips that reduce wrappers:

- `toScalar (leaf a) = a`.
- `leaf (toScalar x) = x`.
- `(i.toFin : Nat) = i.toNat`.
- `i.toNat = i.val.toScalar`.
- `GetElem`/`SetElem` bridge lemmas.

Use `@[norm_cast]` for theorems whose purpose is moving coercions across relations or equalities:

- `((i : Fin n) : Nat) = (i : Nat)` for `FinHTuple h(n)`.
- Scalar comparisons involving `FinHTuple h(n)` and `Nat`.
- Scalar comparisons involving `HTuple Nat .leaf` and `Nat` if they are phrased as coercions.

Use `@[grind_htuple_order]` for order-normalization lemmas that should be available to the tuple-order automation:

- Product decomposition of `<ₑ` and `≤ₑ`.
- Leaf scalar bridges.
- `Nat.cast` leaf bridges.
- Range membership bridges.
- Boundedness of `FinHTuple.val` and `FinHTupleMap` evaluation.

Avoid making large recursive definitions reducible just to help coercions. Prefer small bridge lemmas with controlled attributes.

## Suggested Regression Tests

Add tests for these examples:

```lean
example (a : HTuple Nat .leaf) (b : Nat) :
    (a <ₑ b) ↔ (a : Nat) < b := by simp

example (a : Nat) (b : HTuple Nat .leaf) :
    (a <ₑ b) ↔ a < (b : Nat) := by simp

example (i : FinHTuple h(n)) :
    (((i : Fin n) : Nat) = (i : Nat)) := by simp

example (i : FinHTuple h(n)) :
    (i.val : HTuple Nat .leaf).toScalar = (i : Nat) := by simp

example (xs : Vector α n) (i : FinHTuple h(n)) :
    xs[i] = xs[(i : Fin n)] := by rfl

example {src : HTuple Nat p} {dst : HTuple Nat q} (f : FinHTupleMap src dst) (i : FinHTuple src) :
    (f i).val <ₑ dst := by exact (f i).isLt
```

Also keep the current negative test around `Nat.cast` until the direct leaf cast lemmas are added, then turn it into a positive `simp`/`grind` test.

## Priority List

1. Add missing `HTuple α .leaf` round-trip simp lemmas.
2. Add `Nat.cast`/leaf order bridge lemmas for `HTuple Nat .leaf` and tag them for `simp` and `grind_htuple_order`.
3. Add explicit `[simp, norm_cast]` theorem for `((i : Fin n) : Nat) = (i : Nat)` on `FinHTuple h(n)`.
4. Tag `FinHTuple.ext` with `@[ext]` and add representation-normalizing simp lemmas through `.val.toScalar`.
5. Add `CanLift` instances for raw tuple-to-bounded tuple and Nat-to-leaf-bounded tuple.
6. Rework `FinHTupleMap` so function application returns `FinHTuple dst`, and raw evaluation uses `evalRaw` or `f[i]'h`.
7. Add regression tests for each mixed scalar/leaf/Fin expression that should elaborate and simplify automatically.
