# Fold And Range API Roadmap

This note records the plan for a more stable, comprehensive API for reasoning about folded ranges.

The main goal is to stop exposing users to subtype-heavy range entries when the intended mental model is a simple finite index space.  The public API should make it easy to move between a range and `Fin n` through `fromFin`/`toFin`, and `simp` should discharge the proof plumbing.

## Current Pain Points

### Subtype-heavy fold entries

The canonical fold model is currently:

```lean
NumLean.entries xs : List {a : α // a ∈ xs}
```

This is good internally, but downstream proofs often have to manipulate `{a // a ∈ xs}` explicitly.

Hotspots:

- `NumLean/Data/FinHTuple/Fold.lean`
- `NumLean/Data/Vector/TensorAlgebra/Lemmas.lean`
- `NumLean/Data/Tensor/Algebra/Equiv.lean`
- `NumLean/Interfaces/TensorAlgebra.lean`

Common symptoms:

- repeated `Subtype.ext` proofs;
- repeated conversion from `entries (0...shape)` to `Fin shape.numel`;
- duplicated bespoke sum lemmas;
- proof terms leaking into user-facing theorem statements.

### Range membership conversions are too visible

For HTuple ranges, proofs often manually rewrite through:

```lean
HTuple.Range.mem_iff_Valid
Std.Rco.mem_iff
HTuple.Range.valid_iff_le_lt
```

Hotspots:

- `NumLean/Data/HTuple/Fold.lean:23-34`
- `NumLean/Data/HTuple/Fold.lean:130-153`
- `NumLean/Meta/ForAll/HTuple.lean:91-150`
- `NumLean/Data/Tensor/Algebra/Equiv.lean:36-65`

Desired normal forms:

```lean
idx ∈ ((0 : HTuple Nat p)...shape) ↔ idx <ₑ shape
h(i) ∈ (h(0)...h(n) : Std.Rco (HTuple Nat .leaf)) ↔ i < n
idx ∈ (lo...hi : Std.Rco (HTuple α p)) ↔ lo ≤ₑ idx ∧ idx <ₑ hi
```

### Product range API exists but is still low-level

Existing files already contain the key facts:

- `NumLean/Data/Prod/Fold.lean`
- `NumLean/Data/HTuple/Fold.lean`

But tensor proofs still need direct construction of product membership proofs, especially for loops over matrix-like ranges.

Desired theorem shapes:

```lean
Fold.fold ((lo₀, lo₁)...(hi₀, hi₁)) init f =
  Fold.fold (lo₀...hi₀) init fun i hi acc =>
    Fold.fold (lo₁...hi₁) acc fun j hj acc =>
      f (i, j) (by simp [hi, hj]) acc

Fold.fold ((lo₀.prod lo₁)...(hi₀.prod hi₁)) init f =
  Fold.fold (lo₀...hi₀) init fun i hi acc =>
    Fold.fold (lo₁...hi₁) acc fun j hj acc =>
      f (i.prod j) (by simp [hi, hj]) acc
```

There should also be a direct theorem connecting these two product spellings for HTuples:

```lean
Fold.fold ((lo₀, lo₁)...(hi₀, hi₁)) init (fun (i, j) h acc => ...)
=
Fold.fold ((lo₀.prod lo₁)...(hi₀.prod hi₁)) init (fun ij h acc => ...)
```

### Layout range inverses are too hard to use

The `FinHTupleMap.rangeNat` and `rangeNatInv` API is useful, but callers still repeatedly prove membership and inverse facts by hand.

Hotspots:

- `NumLean/Data/FinHTuple/Fold.lean:140-193`
- `NumLean/Interfaces/TensorAlgebra.lean:378-445`
- `NumLean/Data/Tensor/HasFlatRepr.lean:34-80`
- `NumLean/Data/Tensor/Algebra/Equiv.lean:100-126`

Desired simp lemmas:

```lean
idx ∈ (Layout.id h(n)).rangeNat ↔ idx < n
(Layout.id h(n)).rangeNatInv idx h = ⟨h(idx), ...⟩

idx ∈ (Layout.contiguous1D off h).rangeNat ↔ off ≤ idx ∧ idx < off + len
(Layout.contiguous1D off h).rangeNatInv idx h = ⟨h(idx - off), ...⟩

i.rowMajorIndex shape ∈ (FinHTupleMap.rowMajorMap shape).rangeNat
(FinHTupleMap.rowMajorMap shape).rangeNatInv (i.rowMajorIndex shape) _ = ⟨i, hi⟩
```

Some row-major inverse lemmas already exist in `NumLean/Data/FinHTuple/FinHTupleMap.lean`; the main work is providing higher-level theorem shapes and `simp`-friendly wrappers.

### There are two no-break traversal stacks

`Interfaces/Fold` defines the newer canonical API:

```lean
FoldEntries
Fold
LawfulFold
```

`Meta/ForAll` still defines a parallel no-break API:

```lean
ForAllIn'
LawfulForAllIn'
ForAllInProfile
LawfulForAllInProfile
```

This duplicates scalar native stepping and HTuple profile recursion.

Hotspots:

- `NumLean/Meta/ForAll/Basic.lean`
- `NumLean/Meta/ForAll/RcoNative.lean`
- `NumLean/Meta/ForAll/RcoNat.lean`
- `NumLean/Meta/ForAll/HTuple.lean`
- `NumLean/Data/HTuple/Fold.lean`

Direction:

- `Fold` should be the canonical no-break, lawful range API.
- `ForIn'` and RangeIterator code should remain for monadic or breakable loops.
- `for_all_fast` should eventually route through a Fold-level fast path rather than a separate law stack.

## Proposed Core API

### `Fold.FinRangeView`

Add a finite-index view for lawful folded ranges, likely in `NumLean/Interfaces/Fold/Fin.lean`.

Sketch:

```lean
structure Fold.FinRangeView {ρ α} [Membership α ρ]
    [FoldEntries ρ α inferInstance] [Fold ρ] [LawfulFold ρ α inferInstance]
    (xs : ρ) where
  size : Nat
  fromFin : Fin size → α
  mem_fromFin : ∀ i, fromFin i ∈ xs
  toFin : (a : α) → a ∈ xs → Fin size
  toFin_fromFin : ∀ i, toFin (fromFin i) (mem_fromFin i) = i
  fromFin_toFin : ∀ a h, fromFin (toFin a h) = a
  entries_eq :
    NumLean.entries xs =
      (List.finRange size).map fun i => ⟨fromFin i, mem_fromFin i⟩
```

The important design decision is that users should usually see only:

```lean
view.size
view.fromFin
view.toFin
```

The subtype proof fields stay internal and are used by bridge lemmas.

### Generic fold-to-`Fin.foldl`

The key theorem should be generic over any finite range view:

```lean
theorem Fold.FinRangeView.fold_eq_fin_foldl
    (view : Fold.FinRangeView xs) :
    Fold.fold xs init f =
      Fin.foldl view.size
        (fun acc i => f (view.fromFin i) (view.mem_fromFin i) acc)
        init
```

Also add convenience lemmas:

```lean
theorem Fold.FinRangeView.entries_eq_finRange
theorem Fold.FinRangeView.toFin_fromFin
theorem Fold.FinRangeView.fromFin_toFin
def Fold.FinRangeView.rangeIsoFin
```

### Big-operator wrappers

Current code has `Fold.fold_eq_sum`; tensor algebra needs more than additive sums.

Add:

```lean
theorem Fold.fold_eq_fin_sum
theorem Fold.fold_eq_fin_prod
theorem Fold.sum_entries_eq_fin_sum
theorem Fold.prod_entries_eq_fin_prod
```

Longer term, prefer a monoid-polymorphic theorem over one-off additive and multiplicative variants.

## Standard Range Views

### Nat ranges

For zero-origin ranges:

```lean
def Fold.finViewZeroNat (n : Nat) :
    Fold.FinRangeView (0...n : Std.Rco Nat)
```

Use:

```lean
size := n
fromFin i := i.val
toFin a ha := ⟨a, (Std.Rco.mem_iff.mp ha).2⟩
```

For general ranges:

```lean
def Fold.finViewNat (lo hi : Nat) :
    Fold.FinRangeView (lo...hi : Std.Rco Nat)
```

Use:

```lean
size := hi - lo
fromFin i := lo + i.val
toFin a ha := ⟨a - lo, by omega⟩
```

### Int ranges

For integer ranges:

```lean
def Fold.finViewInt (lo hi : Int) :
    Fold.FinRangeView (lo...hi : Std.Rco Int)
```

Use:

```lean
size := (hi - lo).toNat
fromFin i := lo + i.val
toFin a ha := ⟨(a - lo).toNat, by omega⟩
```

### Product ranges

Given views for `xs` and `ys`, define a row-major product view:

```lean
def Fold.FinRangeView.prod
    (vx : Fold.FinRangeView xs) (vy : Fold.FinRangeView ys) :
    Fold.FinRangeView ((xs.lower, ys.lower)...(xs.upper, ys.upper))
```

Use `finProdFinEquiv` so the order matches existing product folds:

```lean
size := vx.size * vy.size
fromFin i :=
  let ij := finProdFinEquiv.symm i
  (vx.fromFin ij.1, vy.fromFin ij.2)
toFin (a, b) h :=
  finProdFinEquiv (vx.toFin a h.1, vy.toFin b h.2)
```

### HTuple zero-origin ranges

For zero-origin tuple ranges:

```lean
def Fold.finViewZeroHTuple (shape : HTuple Nat p) :
    Fold.FinRangeView ((0 : HTuple Nat p)...shape)
```

Use the existing equivalences:

```lean
FinHTuple.equivZeroRange
FinHTuple.equivFin
FinHTuple.zeroRangeEquivFlatFin
```

Recommended public names:

```lean
Fold.fold_zeroHTuple_eq_fin_foldl
Fold.sum_zeroHTuple_eq_fin_sum
Fold.prod_zeroHTuple_eq_fin_prod
Fold.entries_zeroHTuple_eq_finRange
```

### HTuple product ranges

Use existing `htupleProdRangeIso` as the order-preserving bridge between:

```lean
((lo₀, lo₁)...(hi₀, hi₁))
((lo₀.prod lo₁)...(hi₀.prod hi₁))
```

Add theorem forms that do not force users to manipulate `RangeIso` directly:

```lean
theorem Fold.fold_htuple_pair_eq_fold_htuple_prod
theorem Fold.entries_htuple_pair_eq_entries_htuple_prod
theorem Fold.finView_htuple_prod_eq_product_view
```

## Membership And Simplification Suite

Add a small set of canonical membership lemmas and choose stable simp normal forms.

Recommended normal forms:

- Zero-origin HTuple membership normalizes to `<ₑ`.
- General HTuple membership normalizes to `≤ₑ` and `<ₑ`.
- Leaf HTuple membership normalizes to scalar membership or scalar inequalities.
- Product membership normalizes to component membership.

Suggested lemmas:

```lean
@[simp] theorem HTuple.Range.mem_zero_iff_lt
@[simp] theorem HTuple.Range.mem_leaf_iff
@[simp] theorem HTuple.Range.mem_zero_leaf_iff
@[simp] theorem HTuple.Range.mem_prod_iff
@[simp] theorem HTuple.Range.mem_zero_prod_iff
```

Be careful not to create simp loops between `Valid`, membership, and elementwise order. Pick one direction as the normal form.

## Layout Range API Improvements

The fold-to-Fin API will not fully clean tensor proofs unless layout range inverses also simplify well.

Add or wrap these theorem shapes:

```lean
@[simp] theorem FinHTupleMap.mem_rangeNat_id_iff
@[simp] theorem FinHTupleMap.rangeNatInv_id

@[simp] theorem FinHTupleMap.mem_rangeNat_contiguous1D_iff
@[simp] theorem FinHTupleMap.rangeNatInv_contiguous1D

@[simp] theorem FinHTupleMap.coe_rowMajorMap
@[simp] theorem FinHTupleMap.rangeNatInv_rowMajorIndex'
```

The intended downstream proof style should be:

```lean
rw [get_tensorAxpy]
simp
```

not:

```lean
by_cases hi : idx ∈ map.rangeNat
  have hinv := map.eval_rangeNatInv idx hi
  ...
else
  exfalso
  exact hi manual_membership
```

## Relationship To Existing Notes

This plan complements:

- `ai/notes/fold_reasoning.md`
- `ai/notes/fold_extensional_resoning.md`
- `ai/notes/tensor_algebra_fold_bridge_plan.md`
- `ai/notes/vector_algebra_fold_reductions.md`

The earlier notes focus on existing range relationships and tensor fold bridges. This note proposes the next user-facing API layer: finite-index views and simplification wrappers.

## Implementation Order

### Phase 1: Core finite range view

1. Add `NumLean/Interfaces/Fold/Fin.lean`.
2. Define `Fold.FinRangeView`.
3. Prove `fold_eq_fin_foldl`.
4. Add entries and round-trip simp lemmas.
5. Import the new module from `NumLean/Interfaces/Fold.lean`.

### Phase 2: Scalar views

1. Add `Fold.finViewZeroNat`.
2. Add `Fold.finViewNat`.
3. Add `Fold.finViewInt`.
4. Add regression tests showing `Fold.fold` rewrites to `Fin.foldl`.

### Phase 3: HTuple zero-origin view

1. Add `Fold.finViewZeroHTuple` using `FinHTuple.zeroRangeEquivFlatFin`.
2. Add fold/sum/product wrappers over `Fin shape.numel`.
3. Replace local bespoke leaf/zero-range sum proofs where possible.

### Phase 4: Product views

1. Add `Fold.FinRangeView.prod`.
2. Add direct product fold-to-`Fin.foldl` theorem.
3. Add iterated sum/fold theorem wrappers.
4. Add HTuple pair-vs-prod fold theorem using `htupleProdRangeIso`.

### Phase 5: Membership simp suite

1. Add HTuple range membership normal forms.
2. Add product membership normal forms.
3. Add tests that `simp` proves common membership goals.

### Phase 6: Layout range simplification

1. Add identity layout `rangeNat` and `rangeNatInv` simp lemmas.
2. Add contiguous layout `rangeNat` and `rangeNatInv` simp lemmas.
3. Add row-major coercion and inverse wrappers.
4. Refactor tensor algebra proof hotspots to use these lemmas.

### Phase 7: Unify traversal stacks

1. Make `Fold` the canonical no-break API.
2. Bridge or deprecate `Meta.ForAll` no-break classes.
3. Keep `RangeIterator`/`ForIn'` for monadic and breakable loops.
4. Add missing lawful `Fold` instances for Vector ranges if needed.

## Regression Tests To Add

Add a focused test file, for example `Tests/FoldFin.lean`, with examples like:

```lean
example (n : Nat) :
    Fold.fold (0...n : Std.Rco Nat) init f =
      Fin.foldl n (fun acc i => f i i.isLt' acc) init := by
  rw [Fold.fold_zeroNat_eq_fin_foldl]

example (shape : HTuple Nat p) :
    Fold.fold ((0 : HTuple Nat p)...shape) init f =
      Fin.foldl shape.numel (fun acc i => ...) init := by
  rw [Fold.fold_zeroHTuple_eq_fin_foldl]

example :
    Fold.fold ((lo₀, lo₁)...(hi₀, hi₁)) init f =
      Fold.fold ((lo₀.prod lo₁)...(hi₀.prod hi₁)) init g := by
  rw [Fold.fold_htuple_pair_eq_fold_htuple_prod]
```

Also test that `simp` handles:

```lean
idx ∈ ((0 : HTuple Nat p)...shape)
h(i) ∈ (h(0)...h(n) : Std.Rco (HTuple Nat .leaf))
i.rowMajorIndex shape ∈ (FinHTupleMap.rowMajorMap shape).rangeNat
(Layout.id h(n)).rangeNatInv i h
```

## Non-goals

- Do not add global coercions from `Nat` to bounded index types.
- Do not expose `FinRangeView` as a typeclass until there is a concrete need; explicit view values are more predictable.
- Do not replace `RangeIso`, `RangeEquiv`, or `RangeEmbedding`; the finite view should sit on top of them for common finite-index workflows.
- Do not make `simp` unfold large executable folds. Use small bridge lemmas and stable normal forms instead.
