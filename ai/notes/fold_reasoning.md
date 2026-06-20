# Fold Reasoning Status

This document tracks the fold/range reasoning infrastructure for NumLean: the goal, what exists,
what is still missing, and what is intentionally deferred.

## Goal

The goal is to make tensor-loop rewrites algebraic and compositional.

The intended workflow is:

1. Express a loop domain as a folded range.
2. Prove a relationship between the source range and the target range.
3. Transport the fold across that relationship.
4. Use commutativity or guards only when the range relationship requires them.

There are three range relationships:

- `Fold.RangeIso xs ys`: ordered bijection. Fold order is preserved, so no commutativity or guard is needed.
- `Fold.RangeEquiv xs ys`: unordered bijection/permutation. Fold equality requires pairwise commutation.
- `Fold.RangeEmbedding xs ys`: injective embedding into a larger range. Fold equality requires a guard and a neutral branch for target entries outside the embedded image.

This should support loop merging/splitting, product folds, row-major flattening, padded tiling, future blocked matrix traversals, scatter-to-gather-style reorderings, and im2col-style domain rewrites.

## What We Have

### Core Fold Interfaces

Implemented in `NumLean/Interfaces/Fold/Basic.lean`:

- `Fold`
- `LawfulFold`
- `LawfulFold.mem_entries`
- `LawfulFold.entries_nodup`

`Fold.entries` is the canonical list order for a folded range. `LawfulFold` is proof-only:
it records coverage, no-duplicates, and equivalence between executable `Fold.fold` and
`Fold.entries.foldl`.

### Commuting Fold Lemmas

Implemented in `NumLean/Interfaces/Fold/Commute.lean`:

- `Fold.ListPairwiseCommutes`
- `Fold.ListPairwiseCommutesDistinct`
- `Fold.PairwiseCommutes`
- `Fold.List.Perm.of_nodup_of_forall_mem_iff`
- fold equality under `List.Perm` and pairwise commutation
- `LawfulFold.fold_eq_foldl_perm_of_pairwise_commutes`

These are the core lemmas for `RangeEquiv` fold transport.

### Range Isomorphisms And Equivalences

Implemented in `NumLean/Interfaces/Fold/RangeIso.lean`:

- `Fold.RangeEquiv`, extending a subtype equivalence.
- `Fold.RangeIso`, extending `RangeEquiv` with ordered `entries_eq`.
- `Fold.RangeEquiv.ofSubtypeEquiv`.
- `Fold.RangeEquiv.ofSubtypeEquivAll`, which derives `entries_perm` from the subtype equivalence and lawful entries.
- `Fold.RangeEquiv.refl`, `symm`, `trans`.
- `Fold.RangeIso.ofSubtypeEquiv`.
- `Fold.RangeIso.refl`, `symm`, `trans`.
- `Fold.RangeIso.fold_eq`.
- `Fold.RangeEquiv.fold_eq_of_pairwise_commutes`.

This means most new range equivalence proofs can start from a subtype equivalence.

### Range Embeddings

Implemented in `NumLean/Interfaces/Fold/Embedding.lean`:

```lean
structure Fold.RangeEmbedding (xs : ρ) (ys : σ) where
  toFun : {a : α // a ∈ xs} → {b : β // b ∈ ys}
  guard : (b : β) → b ∈ ys → Prop
  guard_decidable : ∀ b hb, Decidable (guard b hb)
  guard_toFun : ∀ a, guard (toFun a).1 (toFun a).2
  invFun : (b : β) → (hb : b ∈ ys) → guard b hb → {a : α // a ∈ xs}
  right_inv : ∀ b hb h, toFun (invFun b hb h) = ⟨b, hb⟩
  left_inv : ∀ a, invFun (toFun a).1 (toFun a).2 (guard_toFun a) = a
```

Also implemented:

- decidability instance for `e.guard b hb`.
- `Fold.RangeEmbedding.refl`.
- `Fold.RangeEmbedding.ofRangeIso`.
- `Fold.RangeEmbedding.toFun_injective`.
- `Fold.RangeEmbedding.trans`.

Ordered guarded embeddings are implemented as:

- `Fold.RangeMonoEmbedding`, extending `RangeEmbedding` with an entry-order law:
  guarded target entries, mapped back through `invFun`, are exactly source entries in order.
- `Fold.RangeMonoEmbedding.refl`.
- `Fold.RangeMonoEmbedding.ofRangeIso`.
- `Fold.RangeMonoEmbedding.fold_eq_guarded`.

The guard is positive: it means a target point is in the embedded source image. This makes padded-domain folds natural:

```lean
if h : e.guard b hb then
  sourceStep (e.invFun b hb h) acc
else
  acc
```

### Product Order And Product Folds

Implemented in `NumLean/Data/Prod/Order.lean`:

- recursive `ElementwiseLT` / `ElementwiseLE` for products;
- recursive `LexLT` / `LexLE` for products;
- recursive `ColexLT` / `ColexLE` for products;
- product `LT` / `LE` as recursive row-major lexicographic order;
- `grind_prod_order` facts.

Implemented in `NumLean/Data/Prod/Fold.lean`:

- rectangular product range membership;
- `Fold.mem_rco_prod_iff`;
- `Fold.prodEntry`;
- `Fold.prodEntries`;
- product `Fold` instance;
- lawful product `Fold` instance;
- `Fold.fold_rco_prod_eq_outer_inner`.

Important distinction:

- Product `LT`/`LE` is lexicographic.
- Product `Std.Rco` membership for folds is rectangular and componentwise.

### HTuple Fold And Product Bridge

Implemented in `NumLean/Data/HTuple/Fold.lean`:

- `foldHTuple`.
- `foldHTupleEntries`.
- `foldHTuple_eq_foldl`.
- `entries_htuple_prod`.
- `fold_htuple_prod_eq_outer_inner`.
- `htupleProdRangeIso` between product ranges of HTuples and HTuple product ranges.
- `Fold` and lawful `LawfulFold` instances for HTuple ranges.

### FinHTuple Range Bridges

Implemented in `NumLean/Data/FinHTuple/Basic.lean`:

- `FinHTuple.equivZeroRange`:
  ```lean
  {idx : HTuple Nat p // idx ∈ (0...ns)} ≃ FinHTuple ns
  ```
- `FinHTuple.zeroRangeEquivFlatFin`:
  ```lean
  {idx : HTuple Nat p // idx ∈ (0...ns)} ≃ Fin ns.numel
  ```

Implemented in `NumLean/Interfaces/Fold/RcoNative.lean`:

- `finEquivZeroRange`:
  ```lean
  Fin n ≃ {i : Nat // i ∈ (0...n : Std.Rco Nat)}
  ```

Implemented in `NumLean/Data/FinHTuple/Fold.lean`:

- `FinHTuple.zeroRangeEquivFin`:
  ```lean
  {idx : HTuple Nat p // idx ∈ (0...ns)} ≃ {i : Nat // i ∈ (0...ns.numel)}
  ```
- `FinHTuple.zeroRangeRangeEquivFin`:
  ```lean
  Fold.RangeEquiv (0...ns) (0...ns.numel)
  ```
- `FinHTuple.zeroRangeRangeIsoFin`:
  ```lean
  Fold.RangeIso (0...ns) (0...ns.numel)
  ```

This gives both unordered and ordered row-major flatten/unflatten bridges.

### Verified Tensor Sandbox

Implemented in `NumLean/Misc/VerifiedTensor.lean`:

- theorem wrappers for `RangeIso.fold_eq` and `RangeEquiv.fold_eq_of_pairwise_commutes`;
- product fold merge statement;
- HTuple flatten/unflatten range equivalence statement;
- placeholders for tile/tail, padded rectangular tiling, guarded extension, scatter-to-gather, and im2col.

This file is a theorem-target sandbox, not production infrastructure.

## What Is Missing

### Fold Transport For Embeddings

Ordered guarded fold transport exists for `RangeMonoEmbedding`:

Target shape:

```lean
Fold.fold xs init f =
  Fold.fold ys init fun b hb acc =>
    if h : e.guard b hb then
      f (e.invFun b hb h).1 (e.invFun b hb h).2 acc
    else
      acc
```

This does not require commutativity because `RangeMonoEmbedding` records that the guarded target entries are in source order.

Still missing: unordered guarded fold transport for plain `RangeEmbedding`. That theorem should require a permutation/commutation condition.

### Scalar Tiling APIs

Exact full-blocks-plus-tail tiling is still missing.

Desired decomposition:

```lean
0...n ≃ ((0...k) × (0...(n / k))) ⊕ (0...(n % k))
```

This is deferred because the Sum/tail range API is not settled.

Padded rectangular tiling is also missing.

Desired embedding:

```lean
0...n ≲ (0...ceil(n / k)) × (0...k)
```

with index map:

```lean
tileIndex (block, inner) = block * k + inner
```

and positive guard:

```lean
block * k + inner < n
```

For generated code, a useful equivalent padded-entry test is:

```lean
n % k ≠ 0 ∧ block = ((n + k - 1) / k) - 1 ∧ n % k ≤ inner
```

The neutral branch is taken when that padded-entry test holds.

### Guarded Extension Theorem

The general theorem for extending a fold over `lo...hi` to a larger `lo'...hi'` with neutral behavior outside the original range is still missing.

This should probably be expressed using `RangeEmbedding` rather than a separate ad hoc API.

### Sum/Tail Ranges

No Sum range API exists yet.

This is intentionally deferred. It impacts exact tile-tail decompositions.

### Hoisting And Im2col

The range-domain part should be covered by `RangeIso`, `RangeEquiv`, `RangeEmbedding`, product folds, and HTuple flattening.

Still missing:

- expression-level independence lemmas;
- let-hoisting rewrites;
- concrete theorem statements beyond placeholders in `VerifiedTensor.lean`.

## Deferred Design Choices

These are intentionally not being implemented yet:

- Sum range API.
- General transpose/reorder range equivalences.
- General filter/guard range API beyond `RangeEmbedding`.
- `reverseSlice` and `transposeSlice` semantic proofs.

## Recommended Next Steps

1. Use `RangeMonoEmbedding.fold_eq_guarded` to implement the first concrete guarded transformation.
2. Implement scalar padded rectangular tiling as a concrete `RangeMonoEmbedding`.
3. Only after that, revisit Sum/tail ranges for exact full-blocks-plus-tail tiling.
