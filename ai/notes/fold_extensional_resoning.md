# Fold Extensional Reasoning Notes

This file tracks the attempt to rewrite tensor-op proofs into the local fold-extensional style:
extensionalize a read, filter the fold to the entries that can affect that read, leave the
filtered-entry characterization as the only hard combinatorial fact, and finish by computing a
short `List.foldl`.

## Conventions

- Prefer a local bridge from an entry subtype to `FinHTuple shape` instead of repeatedly proving
  raw `HTuple` bounds inline.
- Avoid repeated `convert` or broad `change`; if a fold has to be exposed, do it once near the
  start and then keep the rest of the proof in named local definitions.
- The intended skipped facts have this shape:
  `have hEntries : entries.filter affects = [...] := by sorry`.
- After rewriting by `hEntries`, the proof should be only `List.foldl_cons`, `List.foldl_nil`,
  and local read lemmas for `setElem`/`swap`.

## Current Hypotheses

- `copySlice` should be singleton/empty: a scalar destination is written by at most one entry by
  injectivity of the destination map.
- `swapSlice` should be singleton/empty for each side: for `fst[i]`, only the entry whose `xmap`
  is `i` can write it; for `snd[i]`, only the entry whose `ymap` is `i` can write it.
- `reverseSlice` likely wants singleton/empty, not two entries. The loop only visits the lower
  half, so exactly one of `target` and `reverse target` should be an actual loop entry when the
  target is moved. The middle/fixed point case should filter to empty or a no-op singleton.
- `transposeSlice` likely wants a two-entry filtered list for off-diagonal positions. Both
  `(i,j)` and `(j,i)` are loop entries, but exactly one guarded swap fires because only one of
  `ij < ji` and `ji < ij` is true.

## Pain Points

- There are three nearby index representations: raw `HTuple Nat p`, `FinHTuple shape`, and
  `{ i : HTuple Nat p // i ∈ 0...shape }`. The best local normal form is usually `FinHTuple` for
  map application and a subtype entry only at the fold boundary.
- `FinHTupleMap` application with a `FinHTuple` is currently raw function application, while
  bounded `GetElem` notation also exists. Proofs are cleaner if they choose one representation
  locally and avoid switching.
- Product-state `swapSlice` proofs should use the generic `FoldMap.foldl_get_eq_foldl_filter_affectors`
  over an explicit read function, not the vector-only wrapper.

## Attempt Notes

- `CopySlice.lean`: the in-range proof already has the desired shape. The out-of-range proof was
  converted from the older `foldl_write_get_of_not_mem_range` induction style to the same
  extensional-filter style, with the filtered list asserted empty.
- `ReverseSlice.lean`: trying to define the active entry by projecting `target.val` was the wrong
  direction because `HTuple` does not expose product `.fst`/`.snd` projections. The better local
  shape is to treat the active entry construction as part of the skipped range/filter fact.
- `ReverseSlice.lean`: singleton reasoning is still the intended shape. A two-entry proof would not
  match the loop domain because only the lower-half representative is an executable entry.
- `TransposeSlice.lean`: two-entry reasoning is the natural shape. The filtered entries are either
  `[target, transpose target]` or `[transpose target, target]`; then the `<` guard decides which of
  the two entries performs the swap.
- `TransposeSlice.lean`: using `Fold.entries` directly for
  `Std.Rco (HTuple Nat (.prod r r))` left a universe metavariable in the theorem body even with
  explicit `ρ`/`α` annotations. For now the proof skeleton uses an explicitly typed local entry
  list placeholder and puts the real nested-to-product/filter transport inside `hExt := by sorry`.
  This should be revisited; a named helper for product-shaped HTuple entries would likely avoid
  this entirely.
- `SwapSlice.lean`: directly applying the generic pair-state affector lemma creates a side-indexed
  dependency relation (`fst i`/`snd j`). For readability, the theorem body records that as a local
  `hExt` fact and then focuses on the singleton/empty filtered fold computation.
- `SwapSlice.lean`: exposing the elaborated `do` loop with `change` was fragile. The final skeleton
  defines a clean local `step` over entries using `FinHTuple.equivZeroRange` and leaves equality to
  the executable loop as the local `hExt` fact.

## API Notes From The Attempt

- A small helper turning an entry `{idx // idx ∈ 0...shape}` into `FinHTuple shape` would remove a
  lot of noise from `copySlice` and `swapSlice` proofs.
- For product-shaped `HTuple`s, if we often need to go from `FinHTuple (.prod a b)` to its two
  components, using `FinHTuple.prodEquiv` explicitly may be better than adding projections.
- For `swapSlice`, a specialized pair-state read/filter lemma could be worthwhile later, but the
  current local `hExt` shape is probably enough until more proofs need it.
- For product-shaped `HTuple` folds, we may want a named `productEntries` wrapper with fixed
  universe parameters and the exact subtype type expected by tensor proofs.
