# Vector Algebra Fold Reductions

Goal: prove the `Vector/VectorAlgebra/*` reference implementations reduce to extensional RHS forms using:

- `Fold.fold_eq_sum`
- `Fold.fold_eq_vector_map`
- `FoldMap.foldl_get_eq_foldl_filter_affectors` where needed

## Step 1: Refactor Vector Algebra To Rank-1 Maps

Before investing more proof work into the current `off/inc` API, restate all `VectorAlgebra`
operations using rank-1 `FinHTupleMap`s:

```lean
xmap : FinHTupleMap h(len) h(n)
```

instead of:

```lean
xoff xinc : Nat
hx : xoff + len * xinc <= n ∧ xinc ≠ 0
```

For read-only operands, require only the map:

```lean
(xs : Vector K n) (xmap : FinHTupleMap h(len) h(n))
```

For written operands, require injectivity:

```lean
(ys : Vector K m) (ymap : FinHTupleMap h(len) h(m))
(hymap : ymap.Injective)
```

This makes `VectorAlgebra` the rank-1 specialization of `TensorAlgebra`, with `shape = h(len)`.

Example signatures:

```lean
def vectorSum [Add K] [Zero K] {n : Nat} {len : Nat}
    (xs : Vector K n) (xmap : FinHTupleMap h(len) h(n)) : K

def vectorAxpy [Add K] [Mul K] {m n : Nat} {len : Nat}
    (a : K)
    (xs : Vector K n) (xmap : FinHTupleMap h(len) h(n))
    (ys : Vector K m) (ymap : FinHTupleMap h(len) h(m))
    (hymap : ymap.Injective) : Vector K m
```

For matrix-vector operations, use rank-1 row/column shapes:

```lean
def vectorGemv [Add K] [Mul K] [Zero K]
    {an xn yn : Nat} {rows cols : Nat}
    (alpha beta : K)
    (A : Vector K an) (amap : FinHTupleMap (.prod h(rows) h(cols)) h(an))
    (x : Vector K xn) (xmap : FinHTupleMap h(cols) h(xn))
    (y : Vector K yn) (ymap : FinHTupleMap h(rows) h(yn))
    (hymap : ymap.Injective) : Vector K yn
```

Add strided convenience constructors/wrappers separately, instead of making striding the core API:

```lean
def FinHTupleMap.strided1D
def FinHTupleMap.contiguous1D
def FinHTupleMap.broadcast1D
```

Then optional wrappers can expose BLAS-style arguments:

```lean
def vectorAxpyStrided ... :=
  vectorAxpy a xs (FinHTupleMap.strided1D ...) ys (FinHTupleMap.strided1D ...) ...
```

Benefits:

- Removes repeated arithmetic bounds from signatures.
- Uses `map.Injective` as the exact write-safety condition.
- Allows read broadcasting naturally, because read maps need not be injective.
- Makes vector proofs align with tensor proofs.
- Avoids proving `stride_injective` for every vector update theorem.

## Scalar Reductions

Use `Fold.fold_eq_sum` for reductions whose implementation is a `for_all` over an accumulator.

Prove:

- `vectorSum_eq_sum`
- `vectorDot_eq_sum`
- `vectorProd_eq_prod` if an analogous multiplicative fold lemma is added, otherwise postpone or prove separately by a local multiplicative analogue.

Expected shape for `vectorSum` after the map refactor:

```lean
theorem vectorSum_eq_sum [AddCommMonoid K] ... :
  vectorSum xs xmap =
    0 + ∑ i ∈ (NumLean.entries _ (0...h(len))).toFinset,
      xs[xmap i.1]
```

Expected shape for `vectorDot` after the map refactor:

```lean
theorem vectorDot_eq_sum [AddCommMonoid K] [Mul K] ... :
  vectorDot xs xmap ys ymap =
    0 + ∑ i ∈ (NumLean.entries _ (0...h(len))).toFinset,
      xs[xmap i.1] * ys[ymap i.1]
```

## Single-Slice Vector Updates

Use `Fold.fold_eq_vector_map` for operations writing to one mapped destination slice.

After the map refactor, the injectivity obligation comes directly from the API:

```lean
hymap : ymap.Injective
```

Then prove extensional map reductions for:

- `vectorScal`
- `vectorNeg`
- `vectorInv`
- `vectorMul`
- `vectorSub`
- `vectorDiv`
- `vectorAxpy`

Expected RHS shape:

```lean
init.mapFinIdx fun j xj _ =>
  if h : ∃ i, ∃ hi : i ∈ (0...h(len)), (ymap i).toScalar = j then
    let i := choose h
    let hi := choose (choose_spec h)
    ... xj ...
  else
    xj
```

## `vectorGemv`

This should be provable after the map refactor.

Proof strategy:

1. Use `Fold.fold_eq_sum` on the inner `cols` loop to reduce the mutable `acc` loop.
2. Use `Fold.fold_eq_vector_map` on the outer `rows` loop over writes through `ymap`.
3. The inner loop does not mutate `y`, only `acc`, so the outer proof should fit the vector-map theorem.

Expected RHS shape:

```lean
y.mapFinIdx fun j yj _ =>
  if h : ∃ i, ∃ hi : i ∈ (0...h(rows)), (ymap i).toScalar = j then
    let i := choose h
    let hi := choose (choose_spec h)
    alpha *
      (0 + ∑ k ∈ (NumLean.entries _ (0...h(cols))).toFinset,
        A[amap (i.prod k.1)] * x[xmap k.1]) +
      beta * yj
  else
    yj
```

## Postpone

### `vectorGer`

For `vectorGer`, the map-refactored API should require:

```lean
hamap : amap.Injective
```

That should make `Fold.fold_eq_vector_map` applicable to the matrix update. Without such a hypothesis,
aliasing is possible for arbitrary layouts. To prove `vectorGer`, the API needs either:

- an explicit matrix-write injectivity hypothesis, or
- a stronger structured layout condition.

### `vectorGemm`

Postpone. A clean proof needs an API theorem to fuse/product two outer ranges into one range so `Fold.fold_eq_vector_map` can see the combined write map.

## Build Checks

After implementation:

```bash
lake build NumLean.Data.Vector.VectorAlgebra
lake build NumLean
```
