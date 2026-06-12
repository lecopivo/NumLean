# TensorSliceMap Refactor Plan

## Goal

Make `TensorSliceMap` a precise, proof-friendly API for embedding one tensor-shaped index space into another flat index space using:

- a base offset `ioffset`
- target strides `istrides`
- proof that produced target indices are in bounds
- proof that the stride layout is injective on the source tensor index space

## Current Issues

1. `TensorSliceMap` is missing `ioffset : Nat`.

   Slice offsets should be computed as:

   ```lean
   ioffset + jt.offset istrides
   ```

   not only:

   ```lean
   jt.offset istrides
   ```

2. `ValidStrides` proves injectivity, not bounds.

   Current:

   ```lean
   istrides_valid : TensorIndex.ValidStrides jdims istrides
   ```

   This proves that two distinct source tensor indices do not map to the same offset.

   It does not prove:

   ```lean
   ioffset + jt.offset istrides < nI
   ```

3. `TensorIndexTypeOfRank` needs a size invariant.

   It should state that the index type size matches the tensor shape:

   ```lean
   n = TensorIndex.numel dims
   ```

4. `toTensorIndex` and `fromTensorIndex` should be an equivalence.

   Current fields are independent functions:

   ```lean
   toTensorIndex : I → TensorIndex dims
   fromTensorIndex : TensorIndex dims → I
   ```

   Prefer:

   ```lean
   tensorEquiv : I ≃ TensorIndex dims
   ```

5. `jstrides` is likely redundant.

   If `J` has a `TensorIndexType`, its dense strides and axis order should come from the instance.

## Proposed API

### `TensorIndexTypeOfRank`

Replace the current conversion fields with an equivalence:

```lean
class TensorIndexTypeOfRank (I : Type u) (n : outParam Nat)
    (rank : Nat) (dims : outParam (Vector Nat rank))
    (axis : outParam (TensorIndex.AxisOrder rank))
    extends IndexType I n where

  n_eq_numel : n = TensorIndex.numel dims

  tensorEquiv : I ≃ TensorIndex dims

  toFin_eq_offset :
    ∀ i : I,
      (toFin i).1 =
        (tensorEquiv i).offset
          (TensorIndex.denseStridesForOrder dims axis)
```

Then define helpers:

```lean
def toTensorIndex [TensorIndexTypeOfRank I n rank dims axis] :
    I → TensorIndex dims :=
  TensorIndexTypeOfRank.tensorEquiv

def fromTensorIndex [TensorIndexTypeOfRank I n rank dims axis] :
    TensorIndex dims → I :=
  TensorIndexTypeOfRank.tensorEquiv.symm
```

### Dense Offset Bound

Expose this theorem from `TensorIndex/Dense.lean`:

```lean
theorem offset_denseStridesForOrder_lt_numel
    {rank : Nat} {dims : Vector Nat rank}
    (axis : TensorIndex.AxisOrder rank)
    (idx : TensorIndex dims) :
    idx.offset (TensorIndex.denseStridesForOrder dims axis) <
      TensorIndex.numel dims
```

This supports constructing `Fin n` from a tensor index when combined with `n_eq_numel`.

## Proposed `TensorSliceMap`

```lean
structure TensorSliceMap
    (J I : Type u)
    {nJ nI}
    {jrank : Nat}
    {jdims : Vector Nat jrank}
    {jaxis : TensorIndex.AxisOrder jrank}
    [TensorIndexType J nJ jrank jdims jaxis]
    [IndexType I nI] where

  ioffset : Nat

  istrides : Vector Nat jrank

  istrides_valid :
    TensorIndex.ValidStrides jdims istrides

  in_bounds :
    ∀ jt : TensorIndex jdims,
      ioffset + jt.offset istrides < nI
```

Then define the induced map instead of storing it:

```lean
def TensorSliceMap.toFun
    (m : TensorSliceMap J I) : J → I :=
  fun j =>
    let jt := TensorIndexType.toTensorIndex j
    fromFin ⟨m.ioffset + jt.offset m.istrides, m.in_bounds jt⟩
```

If performance requires a specialized implementation, add it as an optional cached field later:

```lean
map : J → I
map_eq_toFun : map = toFun
```

But the default should be definitional and proof-friendly.

## Important Lemmas

### Offset Injectivity With Base Offset

```lean
theorem offset_injective_with_base
    (h : TensorIndex.ValidStrides dims strides) :
    Function.Injective
      (fun idx : TensorIndex dims => base + idx.offset strides)
```

Reason:

```lean
base + a = base + b → a = b
```

then use `ValidStrides`.

### Slice Map Injectivity

```lean
theorem TensorSliceMap.injective
    (m : TensorSliceMap J I) :
    Function.Injective m.toFun
```

Proof outline:

1. Convert equality in `I` to equality in `Fin nI` via `toFin`.
2. Use `IndexType.toFin_fromFin`.
3. Cancel `ioffset`.
4. Use `istrides_valid`.
5. Use `TensorIndexType.tensorEquiv.injective`.

## Constructors

### Identity Slice

Create the identity slice map:

```lean
def TensorSliceMap.id
    (I : Type u)
    {n rank dims axis}
    [TensorIndexType I n rank dims axis] :
    TensorSliceMap I I :=
  ...
```

Expected fields:

```lean
ioffset := 0
istrides := TensorIndex.denseStridesForOrder dims axis
```

Proof obligations:

- `istrides_valid` follows from `validStrides_denseStridesForOrder`.
- `in_bounds` follows from `offset_denseStridesForOrder_lt_numel` and `n_eq_numel`.

### Product Slice: Left Injection

Create a slice embedding `I → I × J` by fixing the `J` component at its first/zero index.

```lean
def TensorSliceMap.prodLeft
    (I J : Type u)
    {nI nJ irank idims iaxis jrank jdims jaxis}
    [TensorIndexType I nI irank idims iaxis]
    [TensorIndexType J nJ jrank jdims jaxis] :
    TensorSliceMap I (I × J) :=
  ...
```

For the existing row-major `IndexType` instance on products, `I × J` linearization is:

```lean
iOffsetInProduct = iOffset * nJ + jOffset
```

So the left slice should use:

```lean
ioffset := 0
istrides := nJ • denseStridesForOrder idims iaxis
```

where scalar multiplication on strides means:

```lean
Vector.ofFn fun k => nJ * (TensorIndex.denseStridesForOrder idims iaxis)[k]
```

Proof obligations:

- `ValidStrides` is preserved by multiplying all strides by a positive scalar.
- `nJ > 0` is needed unless `I` is empty; this usually follows from `nJ = numel jdims` and inhabited index assumptions, or should be carried as a constructor hypothesis when needed.
- Bounds follow from product-size arithmetic.

### Product Slice: Right Injection

Create a slice embedding `J → I × J` by fixing the `I` component at its first/zero index.

```lean
def TensorSliceMap.prodRight
    (I J : Type u)
    {nI nJ irank idims iaxis jrank jdims jaxis}
    [TensorIndexType I nI irank idims iaxis]
    [TensorIndexType J nJ jrank jdims jaxis] :
    TensorSliceMap J (I × J) :=
  ...
```

Expected fields:

```lean
ioffset := 0
istrides := TensorIndex.denseStridesForOrder jdims jaxis
```

This is because the right component is the contiguous innermost block in the existing row-major product encoding.

### Swapped Product Slice

Also provide constructors for `I → J × I` and `J → J × I` by reusing the product constructors with swapped arguments:

```lean
def TensorSliceMap.prodLeftSwap  -- I → J × I
def TensorSliceMap.prodRightSwap -- J → J × I
```

These are useful because product order changes the flat offset formula.

### Lift Existing Slice Through Product: Left Factor

Given a slice map:

```lean
s : TensorSliceMap I I'
```

construct:

```lean
TensorSliceMap.prodMapLeft s J : TensorSliceMap I (I' × J)
```

This lifts the target offset through the left side of a product:

```lean
ioffset := s.ioffset * nJ
istrides := nJ • s.istrides
```

Proof obligations:

- `ValidStrides` is preserved by positive scalar multiplication.
- `in_bounds` follows from `s.in_bounds` and product-size bounds.

### Lift Existing Slice Through Product: Right Factor

Given:

```lean
s : TensorSliceMap I I'
```

construct:

```lean
TensorSliceMap.prodMapRight J s : TensorSliceMap I (J × I')
```

This embeds into the right product factor:

```lean
ioffset := s.ioffset
istrides := s.istrides
```

because the right factor is innermost in row-major product encoding.

Bounds use:

```lean
s.ioffset + jt.offset s.istrides < nI'
```

and therefore:

```lean
s.ioffset + jt.offset s.istrides < nJ * nI'
```

assuming `0 < nJ`.

### Endpoint-Based Slice Constructor

Provide a constructor that builds a one-dimensional or rank-polymorphic slice map from explicit endpoints.

For one-dimensional slices:

```lean
def TensorSliceMap.interval
    (I : Type u)
    {nI}
    [IndexType I nI]
    (start stop step : Nat)
    (hstep : 0 < step)
    (hbounds : start + (stop - 1) * step < nI) :
    TensorSliceMap (Fin stop) I :=
  ...
```

Expected fields:

```lean
ioffset := start
istrides := #[step]
```

For a rank-polymorphic box slice, use:

```lean
def TensorSliceMap.box
    (I : Type u)
    {nI rank}
    [IndexType I nI]
    (dims : Vector Nat rank)
    (ioffset : Nat)
    (istrides : Vector Nat rank)
    (hvalid : TensorIndex.ValidStrides dims istrides)
    (hbounds : ∀ idx : TensorIndex dims,
      ioffset + idx.offset istrides < nI) :
    TensorSliceMap (TensorIndex dims) I :=
  ...
```

This constructor is the most general low-level entry point. Endpoint-specific constructors should elaborate down to this form.

## Implementation Steps

1. Add theorem in `TensorIndex/Dense.lean`:

   ```lean
   offset_denseStridesForOrder_lt_numel
   ```

2. Refactor `TensorIndexTypeOfRank`.

   Add:

   ```lean
   n_eq_numel
   tensorEquiv
   toFin_eq_offset
   ```

   Remove or deprecate independent `toTensorIndex`/`fromTensorIndex` fields.

3. Add helper definitions:

   ```lean
   TensorIndexType.toTensorIndex
   TensorIndexType.fromTensorIndex
   ```

4. Refactor `TensorSliceMap`.

   Add:

   ```lean
   ioffset
   in_bounds
   ```

   Remove:

   ```lean
   jstrides
   map_valid with sorry reconstruction
   ```

5. Define:

   ```lean
   TensorSliceMap.toFun
   ```

6. Prove:

   ```lean
   offset_injective_with_base
   TensorSliceMap.injective
   ValidStrides.scale
   ```

7. Add constructors:

   ```lean
   TensorSliceMap.id
   TensorSliceMap.prodLeft
   TensorSliceMap.prodRight
   TensorSliceMap.prodMapLeft
   TensorSliceMap.prodMapRight
   TensorSliceMap.interval
   TensorSliceMap.box
   ```

8. Build:

   ```bash
   lake build NumLean.Data.TensorIndex.Basic \
              NumLean.Data.TensorIndex.Dense \
              NumLean.Data.TensorIndex.SliceMap
   ```

## Open Questions

1. Should `TensorSliceMap` store `map : J → I` for performance, or should `toFun` always be computed from fields?

2. Should `TensorSliceMap` target only flat `IndexType I nI`, or should target `I` also be a `TensorIndexType` with its own dimensions?

3. Do we want `TensorSliceMap` to support nonzero source offset too, or only target base offset `ioffset`?
