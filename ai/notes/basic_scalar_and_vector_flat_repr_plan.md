# Basic Scalar + Vector Flat-Repr Plan

The goal is to provide correct, efficient implementations of scalar and flat-vector interfaces for
basic types: `Float32`, `Float`, `Complex32`, `Complex64`, and `UInt8`.

All scalar code should live under `NumLean/Data/Scalars/`.

## Required Layout

For each scalar family, use the following structure, e.g. `Complex32/`:

- `Basic.lean`: scalar definition and basic scalar operations.
- `Complex32Vector.lean` or `Float32Vector.lean`: size-indexed flat vector representation.
- `Algebra.lean`: strongest meaningful algebraic interface instances.
- `VectorType.lean`: `VectorType` instance for the vector representation.
- `HasFlatRepr.lean`: default and cross-representation flat-repr instances.

Aggregate import files should exist at:

- `NumLean/Data/Scalars/Complex32.lean`
- `NumLean/Data/Scalars/Complex64.lean`
- `NumLean/Data/Scalars/Float32.lean`
- `NumLean/Data/Scalars/Float.lean`
- `NumLean/Data/Scalars/UInt8.lean`
- `NumLean/Data/Scalars.lean`

## Correct Representation Design

### Complex Scalars

Define complex scalar types as two-field structures:

```lean
@[unbox]
structure Complex32 where
  re im : Float32
```

Similarly, `Complex64` should use `Float` fields.

Do not define `Complex32Array` or `Complex64Array` as separate array types for this plan.

### Complex Vectors

`Complex32Vector n` must be stored directly as a packed `Float32Array`:

```lean
structure Complex32Vector (n : Nat) where
  data : Float32Array
  size_eq : data.size = 2 * n
```

Elements are stored interleaved:

- `data[2*i] = z.re`
- `data[2*i + 1] = z.im`

`Complex64Vector n` should analogously use a packed `FloatArray`, once the `FloatArray` helper API is ready.

### UInt8 Vectors

`ByteVector n` should wrap `ByteArray` with a size invariant. Do not fake it as `Vector UInt8 n` if the intended representation is `ByteArray`.

## Efficiency Rules

These are mandatory.

- Do not implement runtime operations by converting packed arrays to `Array`/`Vector` and back.
- Do not access or modify `Float32Array.data` in runtime-critical implementations unless the function is an `@[extern]` proof-side body whose compiled implementation is replaced by C.
- Do not derive `BEq` for packed array wrappers such as `Float32Array`; that can force conversion to `Array Float32` and perform an expensive full comparison.
- Do not use `axiom` for interface proofs or representation laws.
- Do not leave anonymous `sorry` as an implementation strategy.
- Do not define `Float32Array.pop` as `xs.data.pop` for runtime; that reallocates/copies and defeats the packed representation.
- Do not use `implemented_by` unless explicitly agreed. Prefer `@[extern]` declarations whose Lean bodies are proof-friendly and whose C implementations are runtime-efficient.

## Float32Array Runtime Primitives

The following operations should have direct C implementations in `c/scalar_arrays.c` and Lean declarations in `NumLean/Data/Float32Array.lean`:

- `replicate`: allocate once and fill, preferably equivalent to `memset`/bulk fill when valid.
- `replicate2`: allocate once and fill interleaved pairs.
- `pop`: no allocation when possible; effectively decrement logical size while preserving capacity.
- `append`: reserve/extend once and `memcpy` data.

Lean bodies for these `@[extern]` functions may use internal `Array Float32` bodies if that makes proofs simple, because compiled/runtime behavior is supplied by C.

## Proof Strategy

### Float32Array

First provide a small, proof-friendly API:

- `size_push`
- `size_set`
- `get_set_eq`
- `get_set_ne`
- `size_replicate`
- `size_replicate2`
- `size_pop`
- `size_append`

For extern-backed operations, prove the theorems from the Lean body. The Lean body can be simple and proof-oriented; the C extern is responsible for performance.

Do not introduce public `Float32Array.ofFn` unless it is genuinely needed. `Complex32Vector.ofVector` is mostly a specification-side operation and can build a proof-friendly `Float32Array` directly using `Float32Array.mk (Array.ofFn ...)`.

### Complex32Vector

Provide extensionality and operation simp/spec theorems directly in `Complex32Vector.lean`.

Required theorems:

- extensionality: two `Complex32Vector n`s are equal if all logical complex entries are equal.
- `toVector_ofVector`
- `ofVector_toVector`
- `uget_spec`
- `uset_spec`
- `set_spec`
- `pop_spec`
- `replicate_spec`
- `swap_spec`
- `push_spec`
- `append_spec`

Then `VectorType.lean` should be mostly wiring to these theorems, not where all hard proofs live.

## Algebra Interface Rules

### RCOps/ROps Order

`RCOps` must not extend `PartialOrder`.

`RCOps` should expose only order operations and decidability:

- `le : K -> K -> Prop`
- `lt : K -> K -> Prop`
- `decLe : DecidableRel le`
- `decLt : DecidableRel lt`

`RCOps` should also include `BEq K` if boolean equality is needed for efficient scalar/order definitions.

`LawfulRCOps` should state the `PartialOrder` laws internally:

- reflexivity
- transitivity
- antisymmetry
- `lt_iff_le_not_ge`

`ROps` should expose `LE`, `LT`, `DecidableLE`, and `DecidableLT` instances for the scalar type.

### Complex Order

For complex-like scalar types, order should follow the `RCLike` shape:

```lean
protected def partialOrder : PartialOrder Complex where
  le z w := z.re <= w.re ∧ z.im = w.im
  lt z w := z.re < w.re ∧ z.im = w.im
```

For the computational scalar classes, use boolean equality for the imaginary component:

```lean
le x y := x.re <= y.re ∧ x.im == y.im
lt x y := x.re < y.re ∧ x.im == y.im
decLe := inferInstance
decLt := inferInstance
```

Do not use the degenerate order:

```lean
le x y := x = y
lt _ _ := False
```

## HasFlatRepr Targets

Eventually provide:

- `HasDefaultFlatRepr Float32 Float32Vector 1`
- `HasFlatRepr Float32 ByteVector 4`
- `HasDefaultFlatRepr Float FloatVector 1`
- `HasFlatRepr Float ByteVector 8`
- `HasDefaultFlatRepr Complex32 Complex32Vector 1`
- `HasFlatRepr Complex32 Float32Vector 2`
- `HasFlatRepr Complex32 ByteVector 8`
- `HasDefaultFlatRepr Complex64 Complex64Vector 1`
- `HasFlatRepr Complex64 FloatVector 2`
- `HasFlatRepr Complex64 ByteVector 16`
- `HasDefaultFlatRepr UInt8 ByteVector 1`

Do not use axioms for these. If byte-level representation is needed, provide explicit byte packing/unpacking primitives and prove/specify them properly.

## Done So Far

- Created the `NumLean/Data/Scalars/` directory layout and aggregate imports.
- Moved scalar algebra code out of `NumLean/Algebra` toward `Data/Scalars` and `Interfaces` modules.
- Refactored `RCOps` so it no longer extends `PartialOrder`.
- Added `le`, `lt`, `decLe`, `decLt`, and `BEq` to `RCOps`.
- Moved partial-order laws into `LawfulRCOps`.
- Added `ROps` instances exposing `LE`, `LT`, and decidability.
- Added direct C primitives for `Float32Array` operations:
  - `lean_float32_array_replicate`
  - `lean_float32_array_replicate2`
  - `lean_float32_array_pop`
  - `lean_float32_array_append`
- Removed `BEq` deriving for `Float32Array`.
- Removed `ForIn`/fold helpers from `Float32Array`.
- Implemented `Complex32` basic definition and algebra operations under `Data/Scalars/Complex32`.
- Implemented the packed `Complex32Vector` shape using `Float32Array` with `data.size = 2*n`.
- Proved `Complex32Vector.toVector_ofVector`.

## Next Steps

Focus on `Complex32` first before copying patterns to other scalar types.

1. Finish `Float32Array` proof-friendly theorems for extern-backed operations.
2. Prove `Complex32Vector.ext` using packed data extensionality.
3. Prove `Complex32Vector.ofVector_toVector`.
4. Prove operation specs in `Complex32Vector.lean`:
   - `uget_spec`
   - `uset_spec`
   - `set_spec`
   - `pop_spec`
   - `replicate_spec`
   - `swap_spec`
   - `push_spec`
   - `append_spec`
5. Keep `VectorType.lean` as thin wiring to proven `Complex32Vector` theorems.
6. Only after `Complex32` is correct, replicate the pattern for `Complex64` using `FloatArray` helpers.
7. Fix `ByteVector`/`UInt8` using actual `ByteArray` representation, not `Vector UInt8`.
8. Implement byte-level flat representations only after proper byte packing/unpacking operations exist.
