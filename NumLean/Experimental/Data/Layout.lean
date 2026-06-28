module

public import NumLean.Data.FinHTuple

@[expose] public section

namespace NumLean

/-- The rank structure of a tensor.

`TensorRank` describes how tensor indices are structured. For ordinary tensors, `.leaf` is used
for a single-axis index, while `.prod p q` combines two index structures, such as the row and
column coordinates of a matrix.

The notation `hp(...)` is syntax for building `HTuple.Profile` values: `•` means `.leaf`, commas
build nested `.prod` nodes, and parentheses keep explicit grouping.

Examples:
- `hp(•)` is `.leaf`, rank 1, used for vectors.
- `hp(•,•)` is `.prod .leaf .leaf`, rank 2, used for matrices.
- `hp(•,•,•,•)` is rank 4, used for ordinary four-axis tensors.
- `hp((•,•),(•,•))` is also rank 4, but grouped as a matrix of matrices.

This plays the role usually called tensor rank, dimension count, or axis structure in libraries
such as NumPy, PyTorch, or XLA, except NumLean keeps this structure at the type level.

**Note:** This is an abbreviation for `HTuple.Profile`. Because it is an abbreviation, it inherits
all `HTuple.Profile` notation and operations, such as `.prod` and `hp(...)`. Lean may display the
resulting type as `HTuple.Profile` instead of `TensorRank`, but the two are definitionally the
same. -/
abbrev TensorRank := HTuple.Profile

/-- Shape of a tensor.

`Shape p` stores the axis sizes for a tensor whose index structure is `p`. For example,
`Shape .leaf` is a one-dimensional length, while `Shape (.prod .leaf .leaf)` is a pair of sizes
that can be read as matrix rows and columns.

The notation `h(...)` builds an `HTuple` matching the profile: `h(n)` is a leaf value, commas build
products, and nested `h(...)` terms preserve grouping. Thus `Shape hp(•,•)` is a readable spelling
of `HTuple Nat (.prod .leaf .leaf)`.

Examples:
- `h(n) : Shape hp(•)` is the shape of a vector of length `n`.
- `h(m,n) : Shape hp(•,•)` is the shape of an `m × n` matrix.
- `h(b,c,y,x) : Shape hp(•,•,•,•)` is a common rank-4 tensor shape, such as
  batch/channel/height/width.
- `h(h(m,n), h(k,l)) : Shape hp((•,•),(•,•))` is a rank-4 shape grouped as a matrix whose rows
  and columns are themselves two-dimensional indices.

This is the NumLean analogue of a shape tuple in NumPy or PyTorch, such as `(m, n)`, except the
rank/profile `p` is tracked in the type.

**Note:** This is an abbreviation for `HTuple Nat p`. Because it is an abbreviation, it inherits
all `HTuple` operations, such as `shape.prod shape'`, `shape.numel`, and tuple notation like
`h(m,n)`. Lean may display the resulting type as `HTuple Nat p` instead of `Shape p`, but the two
are definitionally the same. -/
abbrev Shape (p : TensorRank) := HTuple Nat p

/-- An unbounded tensor index with profile `p`.

`TensorIndex p` is a tuple of natural coordinates matching the tensor rank/profile `p`. For a
matrix profile, this is the familiar `(i, j)` coordinate; for a vector profile, it is a single
coordinate.

The notation is the same as for shapes: `h(i)` is a leaf coordinate, `h(i,j)` is a product of two
coordinates, and nested `h(...)` terms mirror nested `hp(...)` profiles. The difference is semantic:
`Shape` describes extents, while `TensorIndex` describes positions inside those extents.

Examples:
- `h(i) : TensorIndex hp(•)` is an index into a vector.
- `h(i,j) : TensorIndex hp(•,•)` is a row/column index into a matrix.
- `h(b,c,y,x) : TensorIndex hp(•,•,•,•)` is an index into a rank-4 tensor, such as
  batch/channel/height/width.
- `h(h(i,j), h(k,l)) : TensorIndex hp((•,•),(•,•))` is a rank-4 index grouped as an outer
  two-dimensional index and an inner two-dimensional index.

Bounds are supplied separately by membership in a range such as `0...shape`, or by using
`FinHTuple shape` when a statically bounded index is needed.

**Note:** This is an abbreviation for `HTuple Nat p`. Because it is an abbreviation, it inherits
all `HTuple` operations, such as `i.prod j`, `i.fst`, `i.snd`, and tuple notation like `h(i,j)`.
Lean may display the resulting type as `HTuple Nat p` instead of `TensorIndex p`, but the two are
definitionally the same. -/
abbrev TensorIndex (p : TensorRank) := HTuple Nat p

/-- A layout describes how logical tensor indices map into storage or another tensor shape.

`Layout src dst` is used to describe views of tensor data: contiguous storage, strided slices,
broadcasts, transposes, reshaped access patterns, or mappings from a logical tensor into a flat
buffer. The source shape is the logical index space being traversed, and the destination shape is
where those logical indices land.

Conceptually, this is similar to a strided view descriptor in NumPy, PyTorch, BLAS, or MLIR: it
does not store tensor data, but explains how logical coordinates map to physical coordinates.
For example, a contiguous vector slice can be represented by a rank-1 layout `i ↦ off + i`, and
a matrix layout can map `(i, j)` to a flat buffer location.

The source and destination arguments are `Shape`s, so layout types read like maps between familiar
shape tuples. For example, `Layout h(m,n) h(storage)` maps matrix coordinates into flat storage,
while `Layout h(m,n) h(n,m)` maps matrix coordinates into transposed matrix coordinates.

Examples:
- `Layout h(n) h(m)` can describe a vector view of length `n` inside storage of length `m`.
- `Layout h(m,n) h(k)` can describe a matrix stored in a flat buffer, like a BLAS leading-dimension
  layout or row-major/column-major linearization.
- `Layout h(m,n) h(m)` can describe reducing an `m × n` matrix along columns to a length-`m`
  column vector.
- `Layout h(n) h(m,n)` can describe selecting a row or column view from a matrix.
- `Layout h(m,n) h(n,m)` can describe a transpose-like view.
- `Layout h(b,c,h,w) h(storage)` can describe how a rank-4 tensor is packed into one-dimensional
  storage.

**Note:** This is an abbreviation for `FinHTupleMap src dst`. Because it is an abbreviation, it
inherits all `FinHTupleMap` operations, such as `layout1.prod layout2`. Lean may display the
resulting type as `FinHTupleMap src (dst1.prod dst2)` instead of `Layout src (dst1.prod dst2)`,
but the two are definitionally the same. -/
abbrev Layout {p q : TensorRank} (src : Shape p) (dst : Shape q) :=
    FinHTupleMap src dst
