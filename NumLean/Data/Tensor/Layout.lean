import NumLean.Data.Tensor.Index

namespace NumLean
namespace Tensor

/-- A layout describes a map from indices of `src` shaped tensor map into `dst` shaped tensor.

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
resulting type as `FinHTupleMap src (dst1.prod dst2)` instead of `Tensor.Layout src (dst1.prod dst2)`,
but the two are definitionally the same. -/
abbrev Layout {p q : Rank} (src : Shape p) (dst : Shape q) := FinHTupleMap src dst

abbrev Layout.id {p : Rank} (shape : Shape p) :
    Layout shape shape :=
  FinHTupleMap.id shape

abbrev Layout.point (shape : Shape p) (x : Shape p) (h : x <ₑ shape := by get_elem_tactic) :
    Layout h(1) shape :=
  FinHTupleMap.point shape x

abbrev Layout.rowMajor {p : Rank} (shape : Shape p) : Layout shape h(shape.numel) :=
  FinHTupleMap.rowMajorMap shape

@[simp]
theorem Layout.rowMajor_leaf_eq_id (n : Nat) : Layout.rowMajor h(n) = Layout.id h(n) := rfl

/-- A compact layout covers its one-dimensional destination exactly once.

This is the layout-level form of a dense tensor view: the tensor domain has the same number of
entries as the backing one-dimensional storage and the layout is a bijection onto that storage. -/
abbrev Layout.Compact {p : Rank} {shape : Shape p} {n : Nat}
    (map : Layout shape h(n)) : Prop :=
  map.Bijective

theorem Layout.Compact.injective {p : Rank} {shape : Shape p} {n : Nat}
    {map : Layout shape h(n)} (hmap : map.Compact) : map.Injective :=
  hmap.1

-- todo: this should produce `Layout cols (rows.prod cols)` !
abbrev Layout.row {p q : Rank} (rows : Shape p) (cols : Shape q)
    (row : Index p) (hrow : row <ₑ rows := by get_elem_tactic) :
    Layout (h(1).prod cols) (rows.prod cols) :=
  (point rows row).pair (id cols)

-- todo: this should produce `Layout rows (rows.prod cols)` !
abbrev Layout.col {p q : Rank} (rows : Shape p) (cols : Shape q)
    (col : Index q) (hrow : col <ₑ cols := by get_elem_tactic) :
    Layout (rows.prod h(1)) (rows.prod cols) :=
  (id rows).pair (point cols col)

end Tensor
end NumLean
