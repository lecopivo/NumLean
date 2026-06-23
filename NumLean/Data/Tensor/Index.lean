import NumLean.Data.Tensor.Shape

namespace NumLean
namespace Tensor

/-- An unbounded tensor index with rank/profile `p`.

`Index p` is a tuple of natural coordinates matching the tensor rank/profile `p`. For a matrix
profile, this is the familiar `(i, j)` coordinate; for a vector profile, it is a single coordinate.

The notation is the same as for shapes: `h(i)` is a leaf coordinate, `h(i,j)` is a product of two
coordinates, and nested `h(...)` terms mirror nested `hp(...)` profiles. The difference is semantic:
`Shape` describes extents, while `Index` describes positions inside those extents.

Examples:
- `h(i) : Index hp(•)` is an index into a vector.
- `h(i,j) : Index hp(•,•)` is a row/column index into a matrix.
- `h(b,c,y,x) : Index hp(•,•,•,•)` is an index into a rank-4 tensor, such as
  batch/channel/height/width.
- `h(h(i,j), h(k,l)) : Index hp((•,•),(•,•))` is a rank-4 index grouped as an outer
  two-dimensional index and an inner two-dimensional index.

Bounds are supplied separately by membership in a range such as `0...shape`, or by using
`FinHTuple shape` when a statically bounded index is needed.

**Note:** This is an abbreviation for `HTuple Nat p`. Because it is an abbreviation, it inherits
all `HTuple` operations, such as `i.prod j`, `i.fst`, `i.snd`, and tuple notation like `h(i,j)`.
Lean may display the resulting type as `HTuple Nat p` instead of `Tensor.Index p`, but the two are
definitionally the same. -/
abbrev Index (p : Rank) := HTuple Nat p

end Tensor
end NumLean
