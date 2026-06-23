import NumLean.Data.Tensor.Rank

namespace NumLean
namespace Tensor

/-- Shape of a tensor.

`Shape p` stores the axis sizes for a tensor whose index structure is `p`. For example,
`Shape hp(•)` is a one-dimensional length, while `Shape hp(•,•)` is a pair of sizes that can be
read as matrix rows and columns.

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
`h(m,n)`. Lean may display the resulting type as `HTuple Nat p` instead of `Tensor.Shape p`, but
the two are definitionally the same. -/
abbrev Shape (p : Rank) := HTuple Nat p

end Tensor
end NumLean
