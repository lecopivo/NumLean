import NumLean.Data.TensorIndex.Basic

namespace NumLean

namespace TensorIndex

instance {p : HRank} : Fintype (HTuple.Index p) :=
  Fintype.ofEquiv (Fin p.size) (HTuple.Index.equivFin p).symm

/-- A permutation of hierarchical axes, ordered from least significant to most significant.

For a product-shaped coordinate `(i, j)`, the axis at position `0` is fastest-moving. -/
abbrev AxisOrder (p : HRank) := Fin p.size ≃ HTuple.Index p

namespace AxisOrder

/-- The axis order induced by the left-to-right order of `HTuple.Index`.

For a matrix-shaped profile `(row, col)`, this is column-major/colexicographic order. -/
@[inline] def colMajor (p : HRank) : AxisOrder p :=
  (HTuple.Index.equivFin p).symm

/-- The reversed left-to-right axis order.

For a matrix-shaped profile `(row, col)`, this is row-major order. -/
@[inline] def rowMajor (p : HRank) : AxisOrder p :=
  (⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩ : Fin p.size ≃ Fin p.size).trans
    (HTuple.Index.equivFin p).symm

end AxisOrder

namespace Shape

/-- Dimension of a shape at a leaf axis, as a natural number. -/
@[inline] def dim {p : HRank} (shape : Shape p) (axis : HTuple.Index p) : Nat :=
  shape.get axis

end Shape

end TensorIndex

end NumLean
