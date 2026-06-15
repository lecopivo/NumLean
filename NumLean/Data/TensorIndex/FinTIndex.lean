import NumLean.Data.TensorIndex.AxisOrder

namespace NumLean

namespace TensorIndex

namespace FinTIndex

@[implicit_reducible]
def fintype {p : HRank} (shape : Shape p) : Fintype (FinTIndex shape) :=
  Fintype.ofEquiv (Fin shape.size) (equivFin shape).symm

instance {p : HRank} {shape : Shape p} : Fintype (FinTIndex shape) :=
  fintype shape

theorem card_eq_shape_size {p : HRank} (shape : Shape p) :
    Fintype.card (FinTIndex shape) = shape.size := by
  simpa using Fintype.card_congr (equivFin shape)

end FinTIndex

end TensorIndex

end NumLean
