import NumLean.Data.TensorIndex.Hierarchical
import NumLean.Interfaces.IndexType

namespace NumLean
open TensorIndex
/-- `I` is tensor index type of given rank `rank`. -/
class TensorIndexTypeOfRank (I : Type u) (n : outParam Nat) (rank : HRank)
  (shape : outParam (Shape rank))
    extends IndexType I n where

  n_eq_shape_size : n = shape.size

  layout : Layout shape Int
  compact_layout : layout.Compact

  /-- Tensor-shaped view of this flat index type. -/
  tensorEquiv : I ≃ FinIndex shape

  /-- The `IndexType` flat position is the dense tensor offset for the configured axis order. -/
  layout_eval_tensorEquiv_eq_toFin (i : I) :
    layout.eval (tensorEquiv i).1 = (toFin i).1

/-- `I` is tensor index type of canonical rank `rank`. -/
class TensorIndexType (I : Type u) (n : outParam Nat) (rank : outParam HRank)
  (shape : outParam (Shape rank))
    extends TensorIndexTypeOfRank I n rank shape

namespace TensorIndexType

open TensorIndexTypeOfRank

variable {I : Type u} {n : Nat} {rank} {shape : Shape rank}
    [TensorIndexType I n rank shape]

/-- Convert a flat index type to its tensor-shaped index. -/
def toFinIndex (i : I) : FinIndex shape := tensorEquiv i

/-- Convert a tensor-shaped index back to the flat index type. -/
def fromFinIndex (idx : FinIndex shape) : I := tensorEquiv.symm idx

@[simp]
theorem fromFinIndex_toFinIndex (i : I) :
    fromFinIndex (toFinIndex i) = i := by
  simp [fromFinIndex, toFinIndex]

@[simp]
theorem toFinIndex_fromFinIndex (idx : FinIndex shape) :
    toFinIndex (fromFinIndex (I := I) idx) = idx := by
  simp [fromFinIndex, toFinIndex]

end TensorIndexType

namespace TensorIndexTypa


instance : TensorIndexType (Fin n) n .leaf (.leaf n) where
  n_eq_shape_size := by rfl
  layout := {
    offset := 0
    stride := .leaf 1
  }
  compact_layout := sorry
  tensorEquiv := sorry
  layout_eval_tensorEquiv_eq_toFin := sorry


instance instFinIndexTypeFin (n : Nat) :
    FinIndexType (Fin n) n 1 #v[n] (rowMajorAxisOrder 1) where
  n_eq_numel := by
    change n = ∏ _ : Fin 1, n
    simp
  tensorEquiv := finEquivFinIndexSingleton n
  toFin_eq_offset := by
    intro i
    calc
      ↑(toFin i) = i.1 := rfl
      _ = (finEquivFinIndexSingleton n i).offset
          (denseStridesForOrder #v[n] (rowMajorAxisOrder 1)) := by
          simp [finEquivFinIndexSingleton, denseStridesForOrder, offset, offsetOf,
            rowMajorAxisOrder]

end FinIndex

end NumLean
