import NumLean.Data.TensorIndex.Layout
import NumLean.Interfaces.IndexType

namespace NumLean
open TensorIndex
/-- `I` is tensor index type of given rank `rank`. -/
class TensorIndexTypeOfRank (I : Type u) (n : outParam Nat) (rank : HRank)
  (shape : outParam (Shape rank))
    extends IndexType I n where

  size_eq_shape_size : n = shape.size

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

section API
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

end API

/-- Any index type is tensor index type of rank 1. -/
instance {I nI} [IndexType I nI] : TensorIndexTypeOfRank I nI .leaf (.leaf nI) where
  size_eq_shape_size := by rfl
  layout := .ofFin nI
  compact_layout := Layout.compact_ofFin
  tensorEquiv := (IndexType.equivFin (I := I)).trans ((FinIndex.equivFin (.leaf nI)).symm)
  layout_eval_tensorEquiv_eq_toFin := by
    intro i; simp [Layout.ofFin, FinIndex.equivFin, FinIndex.leafEquiv, IndexType.equivFin]

/-- Default h-rank of `Fin n` is `.leaf` -/
instance : TensorIndexType (Fin n) n .leaf (.leaf n) where

open TensorIndexTypeOfRank

instance {I : Type u} {J : Type v} {nI nJ : Nat}
    {p q : HRank} {shapeI : Shape p} {shapeJ : Shape q}
    [TensorIndexTypeOfRank I nI p shapeI] [TensorIndexTypeOfRank J nJ q shapeJ] :
    TensorIndexTypeOfRank (I × J) (nI * nJ) (.prod p q) (HTuple.prod shapeI shapeJ) where
  size_eq_shape_size := by
    simp [Shape.size, size_eq_shape_size (I:=I) (rank := p), size_eq_shape_size (I:=J) (rank := q)]
  layout := (layout (I := I) (rank := p)).rowMajorProd (layout (I := J) (rank := q))
  compact_layout := by simp [compact_layout (I := I), compact_layout (I := J)]
  tensorEquiv := (Equiv.prodCongr tensorEquiv tensorEquiv).trans FinIndex.prodEquiv.symm
  layout_eval_tensorEquiv_eq_toFin := by
    intro (i,j)
    simp [FinIndex.prodEquiv,layout_eval_tensorEquiv_eq_toFin, ← size_eq_shape_size (I := J), toFin]

instance {I : Type u} {J : Type v} {nI nJ : Nat}
    {p q : HRank} {shapeI : Shape p} {shapeJ : Shape q}
    [TensorIndexType I nI p shapeI] [TensorIndexType J nJ q shapeJ] :
    TensorIndexType (I × J) (nI * nJ) (.prod p q) (HTuple.prod shapeI shapeJ) where

end TensorIndexType

end NumLean
