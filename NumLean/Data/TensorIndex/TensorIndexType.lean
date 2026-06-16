import NumLean.Data.TensorIndex.Layout
import NumLean.Data.TensorIndex.FinTIndex
import NumLean.Interfaces.IndexType

namespace NumLean
open TensorIndex
/-- `I` is tensor index type of given rank `rank`. -/
class TensorIndexTypeOfRank (I : Type u) (n : outParam Nat) (rank : HRank)
  (shape : outParam (Shape rank))
    extends IndexType I n where

  size_eq_shape_size : n = shape.size

  layout : Layout shape Nat
  compact_layout : layout.Compact

  /-- Tensor-shaped view of this flat index type. -/
  tensorEquiv : I ≃ FinTIndex shape

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
def toFinTIndex (i : I) : FinTIndex shape := tensorEquiv i

/-- Convert a tensor-shaped index back to the flat index type. -/
def fromFinTIndex (idx : FinTIndex shape) : I := tensorEquiv.symm idx

@[simp]
theorem fromFinTIndex_toFinTIndex (i : I) :
    fromFinTIndex (toFinTIndex i) = i := by
  simp [fromFinTIndex, toFinTIndex]

@[simp]
theorem toFinTIndex_fromFinTIndex (idx : FinTIndex shape) :
    toFinTIndex (fromFinTIndex (I := I) idx) = idx := by
  simp [fromFinTIndex, toFinTIndex]

end API

/-- Any index type is tensor index type of rank 1. -/
instance {I nI} [IndexType I nI] : TensorIndexTypeOfRank I nI .leaf (.leaf nI) where
  size_eq_shape_size := by rfl
  layout := .ofFin nI
  compact_layout := Layout.compact_ofFin
  tensorEquiv := (IndexType.equivFin (I := I)).trans ((FinTIndex.equivFin (.leaf nI)).symm)
  layout_eval_tensorEquiv_eq_toFin := by
    intro i; simp [Layout.ofFin, FinTIndex.equivFin, FinTIndex.leafEquiv, IndexType.equivFin]

instance {r} {shape : Shape r} : TensorIndexTypeOfRank (FinTIndex shape) shape.size r shape where
  toIdx i := ((FinTIndex.equivFin shape) i).toIdx
  fromIdx i := (FinTIndex.equivFin shape).symm i.toFin
  left_inv := by intro h; sorry
  right_inv := by intro h; sorry
  toFin i := (FinTIndex.equivFin shape) i
  fromFin i := (FinTIndex.equivFin shape).symm i
  left_inv' := by exact Equiv.leftInverse_symm (FinTIndex.equivFin shape)
  right_inv' := by exact Equiv.rightInverse_symm (FinTIndex.equivFin shape)
  size_eq_shape_size := by simp
  layout := Layout.rowMajor shape
  compact_layout := Layout.compact_rowMajor
  tensorEquiv := Equiv.refl _
  layout_eval_tensorEquiv_eq_toFin := by
    intros; simp
    unfold Layout.eval Layout.rowMajor
    rw[FinTIndex.offset_rowMajorEquiv_eq_equivFin]
    simp only [zero_add]

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
  tensorEquiv := (Equiv.prodCongr tensorEquiv tensorEquiv).trans (FinTIndex.prodEquiv _ _).symm
  layout_eval_tensorEquiv_eq_toFin := by
    intro (i,j)
    have hi := layout_eval_tensorEquiv_eq_toFin (I := I) (rank := p) i
    have hj := layout_eval_tensorEquiv_eq_toFin (I := J) (rank := q) j
    have hsizeJ := size_eq_shape_size (I := J) (rank := q)
    simp [Layout.rowMajorProd, toFin, ← hi, ← hj, - nsmul_eq_mul, TIndex.offset_smul, ←hsizeJ,
          Layout.eval, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

instance {I : Type u} {J : Type v} {nI nJ : Nat}
    {p q : HRank} {shapeI : Shape p} {shapeJ : Shape q}
    [TensorIndexType I nI p shapeI] [TensorIndexType J nJ q shapeJ] :
    TensorIndexType (I × J) (nI * nJ) (.prod p q) (HTuple.prod shapeI shapeJ) where

end TensorIndexType

end NumLean
