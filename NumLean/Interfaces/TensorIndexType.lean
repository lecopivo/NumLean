import NumLean.Data.FinHTuple
import NumLean.Interfaces.IndexType

namespace NumLean

#exit
/-- `I` is tensor index type of given rank `rank`. -/
class TensorIndexTypeOfRank (I : Type u) (n : outParam Nat) (rank : HTuple.Profile)
  (shape : outParam (HTuple ℕ rank))
    extends IndexType I n where

  size_eq_shape_size : n = shape.numel

  layout : FinHTupleMap shape h(n)
  compact_layout : layout.evalFin.Bijective

  -- Tensor-shaped view of this flat index type.
  tensorEquiv : I ≃ FinHTuple shape

  /-- The `IndexType` flat position is the dense tensor offset for the configured axis order. -/
  layout_eval_tensorEquiv_eq_toFin (i : I) :
    layout.eval (tensorEquiv i).1 = (toFin i).1


/-- `I` is tensor index type of canonical rank `rank`. -/
class TensorIndexType (I : Type u) (n : outParam Nat) (rank : outParam HTuple.Profile)
  (shape : outParam (HTuple ℕ rank))
    extends TensorIndexTypeOfRank I n rank shape

namespace TensorIndexType

open TensorIndexTypeOfRank

section API
variable {I : Type u} {n : Nat} {rank} {shape : HTuple ℕ rank}
    [TensorIndexType I n rank shape]

/-- Convert a flat index type to its tensor-shaped index. -/
def toFinHTuple (i : I) : FinHTuple shape := tensorEquiv i

/-- Convert a tensor-shaped index back to the flat index type. -/
def fromFinHTuple (idx : FinHTuple shape) : I := tensorEquiv.symm idx

@[simp]
theorem fromFinHTuple_toFinHTuple (i : I) :
    fromFinHTuple (toFinHTuple i) = i := by
  simp [fromFinHTuple, toFinHTuple]

@[simp]
theorem toFinHTuple_fromFinHTuple (idx : FinHTuple shape) :
    toFinHTuple (fromFinHTuple (I := I) idx) = idx := by
  simp [fromFinHTuple, toFinHTuple]

end API

/-- Any index type is tensor index type of rank 1. -/
instance {I nI} [IndexType I nI] : TensorIndexTypeOfRank I nI .leaf (.leaf nI) where
  size_eq_shape_size := by rfl
  layout := .id nI
  compact_layout := sorry
  tensorEquiv := (IndexType.equivFin (I := I)).trans (FinHTuple.equivFin h(nI)).symm
  layout_eval_tensorEquiv_eq_toFin := by
    intro i; simp [FinHTuple.equivFin, IndexType.equivFin]

instance {r} {shape : HTuple Nat r} : TensorIndexTypeOfRank (FinHTuple shape) shape.numel r shape where
  toIdx i := ((FinHTuple.equivFin shape) i).toIdx
  fromIdx i := (FinHTuple.equivFin shape).symm i.toFin
  left_inv := by intro h; sorry
  right_inv := by intro h; sorry
  toFin i := (FinHTuple.equivFin shape) i
  fromFin i := (FinHTuple.equivFin shape).symm i
  left_inv' := by exact Equiv.leftInverse_symm (FinHTuple.equivFin shape)
  right_inv' := by exact Equiv.rightInverse_symm (FinHTuple.equivFin shape)
  size_eq_shape_size := by simp
  layout := (FinHTupleMap.id shape).linearize
  compact_layout := sorry
  tensorEquiv := Equiv.refl _
  layout_eval_tensorEquiv_eq_toFin := by
    intros; simp
    simp [FinHTuple.equivFin_val_eq_linearIndex_zero]
    sorry

/-- Default h-rank of `Fin n` is `.leaf` -/
instance : TensorIndexType (Fin n) n .leaf (.leaf n) where

open TensorIndexTypeOfRank

-- instance {I : Type u} {J : Type v} {nI nJ : Nat}
--     {p q : HTuple.Profile} {shapeI : HTuple Nat p} {shapeJ : HTuple Nat q}
--     [TensorIndexTypeOfRank I nI p shapeI] [TensorIndexTypeOfRank J nJ q shapeJ] :
--     TensorIndexTypeOfRank (I × J) (nI * nJ) (.prod p q) (HTuple.prod shapeI shapeJ) where
--   size_eq_shape_size := by
--     simp [Shape.size, size_eq_shape_size (I:=I) (rank := p), size_eq_shape_size (I:=J) (rank := q)]
--   layout := (layout (I := I) (rank := p)).rowMajorProd (layout (I := J) (rank := q))
--   compact_layout := by simp [compact_layout (I := I), compact_layout (I := J)]
--   tensorEquiv := (Equiv.prodCongr tensorEquiv tensorEquiv).trans (FinHTuple.prodEquiv _ _).symm
--   layout_eval_tensorEquiv_eq_toFin := by
--     intro (i,j)
--     have hi := layout_eval_tensorEquiv_eq_toFin (I := I) (rank := p) i
--     have hj := layout_eval_tensorEquiv_eq_toFin (I := J) (rank := q) j
--     have hsizeJ := size_eq_shape_size (I := J) (rank := q)
--     simp [Layout.rowMajorProd, toFin, ← hi, ← hj, - nsmul_eq_mul, TIndex.offset_smul, ←hsizeJ,
--           Layout.eval, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

-- instance {I : Type u} {J : Type v} {nI nJ : Nat}
--     {p q : HRank} {shapeI : Shape p} {shapeJ : Shape q}
--     [TensorIndexType I nI p shapeI] [TensorIndexType J nJ q shapeJ] :
--     TensorIndexType (I × J) (nI * nJ) (.prod p q) (HTuple.prod shapeI shapeJ) where

end TensorIndexType

end NumLean
