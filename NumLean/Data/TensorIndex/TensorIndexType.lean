import NumLean.Data.TensorIndex.Dense
import NumLean.Interfaces.IndexType

namespace NumLean

/-- `I` is tensor index type of given rank `rank`. -/
class TensorIndexTypeOfRank (I : Type u) (n : outParam Nat)
    (rank : Nat) (dims : outParam (Vector Nat rank))
    (axis : outParam (TensorIndex.AxisOrder rank))
    extends IndexType I n where
  /-- The flat index size agrees with the tensor shape. -/
  n_eq_numel : n = TensorIndex.numel dims

  /-- Tensor-shaped view of this flat index type. -/
  tensorEquiv : I ≃ TensorIndex dims

  /-- The `IndexType` flat position is the dense tensor offset for the configured axis order. -/
  toFin_eq_offset (i : I) :
    (toFin i).1 =
      (tensorEquiv i).offset (TensorIndex.denseStridesForOrder dims axis)

/-- `I` is tensor index type of canonical rank `rank`. -/
class TensorIndexType (I : Type u) (n : outParam Nat)
    (rank : outParam Nat) (dims : outParam (Vector Nat rank))
    (axis : outParam (TensorIndex.AxisOrder rank))
    extends TensorIndexTypeOfRank I n rank dims axis

namespace TensorIndexType

variable {I : Type u} {n rank : Nat} {dims : Vector Nat rank}
    {axis : TensorIndex.AxisOrder rank} [TensorIndexType I n rank dims axis]

/-- Convert a flat index type to its tensor-shaped index. -/
def toTensorIndex (i : I) : TensorIndex dims :=
  TensorIndexTypeOfRank.tensorEquiv i

/-- Convert a tensor-shaped index back to the flat index type. -/
def fromTensorIndex (idx : TensorIndex dims) : I :=
  TensorIndexTypeOfRank.tensorEquiv.symm idx

@[simp]
theorem fromTensorIndex_toTensorIndex (i : I) :
    fromTensorIndex (toTensorIndex i) = i := by
  simp [fromTensorIndex, toTensorIndex]

@[simp]
theorem toTensorIndex_fromTensorIndex (idx : TensorIndex dims) :
    toTensorIndex (fromTensorIndex (I := I) idx) = idx := by
  simp [fromTensorIndex, toTensorIndex]

end TensorIndexType

namespace TensorIndex

/-- A one-dimensional tensor index is equivalent to `Fin n`. -/
def finEquivTensorIndexSingleton (n : Nat) : Fin n ≃ TensorIndex #v[n] where
  toFun i :=
    { val := Vector.ofFn fun _ : Fin 1 => i.1
      valid := by
        intro k
        fin_cases k
        simp [i.2] }
  invFun idx := ⟨idx.val[0], by simpa using idx.valid 0⟩
  left_inv i := by
    apply Fin.ext
    simp
  right_inv idx := by
    cases idx with
    | mk val valid =>
      have hval : (Vector.ofFn fun _ : Fin 1 => val[0]) = val := by
        apply Vector.ext
        intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        simp
      simpa [TensorIndex.mk.injEq] using hval

instance instTensorIndexTypeFin (n : Nat) :
    TensorIndexType (Fin n) n 1 #v[n] (rowMajorAxisOrder 1) where
  n_eq_numel := by
    change n = ∏ _ : Fin 1, n
    simp
  tensorEquiv := finEquivTensorIndexSingleton n
  toFin_eq_offset := by
    intro i
    calc
      ↑(toFin i) = i.1 := rfl
      _ = (finEquivTensorIndexSingleton n i).offset
          (denseStridesForOrder #v[n] (rowMajorAxisOrder 1)) := by
          simp [finEquivTensorIndexSingleton, denseStridesForOrder, offset, offsetOf,
            rowMajorAxisOrder]

end TensorIndex

end NumLean
