import NumLean.Interfaces.TensorAlgebra.MulOps

namespace NumLean

open Tensor

namespace TensorMulOps

variable {Ks : Nat → Type u} {K : Type} [VectorType Ks K]

example (n : Nat) : Layout.rowMajor h(n) = Layout.id h(n) := by rfl

theorem tensorScal_full_get [TensorMulOps Ks K .leaf] [Mul K] [One K]
    [LawfulTensorMulOps Ks K .leaf] {n : Nat}
    (a : K) (xs : Ks n) (i : Nat) (hi : i < n) :
    VectorType.get (tensorScal a xs (Layout.id h(n)) (FinHTupleMap.injective_id h(n))) i hi =
      a * VectorType.get xs i hi := by
  rw [VectorType.get_eq_getElem]
  rw [LawfulTensorMulOps.tensorScal_spec]
  rw [Vector.tensorScal_eq_map]
  rw [Vector.getElem_mapFinIdx]
  have hex : ∃ i', ∃ hi : i' ∈ (h(0)...h(n)),
      ((Layout.id h(n)) i').toScalar = i := by
    exact ⟨h(i), by simpa [HTuple.Range.mem_iff_le_lt] using hi, by simp [Layout.id]⟩
  simp [VectorType.get_eq_getElem, Layout.id]
  intro hnone
  exact (hnone h(i) (by simpa [HTuple.Range.mem_iff_le_lt] using hi) rfl).elim

end TensorMulOps

end NumLean
