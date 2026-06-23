import NumLean.Interfaces.TensorAlgebra.SemiringOps
import NumLean.Interfaces.TensorAlgebra.LawfulMulOps
import Batteries.Data.Vector.Lemmas

namespace NumLean

open Tensor

namespace TensorSemiringOps

variable {Ks : Nat → Type u} {K : Type} [VectorType Ks K]

theorem tensorAxpy_full_get [TensorSemiringOps Ks K .leaf] [Add K] [Mul K] [Zero K]
    [One K] [LawfulTensorSemiringOps Ks K .leaf] {n : Nat}
    (a : K) (xs ys : Ks n) (i : Nat) (hi : i < n) :
    VectorType.get (tensorAxpy a xs (Layout.id h(n)) ys (Layout.id h(n))
      (FinHTupleMap.injective_id h(n))) i hi =
      VectorType.get ys i hi + a * VectorType.get xs i hi := by
  rw [VectorType.get_eq_getElem]
  rw [LawfulTensorSemiringOps.tensorAxpy_spec]
  rw [Vector.tensorAxpy_eq_map]
  rw [Vector.getElem_mapFinIdx]
  have hex : ∃ i', ∃ hi : i' ∈ ((0 : Shape .leaf)...h(n)), i'.toScalar = i := by
    exact ⟨h(i), by simpa [HTuple.Range.mem_iff_le_lt] using hi, rfl⟩
  have hex' : ∃ i', ∃ hi : i' ∈ ((0 : Shape .leaf)...h(n)),
      ((Layout.id h(n)) i').toScalar = i := by
    simpa [Layout.id] using hex
  by_cases hcase : ∃ i', ∃ hi : i' ∈ ((0 : Shape .leaf)...h(n)),
      ((Layout.id h(n)) i').toScalar = i
  · rw [dif_pos hcase]
    simp only [Layout.id, FinHTupleMap.id_eval] at ⊢
    have hxs_any (hproof : ∃ i', ∃ hi : i' ∈ ((0 : Shape .leaf)...h(n)), i'.toScalar = i) :
        (VectorType.toVector xs)[Classical.choose hproof]'(by
          have hmem := Classical.choose (Classical.choose_spec hproof)
          simpa [HTuple.elementwiseLT_leaf] using (HTuple.Range.mem_iff_le_lt.1 hmem).2) =
          (VectorType.toVector xs)[i]'hi := by
      have hidx : (Classical.choose hproof).toScalar = i :=
        Classical.choose_spec (Classical.choose_spec hproof)
      have hchooseLt : (Classical.choose hproof).toScalar < n := by
        have hmem := Classical.choose (Classical.choose_spec hproof)
        simpa [HTuple.elementwiseLT_leaf] using (HTuple.Range.mem_iff_le_lt.1 hmem).2
      have hfin : (⟨(Classical.choose hproof).toScalar, hchooseLt⟩ : Fin n) = ⟨i, hi⟩ := by
        apply Fin.ext
        simpa [Layout.id] using hidx
      simpa [Vector.get_eq_getElem] using
        congrArg (fun k : Fin n => (VectorType.toVector xs).get k) hfin
    rw [VectorType.get_eq_getElem, VectorType.get_eq_getElem]
    congr 1
    congr 1
    apply hxs_any
  · exact (hcase hex').elim

end TensorSemiringOps

end NumLean
