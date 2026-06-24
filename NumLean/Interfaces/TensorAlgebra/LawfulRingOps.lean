import NumLean.Interfaces.TensorAlgebra.RingOps
import NumLean.Interfaces.TensorAlgebra.LawfulSemiringOps
import Batteries.Data.Vector.Lemmas

namespace NumLean

open Tensor

namespace TensorRingOps

variable {Ks : Nat → Type u} {K : Type} [VectorType Ks K]

theorem tensorSub_full_get [TensorRingOps Ks K .leaf] [Add K] [Mul K] [Zero K]
    [One K] [Neg K] [Sub K] [LawfulTensorRingOps Ks K .leaf] {n : Nat}
    (xs ys : Ks n) (i : Nat) (hi : i < n) :
    VectorType.get (tensorSub xs (Layout.id h(n)) ys (Layout.id h(n))
      (FinHTupleMap.injective_id h(n))) i hi =
      VectorType.get ys i hi - VectorType.get xs i hi := by
  rw [VectorType.get_eq_getElem]
  rw [LawfulTensorRingOps.tensorSub_spec]
  rw [Vector.tensorSub_eq_map']
  rw [Vector.getElem_mapFinIdx]
  have hmem : i ∈ (Layout.id h(n)).rangeNat := by
    simpa [Layout.id] using
      (FinHTupleMap.mem_rangeNat_eval (f := Layout.id h(n))
        (i := FinHTuple.ofNatLt i hi))
  have hinv : (Layout.id h(n)).rangeNatInv i hmem = FinHTuple.ofNatLt i hi := by
    simpa [Layout.id] using
      (FinHTupleMap.rangeNatInv_eval (Layout.id h(n)) (FinHTuple.ofNatLt i hi)
        (FinHTupleMap.injective_id h(n)))
  simp [hmem, hinv, VectorType.get_eq_getElem, Layout.id]

end TensorRingOps

end NumLean
