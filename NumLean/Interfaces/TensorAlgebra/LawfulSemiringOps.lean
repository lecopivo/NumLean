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
  rw [Vector.tensorAxpy_eq_map']
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

end TensorSemiringOps

end NumLean
