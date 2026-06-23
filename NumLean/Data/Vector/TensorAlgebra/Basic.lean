import NumLean.Data.Vector.Basic
import NumLean.Data.Tensor.Layout
import NumLean.Meta.ForAll
import NumLean.Tactic.TBounds

set_option backward.do.legacy false

namespace NumLean
namespace Vector

open Tensor

theorem map_toScalar_lt {p : Rank} {shape : Shape p} {n : Nat}
    (map : Layout shape h(n)) (i : Index p)
    (hi : i ∈ ((0 : Shape p)...shape)) : (map i).toScalar < n := by
  have hlt := map.inBounds i (HTuple.Range.mem_iff_le_lt.1 hi).2
  simpa using hlt

theorem map_toScalar_injective {p : Rank} {shape : Shape p} {n : Nat}
    (map : Layout shape h(n)) (hmap : map.Injective) :
    Function.Injective (fun i : {i' // i' ∈ ((0 : Shape p)...shape)} =>
      (map i.1).toScalar) := by
  intro i j hij
  apply Subtype.ext
  let i' : FinHTuple shape := ⟨i.1, (HTuple.Range.mem_iff_le_lt.1 i.2).2⟩
  let j' : FinHTuple shape := ⟨j.1, (HTuple.Range.mem_iff_le_lt.1 j.2).2⟩
  have hfin : map.evalFin i' = map.evalFin j' := by
    apply FinHTuple.ext
    apply HTuple.toScalar_injective
    simpa [FinHTupleMap.evalFin, i', j'] using hij
  have hij' := hmap hfin
  exact congrArg FinHTuple.val hij'

theorem prod_mem_zero_shape {p q : Rank} {shape : Shape p} {shape' : Shape q}
    {i : Index p} {j : Index q}
    (hi : i ∈ ((0 : Shape p)...shape))
    (hj : j ∈ ((0 : Shape q)...shape')) :
    i.prod j ∈ ((0 : Shape (.prod p q))...(shape.prod shape')) := by
  rw [HTuple.Range.mem_iff_le_lt] at hi hj ⊢
  simp [HTuple.elementwiseLE_prod, HTuple.elementwiseLT_prod, hi.1, hi.2, hj.1, hj.2]

end Vector
end NumLean
