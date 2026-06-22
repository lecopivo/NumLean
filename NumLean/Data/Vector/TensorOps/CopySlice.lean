import NumLean.Data.Vector.TensorOps.Defs
import NumLean.Interfaces.Fold.Filter
import NumLean.Data.FinHTuple
import NumLean.Data.Vector.Basic
import Std.Tactic.Do

set_option backward.do.legacy false

namespace NumLean

namespace Vector

namespace ForAll

open Std.Do

open Classical Function in
theorem copySlice_in_dst_range
    {K n m r} {shape : HTuple Nat r}
    (src : Vector K n) (srcMap : FinHTupleMap shape h(n))
    (dst : Vector K m) (dstMap : FinHTupleMap shape h(m))
    (hf : dstMap.Injective) (i : Nat) (hi : i ∈ dstMap.rangeNat) :
    (copySlice src srcMap dst dstMap hf)[i]
    =
    src[srcMap (dstMap.rangeNatInv i hi)] := by
  classical
  unfold copySlice
  simp only [LawfulFold.fold_eq_foldl]
  simp only [HTuple.getElem_leaf, HTuple.setElem_leaf, setElem_nat_eq_set, bind, Id.run, pure]
  rw[FoldMap.foldl_get_eq_foldl_filter_affectors_vector
      (deps := fun i => {i})
      (hself := by simp)
      (affectors := fun i : Fin m => { idx | dstMap idx.1 = i})
      ]
  case hdeps =>
    intros j xs ys s k hk; simp_all
    by_cases h : i = dstMap j.1
    · simp [h]
    · simp (disch:= first | assumption | grind) [s]
  case hpreserve =>
    intro j hj a ha xs
    have h : (dstMap a.1).toScalar ≠ j :=
      cast (by simp_all; intro ha'; rw[←ha'] at ha; simp at ha;) ha
    simp [h]
  simp
  have h : ((Fold.entries.{0,0,0} 0...shape).filter (fun a : Subtype _ => dstMap a = i))
           =
           [⟨(dstMap.rangeNatInv i hi).val, FinHTuple.val_mem_zero_shape (dstMap.rangeNatInv i hi)⟩] := by sorry
  conv => enter [1,1,3]; erw[h]
  simp only [List.foldl_cons, List.foldl_nil]
  have h : dstMap (dstMap.rangeNatInv i hi) = h(i) := by
    apply HTuple.toScalar_injective
    exact dstMap.eval_rangeNatInv i hi
  conv => enter [1,1,2]; rw[h]
  simp only [HTuple.leaf_toScalar, Vector.getElem_set_self]

theorem copySlice_out_dst_range
    {K n m r} {shape : HTuple Nat r}
    (src : Vector K n) (srcMap : FinHTupleMap shape h(n))
    (dst : Vector K m) (dstMap : FinHTupleMap shape h(m))
    (h : dstMap.Injective) (i : Nat) (hi : h(i) ∉ dstMap.range) (hi' : i < m) :
    (copySlice src srcMap dst dstMap h)[i]
    =
    dst[i] := by
  classical
  unfold copySlice
  simp only [LawfulFold.fold_eq_foldl]
  simp only [HTuple.getElem_leaf, HTuple.setElem_leaf, setElem_nat_eq_set, bind, Id.run, pure]
  rw[FoldMap.foldl_get_eq_foldl_filter_affectors_vector
      (deps := fun i => {i})
      (hself := by simp)
      (affectors := fun i : Fin m => { idx | dstMap idx.1 = i})]
  case hdeps =>
    intros j xs ys s k hk; simp_all
    by_cases h : i = dstMap j.1
    · simp [h]
    · simp (disch:= first | assumption | grind) [s]
  case hpreserve =>
    intro j hj a ha xs
    have h : (dstMap a.1).toScalar ≠ j :=
      cast (by simp_all; intro ha'; rw[←ha'] at ha; simp at ha;) ha
    simp [h]
  simp
  have hEntries :
      ((Fold.entries.{0,0,0} 0...shape).filter
        (fun a : Subtype _ => dstMap a = i)) = [] := by
    sorry
  conv => enter [1,1,3]; erw[hEntries]
  simp only [List.foldl_nil]

end ForAll

end Vector

end NumLean
