import NumLean.Data.Vector.TensorOps.Defs

namespace NumLean

namespace Vector

namespace ForAll

theorem reverseIndex_reverseIndex {k r} {shape : HTuple Nat r}
    (i : FinHTuple (.prod (.leaf k) shape)) :
    reverseIndex (reverseIndex i) = i := by
  apply FinHTuple.ext
  cases i with
  | mk val hval =>
    cases val with
    | prod left right =>
      cases left with
      | leaf a =>
        simp [reverseIndex]
        have ha : a < k := by
          exact hval.1
        omega

theorem reverseSlice_in_map_range
    {K n k r} {shape : HTuple Nat r}
    (xs : Vector K n) (map : FinHTupleMap (.prod (.leaf k) shape) h(n))
    (h : map.Injective) (i : Nat) (hi : i ∈ map.rangeNat) :
    (reverseSlice xs map h)[i] =
      xs[map (reverseIndex (map.rangeNatInv i hi))] := by
  sorry


theorem reverseSlice_out_map_range
    {K n k r} {shape : HTuple Nat r}
    (xs : Vector K n) (map : FinHTupleMap (.prod (.leaf k) shape) h(n))
    (h : map.Injective) (i : Nat) (hi : i ∉ map.rangeNat) (hi' : i < n) :
    (reverseSlice xs map h)[i] = xs[i] := by
  sorry

end ForAll

end Vector

end NumLean
