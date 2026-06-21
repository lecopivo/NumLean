import NumLean.Data.Vector.TensorOps.Defs

namespace NumLean

namespace Vector

namespace ForAll

theorem swapSlice_fst_in_xmap_range
    {K m n r} {shape : HTuple Nat r}
    (xs : Vector K m) (xmap : FinHTupleMap shape h(m))
    (ys : Vector K n) (ymap : FinHTupleMap shape h(n))
    (h : xmap.Injective) (h' : ymap.Injective) (i : Nat) (hi : i ∈ xmap.rangeNat) :
    (swapSlice xs xmap ys ymap h h').1[i] =
      ys[ymap (xmap.rangeNatInv i hi)] := by
  sorry

theorem swapSlice_fst_out_xmap_range
    {K m n r} {shape : HTuple Nat r}
    (xs : Vector K m) (xmap : FinHTupleMap shape h(m))
    (ys : Vector K n) (ymap : FinHTupleMap shape h(n))
    (h : xmap.Injective) (h' : ymap.Injective) (i : Nat) (hi : i ∉ xmap.rangeNat) (hi' : i < m) :
    (swapSlice xs xmap ys ymap h h').1[i] = xs[i] := by
  sorry

theorem swapSlice_snd_in_ymap_range
    {K m n r} {shape : HTuple Nat r}
    (xs : Vector K m) (xmap : FinHTupleMap shape h(m))
    (ys : Vector K n) (ymap : FinHTupleMap shape h(n))
    (h : xmap.Injective) (h' : ymap.Injective) (i : Nat) (hi : i ∈ ymap.rangeNat) :
    (swapSlice xs xmap ys ymap h h').2[i] =
      xs[xmap (ymap.rangeNatInv i hi)] := by
  sorry

theorem swapSlice_snd_out_ymap_range
    {K m n r} {shape : HTuple Nat r}
    (xs : Vector K m) (xmap : FinHTupleMap shape h(m))
    (ys : Vector K n) (ymap : FinHTupleMap shape h(n))
    (h : xmap.Injective) (h' : ymap.Injective) (i : Nat) (hi : i ∉ ymap.rangeNat) (hi' : i < n) :
    (swapSlice xs xmap ys ymap h h').2[i] = ys[i] := by
  sorry

end ForAll

end Vector

end NumLean
