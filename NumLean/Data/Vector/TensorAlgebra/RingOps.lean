import NumLean.Data.Vector.TensorAlgebra.SemiringOps

set_option backward.do.legacy false

namespace NumLean
namespace Vector

open Tensor

def tensorNeg [Neg K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (_hxmap : xmap.Injective) : Vector K n := Id.run do
  let mut xs := xs
  for_all i in 0...shape do
    xs[xmap i] := -xs[xmap i]
  return xs

open Classical in
theorem tensorNeg_eq_map [Neg K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n)) (hxmap : xmap.Injective) :
    tensorNeg xs xmap hxmap =
      xs.mapFinIdx fun j xj _ =>
        if _h : ∃ i, ∃ _hi : i ∈ ((0 : Shape r)...shape),
            (xmap i).toScalar = j then
          -xj
        else
          xj := by
  simpa [tensorNeg] using
    (Fold.fold_eq_vector_map
      (range := ((0 : Shape r)...shape))
      (imap := fun i _ => (xmap i).toScalar)
      (f := fun _ _ xj => -xj)
      (init := xs)
      (himap := map_toScalar_lt xmap)
      (himap' := map_toScalar_injective xmap hxmap))

open Classical in
theorem tensorNeg_eq_map' [Neg K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n)) (hxmap : xmap.Injective) :
    tensorNeg xs xmap hxmap =
      xs.mapFinIdx fun j xj _ =>
        if _hj : j ∈ xmap.rangeNat then
          -xj
        else
          xj := by
  calc
    tensorNeg xs xmap hxmap =
        xs.mapFinIdx (fun j xj _ =>
          if h : j ∈ Set.range (fun i : {i' // i' ∈ ((0 : Shape r)...shape)} => (xmap i.1).toScalar) then
            have : Nonempty {i' // i' ∈ ((0 : Shape r)...shape)} := by have ⟨i,_⟩ := h; exact ⟨i⟩
            let ⟨_i,_hi⟩ := Function.invFun (fun i : {i' // i' ∈ ((0 : Shape r)...shape)} => (xmap i.1).toScalar) j
            (-xj)
          else
            xj) := by
      simpa [tensorNeg] using
        (Fold.fold_eq_vector_map'
          (range := ((0 : Shape r)...shape))
          (imap := fun i _ => (xmap i).toScalar)
          (f := fun _ _ xj => -xj)
          (init := xs)
          (himap := map_toScalar_lt xmap)
          (himap' := map_toScalar_injective xmap hxmap))
    _ = xs.mapFinIdx (fun j xj _ =>
        if _hj : j ∈ xmap.rangeNat then
          -xj
        else
          xj) := by
      apply Vector.ext
      intro j hj
      repeat rw [Vector.getElem_mapFinIdx]
      by_cases hNat : j ∈ xmap.rangeNat
      · have hRange : j ∈ Set.range (fun i : {i' // i' ∈ ((0 : Shape r)...shape)} => (xmap i.1).toScalar) := by
          simpa [FinHTupleMap.indexFun] using (xmap.mem_rangeNat_iff_mem_range_indexFun j).1 hNat
        rw [dif_pos hRange, dif_pos hNat]
      · have hRange : ¬ j ∈ Set.range (fun i : {i' // i' ∈ ((0 : Shape r)...shape)} => (xmap i.1).toScalar) := by
          intro hRange
          exact hNat ((xmap.mem_rangeNat_iff_mem_range_indexFun j).2 (by
            simpa [FinHTupleMap.indexFun] using hRange))
        rw [dif_neg hRange, dif_neg hNat]

def tensorSub [Sub K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (_hymap : ymap.Injective) : Vector K m := Id.run do
  let mut ys := ys
  for_all i in 0...shape do
    ys[ymap i] := ys[ymap i] - xs[xmap i]
  return ys

open Classical in
theorem tensorSub_eq_map [Sub K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) :
    tensorSub xs xmap ys ymap hymap =
      ys.mapFinIdx fun j yj _ =>
        if h : ∃ i, ∃ _hi : i ∈ ((0 : Shape r)...shape),
            (ymap i).toScalar = j then
          let i := choose h
          let hi := choose (choose_spec h)
          yj - xs[xmap i]'(map_toScalar_lt xmap i hi)
        else
          yj := by
  simpa [tensorSub] using
    (Fold.fold_eq_vector_map
      (range := ((0 : Shape r)...shape))
      (imap := fun i _ => (ymap i).toScalar)
      (f := fun i _ yj => yj - xs[xmap i])
      (init := ys)
      (himap := map_toScalar_lt ymap)
      (himap' := map_toScalar_injective ymap hymap))

open Classical in
theorem tensorSub_eq_map' [Sub K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) :
    tensorSub xs xmap ys ymap hymap =
      ys.mapFinIdx fun j yj _ =>
        if hj : j ∈ ymap.rangeNat then
          let i := ymap.rangeNatInv j hj
          yj - xs[xmap i]
        else
          yj := by
  calc
    tensorSub xs xmap ys ymap hymap =
        ys.mapFinIdx (fun j yj _ =>
          if h : j ∈ Set.range (fun i : {i' // i' ∈ ((0 : Shape r)...shape)} => (ymap i.1).toScalar) then
            have : Nonempty {i' // i' ∈ ((0 : Shape r)...shape)} := by have ⟨i,_⟩ := h; exact ⟨i⟩
            let ⟨i,hi⟩ := Function.invFun (fun i : {i' // i' ∈ ((0 : Shape r)...shape)} => (ymap i.1).toScalar) j
            yj - xs[xmap i]
          else
            yj) := by
      simpa [tensorSub] using
        (Fold.fold_eq_vector_map'
          (range := ((0 : Shape r)...shape))
          (imap := fun i _ => (ymap i).toScalar)
          (f := fun i _ yj => yj - xs[xmap i])
          (init := ys)
          (himap := map_toScalar_lt ymap)
          (himap' := map_toScalar_injective ymap hymap))
    _ = ys.mapFinIdx (fun j yj _ =>
        if hj : j ∈ ymap.rangeNat then
          let i := ymap.rangeNatInv j hj
          yj - xs[xmap i]
        else
          yj) := by
      apply Vector.ext
      intro j hj
      repeat rw [Vector.getElem_mapFinIdx]
      by_cases hNat : j ∈ ymap.rangeNat
      · have hRange : j ∈ Set.range (fun i : {i' // i' ∈ ((0 : Shape r)...shape)} => (ymap i.1).toScalar) := by
          simpa [FinHTupleMap.indexFun] using (ymap.mem_rangeNat_iff_mem_range_indexFun j).1 hNat
        haveI : Nonempty {i' // i' ∈ ((0 : Shape r)...shape)} := by
          rcases hRange with ⟨i, _⟩
          exact ⟨i⟩
        rw [dif_pos hRange, dif_pos hNat]
        have hinv :
            Function.invFun (fun i : {i' // i' ∈ ((0 : Shape r)...shape)} => (ymap i.1).toScalar) j =
              ⟨(ymap.rangeNatInv j hNat).val, FinHTuple.val_mem_zero_shape _⟩ := by
          simpa [FinHTupleMap.indexFun] using
            (FinHTupleMap.invFun_indexFun_eq_rangeNatInv ymap j hNat hymap)
        simp [hinv]
      · have hRange : ¬ j ∈ Set.range (fun i : {i' // i' ∈ ((0 : Shape r)...shape)} => (ymap i.1).toScalar) := by
          intro hRange
          exact hNat ((ymap.mem_rangeNat_iff_mem_range_indexFun j).2 (by
            simpa [FinHTupleMap.indexFun] using hRange))
        rw [dif_neg hRange, dif_neg hNat]

end Vector
end NumLean
