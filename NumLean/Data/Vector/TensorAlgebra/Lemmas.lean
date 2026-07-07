module

public import NumLean.Data.Vector.TensorAlgebra.Core
public import NumLean.Data.Vector.TensorType
public import NumLean.Interfaces.TensorIndexType

@[expose] public section

namespace NumLean.Vector

open Tensor Classical IndexType


theorem tensorSum_eq_sum [AddCommMonoid K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n)) :
    tensorSum xs xmap
    =
    ∑ i ∈ (NumLean.entries (0...shape)).toFinset, xs[xmap i] := by
  simpa [tensorSum] using
    (Fold.fold_eq_sum
      (range := ((0 : Shape r)...shape))
      (f := fun i _hi => xs[xmap i])
      (init := (0 : K)))


theorem tensorSum_eq_sum' [AddCommMonoid K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n)) :
    tensorSum xs xmap
    =
    ∑ i : Fin shape.numel,
      let i := fromFin (I:=FinHTuple shape) i
      xs[xmap i] := by
  rw [tensorSum_eq_sum]
  rw [FinHTuple.sum_zeroRange_eq_fin]
  rfl


@[simp]
theorem getElem_tensorAxpy [Add K] [Mul K] {m n : Nat} {r : Rank} {shape : Shape r} (a : K)
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) (idx : Nat) (hidx : idx < m) :
    (tensorAxpy a xs xmap ys ymap hymap)[idx]
    =
    if hi : idx ∈ ymap.rangeNat then
      ys[idx] + a * xs[xmap (ymap.rangeNatInv idx hi)]
    else
      ys[idx] := by
  simp [tensorAxpy, hymap]


@[simp]
theorem getElem_tensorAxpySelf [Add K] [Mul K] {n : Nat} {r : Rank} {shape : Shape r} (a : K)
    (data : Vector K n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range)
    (idx : Nat) (hidx : idx < n) :
    (tensorAxpySelf a data srcMap dstMap hdst h)[idx]
    =
    if hi : idx ∈ dstMap.rangeNat then
      data[idx] + a * data[srcMap (dstMap.rangeNatInv idx hi)]
    else
      data[idx] := by
  simpa [tensorAxpySelf] using
    (Tensor.Layout.getElem_map₂ (layout := dstMap) (layout' := srcMap) (xs := data)
      (f := fun _ x y => x + a * y) hdst h.symm idx hidx)


@[simp]
theorem getElem_tensorScal [Mul K] {n : Nat} {r : Rank} {shape : Shape r} (a : K)
    (xs : Vector K n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) (idx : Nat) (hidx : idx < n) :
    (tensorScal a xs xmap hxmap)[idx]
    =
    if _hi : idx ∈ xmap.rangeNat then
      a * xs[idx]
    else
      xs[idx] := by
  simp [tensorScal, hxmap]


theorem tensorDot_eq_sum [AddCommMonoid K] [Mul K] {m n : Nat} {r : Rank}
    {shape : Shape r} (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m)) :
    tensorDot xs xmap ys ymap
    =
    ∑ i ∈ (NumLean.entries (0...shape)).toFinset, xs[xmap i] * ys[ymap i] := by
  simpa [tensorDot] using
    (Fold.fold_eq_sum
      (range := ((0 : Shape r)...shape))
      (f := fun i _hi => xs[xmap i] * ys[ymap i])
      (init := (0 : K)))


open IndexType in
theorem tensorDot_eq_sum' [AddCommMonoid K] [Mul K] {m n : Nat} {r : Rank}
    {shape : Shape r} (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m)) :
    tensorDot xs xmap ys ymap
    =
    ∑ i : Fin shape.numel,
      let i := fromFin (I:=FinHTuple shape) i
      xs[xmap i] * ys[ymap i] := by
  rw [tensorDot_eq_sum]
  rw [FinHTuple.sum_zeroRange_eq_fin]
  rfl


@[simp]
theorem getElem_tensorMul [Mul K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) (idx : Nat) (hidx : idx < m) :
    (tensorMul xs xmap ys ymap hymap)[idx]
    =
    if hi : idx ∈ ymap.rangeNat then
      ys[idx] * xs[xmap (ymap.rangeNatInv idx hi)]
    else
      ys[idx] := by
  simp [tensorMul, hymap]


-- todo: we need variant of Fold.fold_eq_sum
-- theorem tensorProd_eq_prod [CommMonoid K] {n : Nat} {r : Rank} {shape : Shape r}
--     (xs : Vector K n) (xmap : Layout shape h(n)) :
--     tensorProd xs xmap
--     =
--     ∏ i ∈ (NumLean.entries (0...shape)).toFinset, xs[xmap i] := sorry


@[simp]
theorem getElem_tensorDiv [Div K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) (idx : Nat) (hidx : idx < m) :
    (tensorDiv xs xmap ys ymap hymap)[idx]
    =
    if hi : idx ∈ ymap.rangeNat then
      ys[idx] / xs[xmap (ymap.rangeNatInv idx hi)]
    else
      ys[idx] := by
  simp [tensorDiv, hymap]


@[simp]
theorem getElem_tensorInv [Inv K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) (idx : Nat) (hidx : idx < n) :
    (tensorInv xs xmap hxmap)[idx]
    =
    if _hi : idx ∈ xmap.rangeNat then
      (xs[idx])⁻¹
    else
      xs[idx] := by
  simp [tensorInv, hxmap]


@[simp]
theorem getElem_tensorGemv [CommRing K] {an xn yn : Nat}
    {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : K)
    (A : Vector K an) (amap : Layout (.prod rows cols) h(an))
    (x : Vector K xn) (xmap : Layout cols h(xn))
    (y : Vector K yn) (ymap : Layout rows h(yn))
    (hymap : ymap.Injective) (idx : Nat) (hidx : idx < yn) :
    (tensorGemv alpha beta A amap x xmap y ymap hymap)[idx]
    =
    if h : idx ∈ ymap.rangeNat then
      let ⟨i, hi⟩ := ymap.rangeNatInv idx h
      alpha * (∑ ⟨j,hj⟩ ∈ (NumLean.entries (0...cols)).toFinset, A[amap (i.prod j)] * x[xmap j])
      +
      beta * y[idx]
    else
      y[idx] := by
  by_cases h : idx ∈ ymap.rangeNat
  · simp [tensorGemv, hymap, h, Fold.fold_eq_sum]
  · simp [tensorGemv, hymap, h]


def getElem_tensorGemv' [CommRing K] {an xn yn : Nat}
    {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : K)
    (A : Vector K an) (amap : Layout (.prod rows cols) h(an))
    (x : Vector K xn) (xmap : Layout cols h(xn))
    (y : Vector K yn) (ymap : Layout rows h(yn))
    (hymap : ymap.Injective) (idx : Nat) (hidx : idx < yn) :
    (tensorGemv alpha beta A amap x xmap y ymap hymap)[idx]
    =
    if h : idx ∈ ymap.rangeNat then
      let ⟨i, hi⟩ := ymap.rangeNatInv idx h
      alpha * (∑ j : Fin cols.numel,
        let j := fromFin (I:=FinHTuple cols) j
        A[amap (i.prod j)] * x[xmap j])
      +
      beta * y[idx]
    else
      y[idx] := by
  rw [getElem_tensorGemv]
  by_cases h : idx ∈ ymap.rangeNat
  · simp only [h, dif_pos]
    cases ymap.rangeNatInv idx h with
    | mk i hi =>
      rw [FinHTuple.sum_zeroRange_eq_fin]
      rfl
  · simp [h]


@[simp]
theorem getElem_tensorGer [Add K] [Mul K] {an xn yn : Nat}
    {rr rc : Rank} {rows : Shape rr} {cols : Shape rc}
    (alpha : K)
    (x : Vector K xn) (xmap : Layout rows h(xn))
    (y : Vector K yn) (ymap : Layout cols h(yn))
    (A : Vector K an) (amap : Layout (.prod rows cols) h(an))
    (hamap : amap.Injective) (idx : Nat) (hidx : idx < an) :
    (tensorGer alpha x xmap y ymap A amap hamap)[idx]
    =
    if h : idx ∈ amap.rangeNat then
      let ⟨.prod i j, hij⟩ := amap.rangeNatInv idx h
      A[idx] + alpha * x[xmap i] * y[ymap j]
    else
      A[idx]
    := by
  by_cases h : idx ∈ amap.rangeNat
  · simp [tensorGer, hamap, h]
    cases amap.rangeNatInv idx h with
    | mk ij hij =>
      cases ij
      rfl
  · simp [tensorGer, hamap, h]


@[simp]
theorem getElem_tensorGemm [CommRing K]  {an bn cn : Nat}
    {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Vector K an) (amap : Layout (.prod is ks) h(an))
    (B : Vector K bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Vector K cn) (cmap : Layout (.prod is js) h(cn))
    (hcmap : cmap.Injective) (idx : Nat) (hidx : idx < cn) :
    (tensorGemm alpha beta A amap B bmap C cmap hcmap)[idx]
    =
    if h : idx ∈ cmap.rangeNat then
      let ⟨.prod i j, hij⟩ := cmap.rangeNatInv idx h
      alpha * (∑ ⟨k,hk⟩ ∈ (NumLean.entries (0...ks)).toFinset,
                 A[amap (i.prod k)] * B[bmap (k.prod j)])
      +
      beta * C[idx]
    else
      C[idx]
    := by
  by_cases h : idx ∈ cmap.rangeNat
  · simp [tensorGemm, hcmap, h, Fold.fold_eq_sum]
    cases cmap.rangeNatInv idx h with
    | mk ij hij =>
      cases ij
      rfl
  · simp [tensorGemm, hcmap, h]

theorem getElem_tensorGemm' [CommRing K] {an bn cn : Nat}
    {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Vector K an) (amap : Layout (.prod is ks) h(an))
    (B : Vector K bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Vector K cn) (cmap : Layout (.prod is js) h(cn))
    (hcmap : cmap.Injective) (idx : Nat) (hidx : idx < cn) :
    (tensorGemm alpha beta A amap B bmap C cmap hcmap)[idx]
    =
    if h : idx ∈ cmap.rangeNat then
      let ⟨.prod i j, hij⟩ := cmap.rangeNatInv idx h
      alpha * (∑ k : Fin ks.numel,
        let k := fromFin (I := FinHTuple ks) k
        A[amap (i.prod k.val)] * B[bmap (k.val.prod j)])
      +
      beta * C[idx]
    else
      C[idx] := by
  rw [getElem_tensorGemm]
  by_cases h : idx ∈ cmap.rangeNat
  · simp only [h, dif_pos]
    cases cmap.rangeNatInv idx h with
    | mk ij hij =>
      cases ij with
      | prod i j =>
        simp [FinHTuple.sum_zeroRange_eq_fin]
        rfl
  · simp [h]
