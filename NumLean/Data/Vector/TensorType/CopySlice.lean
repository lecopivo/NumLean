import NumLean.Data.Vector.Basic
import NumLean.Data.Tensor
import NumLean.Interfaces.Fold.Lemmas
import NumLean.Meta.ForAll

set_option backward.do.legacy false
namespace NumLean
namespace Vector

open NumLean Tensor

/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i].

This is the reference implementation of `TensorType.copySlice`. -/
def copySlice {K n m} {r : Rank} {shape : Shape r}
    (src : Vector K n) (srcMap : Layout shape h(n))
    (dst : Vector K m) (dstMap : Layout shape h(m))
    (_h : dstMap.Injective) : Vector K m := Id.run do
  let mut dst := dst
  for_all i in 0...shape do
    dst[dstMap i] := src[srcMap i]
  return dst


open Fold Classical Function in
theorem fold_ext {r : Rank} {shape : Shape r}
    {X Xs dom} [GetElem Xs Nat X dom] [SetElem Xs Nat X dom] [LawfulSetElem Xs Nat]
    (map : Layout shape h(n)) (init : Xs)
    (hmap : map.Injective)
    (f : (i : HTuple ℕ r) → (i <ₑ shape) → X → X)
    (himap : ∀ x i (hi : i <ₑ shape), dom x (map i))
    (j : Nat) (hj : ∀ x, dom x j) :
    getElem (Fold.fold (0...shape) (init := init) (fun i hi xs =>
      setElem xs (map i : Nat) (f i (by grind) (getElem xs (map i) (himap _ _ (by grind)))) (himap _ _ (by grind)))) j (hj _)
    =
    if hj : j ∈ map.rangeNat then
      let ⟨i,hi⟩ := map.rangeNatInv j hj
      f i hi (init[j]'(by grind))
    else
      init[j]'(by grind) := sorry

set_option pp.coercions false in
open Classical Fold in
theorem getElem_copySlice {K n m} {r : Rank} {shape : Shape r}
    (src : Vector K n) (srcMap : Layout shape h(n))
    (dst : Vector K m) (dstMap : Layout shape h(m))
    (h : dstMap.Injective) (i : Nat) (hi : i < m) :
    (copySlice src srcMap dst dstMap h)[i]
    =
    if h : i ∈ dstMap.rangeNat then
      src[srcMap (dstMap.rangeNatInv i h)]
    else
      dst[i] := by
  simp [copySlice, Id.run, bind, pure]
  erw[fold_ext (init := dst) (f := fun i h _ => src[(srcMap i : Nat)])]
  case hmap => assumption
  case hj => intros; assumption
  case himap => intros; get_elem_tactic



/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i].

This is the reference implementation of `TensorType.copySlice`. -/
def copySliceSelf {α} {n : Nat} {r : Rank} {shape : Shape r}
    (data : Vector α n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range) : Vector α n := Id.run do
  let mut data := data
  for_all i in 0...shape do
    data[dstMap i] := data[srcMap i]
  return data


open Classical in
/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i].

This is the reference implementation of `TensorType.copySlice`. -/
theorem getElem_copySliceSelf {α} {m n : Nat} {r : Rank} {shape : Shape r}
    (data : Vector α n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range)
    (j : Nat) (hj : j < n) :
    (copySliceSelf data srcMap dstMap hdst h)[j]
    =
    if hi : i ∈ dstMap.rangeNat then
      data[srcMap (dstMap.rangeNatInv i hi)]
    else
      data[j] := sorry


/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i].

This is the reference implementation of `TensorType.copySlice`. -/
def swapSliceSelf {α} {n : Nat} {r : Rank} {shape : Shape r}
    (data : Vector α n) (map : Layout shape h(n)) (map' : Layout shape h(n))
    (hmap : map.Injective) (hmap' : map'.Injective) (h : Disjoint map.range map'.range) :
    Vector α n := Id.run do
  let mut data := data
  for_all i in 0...shape do
    let k := map i
    let k' := map' i
    let x := data[k]
    let x' := data[k']
    data[k] := x'
    data[k'] := x
  return data


open Classical in
/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i].

This is the reference implementation of `TensorType.copySlice`. -/
theorem getElem_swapSliceSelf {α} {n : Nat} {r : Rank} {shape : Shape r}
    (data : Vector α n) (map : Layout shape h(n)) (map' : Layout shape h(n))
    (hmap : map.Injective) (hmap' : map'.Injective) (h : Disjoint map.range map'.range)
    (j : Nat) (hj : j < n) :
    (swapSliceSelf data map map' hmap hmap' h)[j]
    =
    if hk : k ∈ map.rangeNat then
      data[map' (map.rangeNatInv k hk)]
    else if hk : k ∈ map'.rangeNat then
      data[map (map'.rangeNatInv k hk)]
    else
      data[j] := sorry
