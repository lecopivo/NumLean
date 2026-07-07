module

public import NumLean.Data.Vector.Basic
public import NumLean.Data.Vector.LayoutMap
public import NumLean.Data.Tensor.Layout
public import NumLean.Interfaces.Fold.Lemmas
public import NumLean.Meta.ForAll
public import NumLean.Meta.GetElemSetElemLinter

@[expose] public section

set_option backward.do.legacy false
set_option linter.unusedVariables false
namespace NumLean
namespace Vector

open Tensor

/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i].

This is the reference implementation of `TensorType.copySlice`. -/
def copySlice {K n m} {r : Rank} {shape : Shape r}
    (src : Vector K n) (srcMap : Layout shape h(n))
    (dst : Vector K m) (dstMap : Layout shape h(m))
    (h : dstMap.Injective) : Vector K m := Id.run do
  let mut dst := dst
  for_all i in 0...shape do
    dst[dstMap i] := src[srcMap i]
  return dst


/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i].

This is the reference implementation of `TensorType.copySlice`. -/
def copySliceSelf {α} {n : Nat} {r : Rank} {shape : Shape r}
    (data : Vector α n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range) : Vector α n :=
  Layout.map₂ dstMap srcMap data fun _ _ src => src


/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i].

This is the reference implementation of `TensorType.copySlice`. -/
def swapSlice {α} {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector α m) (xmap : Layout shape h(m))
    (ys : Vector α n) (ymap : Layout shape h(n))
    (hxmap : xmap.Injective) (hymap : ymap.Injective) :
    Vector α m × Vector α n := Id.run do
  let mut xs := xs
  let mut ys := ys
  for_all i in 0...shape do
    let ix := xmap i
    let iy := ymap i
    let x := xs[ix]
    let y := ys[iy]
    xs[ix] := y
    ys[iy] := x
  return (xs, ys)

/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i].

This is the reference implementation of `TensorType.copySlice`.

todo: this is not a good implementation as it makes a copy of the data. -/
def swapSliceSelf {α} {n : Nat} {r : Rank} {shape : Shape r}
    (data : Vector α n) (map : Layout shape h(n)) (map' : Layout shape h(n))
    (hmap : map.Injective) (hmap' : map'.Injective) (h : Disjoint map.range map'.range) :
    Vector α n :=
  let data' := Layout.map₂ map' map data fun _ _ y => y
  Layout.map₂ map map' data' fun i _ _ => data[map' i]


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
  erw[Fold.fold_layout_ext (init := dst) (f := fun i h _ => src[(srcMap i)])]
  case hmap => assumption
  rfl


open Classical in
/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i].

This is the reference implementation of `TensorType.copySlice`. -/
@[simp]
theorem getElem_copySliceSelf {α} {m n : Nat} {r : Rank} {shape : Shape r}
    (data : Vector α n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range)
    (j : Nat) (hj : j < n) :
    (copySliceSelf data srcMap dstMap hdst h)[j]
    =
    if hi : j ∈ dstMap.rangeNat then
      data[srcMap (dstMap.rangeNatInv j hi)]
    else
      data[j] := by
  simpa [copySliceSelf] using
    (Tensor.Layout.getElem_map₂ (layout := dstMap) (layout' := srcMap) (xs := data)
      (f := fun _ _ src => src) hdst h.symm j hj)


open Classical in
/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i].

This is the reference implementation of `TensorType.copySlice`. -/
@[simp]
theorem getElem_swapSliceSelf {α} {n : Nat} {r : Rank} {shape : Shape r}
    (data : Vector α n) (map : Layout shape h(n)) (map' : Layout shape h(n))
    (hmap : map.Injective) (hmap' : map'.Injective) (h : Disjoint map.range map'.range)
    (j : Nat) (hj : j < n) :
    (swapSliceSelf data map map' hmap hmap' h)[j]
    =
    if hk : j ∈ map.rangeNat then
      data[map' (map.rangeNatInv j hk)]
    else if hk : j ∈ map'.rangeNat then
      data[map (map'.rangeNatInv j hk)]
    else
      data[j] := by
  rw [swapSliceSelf]
  rw [Tensor.Layout.getElem_map₂ (layout := map) (layout' := map')
    (xs := Layout.map₂ map' map data fun _ _ y => y)
    (f := fun i _ _ => data[map' i]) hmap h j hj]
  by_cases hjmap : j ∈ map.rangeNat
  · simp [hjmap]
  · simp [hjmap]
    rw [Tensor.Layout.getElem_map₂ (layout := map') (layout' := map) (xs := data)
      (f := fun _ _ y => y) hmap' h.symm j hj]
    rfl
