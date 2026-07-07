module

public import NumLean.Data.Tensor.Layout
public import NumLean.Data.Vector.TensorType
public import NumLean.Interfaces.VectorType.Basic

@[expose] public section

namespace NumLean

open VectorType Tensor in
/-- `Ks` supports tensor operations that move data around like copying or swapping tensor shaped
slices of the memory buffer `xs : Ks n`.

For algebraic operations please see classes in `NumLean/Interfaces/TensorAlgebra/*` -/
class TensorType (Ks : Nat → Type) {K : Type} [VectorType Ks K] where

  /-- Copy slice of `src` and copy it to a slice of `dst`.

  It is required that the source and destination locations are disjoint such that this can be
  executed in parallel without causing data races. -/
  copySlice {m n : Nat} {r : Rank} {shape : Shape r}
    (src : Ks n) (srcMap : Layout shape h(n))
    (dst : Ks m) (dstMap : Layout shape h(m))
    (hdst : dstMap.Injective) : Ks m
  toVector_copySlice {m n : Nat} {r : Rank} {shape : Shape r}
    (src : Ks n) (srcMap : Layout shape h(n))
    (dst : Ks m) (dstMap : Layout shape h(m))
    (hdst : dstMap.Injective) :
    toVector (copySlice src srcMap dst dstMap hdst)
    =
    Vector.copySlice (toVector src) srcMap
                     (toVector dst) dstMap hdst

  /-- Copy slice of `data` and copy it back to `data` somewhere else.

  It is required that the source and destination locations are disjoint such that this can be
  executed in parallel without causing data races. -/
  copySliceSelf {n : Nat} {r : Rank} {shape : Shape r}
    (data : Ks n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range) : Ks n
  toVector_copySliceSelf {m n : Nat} {r : Rank} {shape : Shape r}
    (data : Ks n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range) :
    toVector (copySliceSelf data srcMap dstMap hdst h)
    =
    Vector.copySliceSelf (toVector data) srcMap dstMap hdst h


  -- right now we don't have a good infrastracture to reason about it easily so we postpone
  -- requiring it for now
  -- swapSlice {m n : Nat} {r : HTuple.Profile} {shape : HTuple Nat r}
  --   (xs : Ks m) (xmap : FinHTupleMap shape h(m))
  --   (ys : Ks n) (ymap : FinHTupleMap shape h(n))
  --   (hxmap : xmap.Injective) (hymap : ymap.Injective) : Ks m × Ks n

  /-- Swap two slices in `data`. -/
  swapSliceSelf {n : Nat} {r : Rank} {shape : Shape r}
    (data : Ks n) (map : Layout shape h(n)) (map' : Layout shape h(n))
    (hmap : map.Injective) (hmap' : map'.Injective) (h : Disjoint map.range map'.range) : Ks n
  toVector_swapSliceSelf {m n : Nat} {r : Rank} {shape : Shape r}
    (data : Ks n) (map : Layout shape h(n)) (map' : Layout shape h(n))
    (hmap : map.Injective) (hmap' : map'.Injective) (h : Disjoint map.range map'.range) :
    toVector (swapSliceSelf data map map' hmap hmap' h)
    =
    Vector.swapSliceSelf (toVector data) map map' hmap hmap' h


instance {α} : TensorType (Vector α) where
  copySlice := Vector.copySlice
  toVector_copySlice := by intros; rfl
  copySliceSelf := Vector.copySliceSelf
  toVector_copySliceSelf := by intros; rfl
  swapSliceSelf := Vector.swapSliceSelf
  toVector_swapSliceSelf := by intros; rfl

namespace TensorType

open Classical Tensor VectorType

variable {Ks : Nat → Type} {K : Type} [v : VectorType Ks K] [TensorType Ks (K:=K)]
variable {r : Rank}

@[simp]
theorem get_copySlice {m n : Nat} {shape : Shape r}
    (src : Ks n) (srcMap : Layout shape h(n))
    (dst : Ks m) (dstMap : Layout shape h(m))
    (hdst : dstMap.Injective) (idx : Nat) (hidx : idx < m) :
    VectorType.get (TensorType.copySlice (Ks:=Ks) (K:=K) src srcMap dst dstMap hdst) idx hidx
    =
    if hi : idx ∈ dstMap.rangeNat then
      VectorType.get src (srcMap (dstMap.rangeNatInv idx hi)) (by get_elem_tactic)
    else
      VectorType.get dst idx hidx := by
  rw [VectorType.get_spec, TensorType.toVector_copySlice]
  simpa only [VectorType.get_spec] using
    (Vector.getElem_copySlice (src := toVector src) (srcMap := srcMap)
      (dst := toVector dst) (dstMap := dstMap) (h := hdst) idx hidx)

@[simp]
theorem get_copySliceSelf {n : Nat} {shape : Shape r}
    (data : Ks n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range)
    (idx : Nat) (hidx : idx < n) :
    VectorType.get (self:=v)
      (TensorType.copySliceSelf (Ks:=Ks) (K:=K) data srcMap dstMap hdst h) idx hidx
    =
    if hi : idx ∈ dstMap.rangeNat then
      VectorType.get (self:=v) data (srcMap (dstMap.rangeNatInv idx hi)) (by get_elem_tactic)
    else
      VectorType.get (self:=v) data idx hidx := by
  conv_lhs =>
    rw [@VectorType.get_spec Ks K v n
      (TensorType.copySliceSelf (Ks:=Ks) (K:=K) data srcMap dstMap hdst h) idx hidx]
  rw [TensorType.toVector_copySliceSelf]
  convert (Vector.getElem_copySliceSelf (α := K) (m := n) (n := n) (r := r) (shape := shape)
    (data := toVector data) (srcMap := srcMap)
    (dstMap := dstMap) (hdst := hdst) (h := h) idx hidx) using 1
  · by_cases hi : idx ∈ dstMap.rangeNat
    · rw [dif_pos hi, dif_pos hi]
      exact VectorType.get_spec data (srcMap (dstMap.rangeNatInv idx hi)) _
    · rw [dif_neg hi, dif_neg hi]
      exact VectorType.get_spec data idx hidx
  · get_elem_tactic

@[simp]
theorem get_swapSliceSelf {n : Nat} {shape : Shape r}
    (data : Ks n) (map : Layout shape h(n)) (map' : Layout shape h(n))
    (hmap : map.Injective) (hmap' : map'.Injective) (h : Disjoint map.range map'.range)
    (idx : Nat) (hidx : idx < n) :
    VectorType.get (self:=v)
      (TensorType.swapSliceSelf (Ks:=Ks) (K:=K) data map map' hmap hmap' h) idx hidx
    =
    if hk : idx ∈ map.rangeNat then
      VectorType.get (self:=v) data (map' (map.rangeNatInv idx hk)) (by get_elem_tactic)
    else if hk : idx ∈ map'.rangeNat then
      VectorType.get (self:=v) data (map (map'.rangeNatInv idx hk)) (by get_elem_tactic)
    else
      VectorType.get (self:=v) data idx hidx := by
  conv_lhs =>
    rw [@VectorType.get_spec Ks K v n
      (TensorType.swapSliceSelf (Ks:=Ks) (K:=K) data map map' hmap hmap' h) idx hidx]
  rw [TensorType.toVector_swapSliceSelf]
  convert (Vector.getElem_swapSliceSelf (α := K) (n := n) (r := r) (shape := shape)
    (data := toVector data) (map := map) (map' := map')
    (hmap := hmap) (hmap' := hmap') (h := h) idx hidx) using 1
  · by_cases hk : idx ∈ map.rangeNat
    · rw [dif_pos hk, dif_pos hk]
      exact VectorType.get_spec data (map' (map.rangeNatInv idx hk)) _
    · rw [dif_neg hk, dif_neg hk]
      by_cases hk' : idx ∈ map'.rangeNat
      · rw [dif_pos hk', dif_pos hk']
        exact VectorType.get_spec data (map (map'.rangeNatInv idx hk')) _
      · rw [dif_neg hk', dif_neg hk']
        exact VectorType.get_spec data idx hidx
  · get_elem_tactic

end TensorType
