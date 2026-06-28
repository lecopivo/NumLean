module

public import NumLean.Data.Tensor
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


instance : TensorType (Vector α) where
  copySlice := Vector.copySlice
  toVector_copySlice := by intros; rfl
  copySliceSelf := Vector.copySliceSelf
  toVector_copySliceSelf := by intros; rfl
  swapSliceSelf := Vector.swapSliceSelf
  toVector_swapSliceSelf := by intros; rfl
