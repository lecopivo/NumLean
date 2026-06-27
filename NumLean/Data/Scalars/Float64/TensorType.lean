import NumLean.Interfaces.TensorType
import NumLean.Data.Scalars.Float64.VectorType

namespace NumLean
namespace Float64Vector

set_option backward.do.legacy false

open Tensor VectorType

theorem fold_equiv {ρ : Type u} {α : outParam (Type v)}
    {d : outParam (Membership α ρ)} [FoldEntries ρ α d] [Fold ρ] [LawfulFold ρ α d]
    {xs : ρ} {init : Float64Vector n}
    {f : (a : α) → a ∈ xs → Float64Vector n → Float64Vector n} :
    VectorType.toVector (Fold.fold xs init f)
    =
    Fold.fold xs (VectorType.toVector init)
      (fun a ha xs => VectorType.toVector (f a ha (VectorType.fromVector xs))) := by
  rw [LawfulFold.fold_eq_foldl, LawfulFold.fold_eq_foldl]
  induction NumLean.entries xs generalizing init with
  | nil => rfl
  | cons a entries ih =>
      simp only [List.foldl_cons]
      simpa using ih (init := f a.1 a.2 init)

def copySlice {n m} {r : Rank} {shape : Shape r}
    (src : Float64Vector n) (srcMap : Layout shape h(n))
    (dst : Float64Vector m) (dstMap : Layout shape h(m)) :
    Float64Vector m := Id.run do
  let mut dst := dst
  for_all i in 0...shape do
    dst[dstMap i] := src[srcMap i]
  return dst

def copySliceSelf {n} {r : Rank} {shape : Shape r}
    (data : Float64Vector n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n)) :
    Float64Vector n := Id.run do
  let mut data := data
  for_all i in 0...shape do
    data[dstMap i] := data[srcMap i]
  return data

/-- Swap data within one vector through two corresponding disjoint slices. -/
def swapSliceSelf {n} {r : Rank} {shape : Shape r}
    (data : Float64Vector n) (map : Layout shape h(n)) (map' : Layout shape h(n)) :
    Float64Vector n := Id.run do
  let mut data := data
  for_all i in 0...shape do
    data := data.swap (map i) (map' i)
  return data

attribute [simp] VectorType.swap_spec

instance : TensorType Float64Vector where
  copySlice src srcMap dst dstMap _ := Float64Vector.copySlice src srcMap dst dstMap
  toVector_copySlice := by
    intros
    simp [Float64Vector.copySlice, Vector.copySlice, Id.run, pure, bind]
    rw [fold_equiv]
    congr
  copySliceSelf xs srcMap dstMap _ _ := Float64Vector.copySliceSelf xs srcMap dstMap
  toVector_copySliceSelf := by
    intros
    simp [Float64Vector.copySliceSelf, Vector.copySliceSelf, Id.run, pure, bind]
    rw [fold_equiv]
    congr
  swapSliceSelf xs map map' _ _ _ := Float64Vector.swapSliceSelf xs map map'
  toVector_swapSliceSelf := by
    intros
    simp [Float64Vector.swapSliceSelf, Vector.swapSliceSelf, Id.run, pure, bind]
    rw [fold_equiv]
    congr

end Float64Vector
end NumLean
