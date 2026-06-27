import NumLean.Interfaces.TensorAlgebra
import NumLean.Data.Scalars.Float64.Float64Vector

namespace NumLean

namespace Float64Vector

set_option backward.do.legacy false

theorem fold_equiv {ρ : Type u} {α : outParam (Type v)}
    {d : outParam (Membership α ρ)} [FoldEntries ρ α d] [Fold ρ]
    {xs : ρ} {init : β} {f : (a : α) → a ∈ xs → β → β} (g : β ≃ γ) :
    g (Fold.fold xs init f) = Fold.fold xs (g init) (fun a ha b => g (f a ha (g.symm b))) := sorry

open VectorType in
theorem fold_equiv' {ρ : Type u} {α : outParam (Type v)}
    {d : outParam (Membership α ρ)} [FoldEntries ρ α d] [Fold ρ]
    {xs : ρ} {init : Float64Vector n} {f : (a : α) → a ∈ xs → Float64Vector n → Float64Vector n} :
    VectorType.toVector (Fold.fold xs (init) f)
    =
    Fold.fold xs (toVector init) (fun a ha xs => toVector (f a ha (fromVector xs))) := sorry

def extractSliceImpl {n m} {r : HTuple.Profile} {shape : HTuple Nat r} (k : Nat)
    (src : Float64Vector n) (srcMap : FinHTupleMap shape h(n))
    (dst : Float64Vector m) (dstMap : FinHTupleMap shape h(max m k))
    (_h : dstMap.Injective) : Float64Vector (max m k) := Id.run do
  let mut dst := dst.append (.replicate (k-m) default) |>.cast (m:=(max m k)) (by grind)
  for_all i in 0...shape do
    dst[dstMap i] := src[srcMap i]
  return dst

def extractSlice {n m} {r : HTuple.Profile} {shape : HTuple Nat r} (k : Nat)
    (src : Float64Vector n) (srcMap : FinHTupleMap shape h(n))
    (dst : Float64Vector m) (dstMap : FinHTupleMap shape h(max m k))
    (_h : dstMap.Injective) : Float64Vector (max m k) := Id.run do
  let mut dst := dst.append (.replicate (k-m) default) |>.cast (m:=(max m k)) (by grind)
  for_all i in 0...shape do
    dst[dstMap i] := src[srcMap i]
  return dst

unsafe def copySliceRecImpl (r : Nat) (shape : Array USize) (dim : USize)
    (src : FloatArray) (srcOff : USize) (srcStrides : Array USize)
    (dst : FloatArray) (dstOff : USize) (dstStrides : Array USize) :
    FloatArray := Id.run do
  let mut dst := dst
  let dsize := shape.uget dim lcProof
  if dim = r.toUSize - 1 then
    for_all k in 0...dsize do
      let srcOff' := srcOff + k * srcStrides.uget dim lcProof
      let dstOff' := dstOff + k * dstStrides.uget dim lcProof
      dst := dst.uset dstOff' (src.uget srcOff' lcProof) lcProof
    return dst
  else if dim < r.toUSize - 1 then
    for_all k in 0...dsize do
      let srcOff' := srcOff + k * srcStrides.uget dim lcProof
      let dstOff' := dstOff + k * dstStrides.uget dim lcProof
      dst := copySliceRecImpl r shape (dim+1) src srcOff' srcStrides dst dstOff' dstStrides
    return dst
  else
    panic! s!"Invalid dimension {dim} for rank {r}!"

-- for some reason this function makes the file impossible to compile
-- unsafe def copySliceImpl {n m} {r : HTuple.Profile} {shape : HTuple Nat r}
--     (src : Float64Vector n) (srcMap : FinHTupleMap shape h(n))
--     (dst : Float64Vector m) (dstMap : FinHTupleMap shape h(m))
--     (_h : dstMap.Injective) : Float64Vector m := Id.run do
--   let rank := r.size
--   let shape := shape.toList.toArray.map (·.toUSize)
--   let srcOff := srcMap.1.offset.toScalar.toUSize
--   let srcStrides := srcMap.1.stride.toList.toArray.map (·.toScalar.toUSize)
--   let dstOff := dstMap.1.offset.toScalar.toUSize
--   let dstStrides := dstMap.1.stride.toList.toArray.map (·.toScalar.toUSize)
--   let data := copySliceRecImpl rank shape 0 src.data srcOff srcStrides dst.data dstOff dstStrides
--   return ⟨data, lcProof⟩

-- @[implemented_by copySliceImpl]
def copySlice {n m} {r : HTuple.Profile} {shape : HTuple Nat r}
    (src : Float64Vector n) (srcMap : FinHTupleMap shape h(n))
    (dst : Float64Vector m) (dstMap : FinHTupleMap shape h(m))
    (_h : dstMap.Injective) : Float64Vector m := Id.run do
  let mut dst := dst
  for_all i in 0...shape do
    dst[dstMap i]'sorry := src[srcMap i]'sorry
  return dst

/-- Reverse along the first dimension of the domain of `map`, swapping
`xs[map (i, j)]` with `xs[map (k - i - 1, j)]`. -/
def reverseSlice {n k} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Float64Vector n) (map : FinHTupleMap (.prod (.leaf k) shape) h(n))
    (_h : map.Injective) : Float64Vector n := Id.run do
  let mut xs := xs
  for_all i in (0 : Nat)...(k / 2) do
    for_all j in (0 : HTuple Nat r)...shape do
      let idx := map ((HTuple.leaf i).prod j)
      let idx' := map ((HTuple.leaf (k - i - 1)).prod j)
      xs := xs.swap idx idx'
  return xs

/-- Transpose elements of `xs` based on `map`, swapping `xs[map (i,j)]` with `xs[map (j,i)]`. -/
def transposeSlice {n} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Float64Vector n) (map : FinHTupleMap (.prod shape shape) h(n))
    (_h : map.Injective) : Float64Vector n := Id.run do
  let mut xs := xs
  for_all i in (0 : HTuple Nat r)...shape do
    for_all j in (0 : HTuple Nat r)...shape do
      let ij := map (i.prod j)
      let ji := map (j.prod i)
      if ij.toScalar < ji then
        xs := xs.swap ij ji
  return xs

/-- Swap data within one vector through two corresponding disjoint slices. -/
def swapSliceSelf {n} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Float64Vector n) (map : FinHTupleMap shape h(n)) (map' : FinHTupleMap shape h(n))
    (_h : map.Injective) (_h' : map'.Injective) (_hdisjoint : Disjoint map.range map'.range) :
    Float64Vector n := Id.run do
  let mut xs := xs
  for_all i in (0 : HTuple Nat r)...shape do
    let idx := map i
    let jdx := map' i
    xs := xs.swap idx jdx
  return xs

/-- Swap data between two vectors through corresponding slices. -/
def swapSlice {m n} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Float64Vector m) (xmap : FinHTupleMap shape h(m))
    (ys : Float64Vector n) (ymap : FinHTupleMap shape h(n))
    (_h : xmap.Injective) (_h' : ymap.Injective) : Float64Vector m × Float64Vector n := Id.run do
  let mut xs := xs
  let mut ys := ys
  for_all i in (0 : HTuple Nat r)...shape do
    let idx := xmap i
    let jdx := ymap i
    let tmp := xs[idx]
    xs[idx] := ys[jdx]
    ys[jdx] := tmp
  return (xs, ys)

def vectorEquiv : Float64Vector n ≃ Vector Float64 n := sorry

attribute [simp] VectorType.swap_spec

-- instance : TensorType Float64Vector Float64 where
--   extractSlice := extractSlice
--   copySlice := copySlice
--   copySlice_spec := by
--     intros
--     simp [copySlice, Vector.ForAll.copySlice, Id.run, pure, bind]
--     rw [fold_equiv']
--     congr
--   reverseSlice := reverseSlice
--   reverseSlice_spec := by
--     intros
--     simp [reverseSlice, Vector.ForAll.reverseSlice, Id.run, pure, bind]
--     rw [fold_equiv']
--     congr; funext i h xs
--     rw [fold_equiv']
--     congr
--   transposeSlice := transposeSlice
--   transposeSlice_spec := by
--     intros
--     simp [transposeSlice, Vector.ForAll.transposeSlice, Id.run, pure, bind]
--     rw [fold_equiv']
--     congr; funext i h xs
--     rw [fold_equiv']
--     congr; funext j h xs
--     split_ifs
--     · sorry -- erw [VectorType.swap_spec]
--     · simp
--   swapSliceSelf := swapSliceSelf
--   swapSlice := swapSlice
--   swapSlice_spec := by
--     intros _ _ _ _ _ _ _ _ _ _
--     simp [swapSlice, Vector.ForAll.swapSlice, Id.run, pure, bind]
--     sorry

-- instance : TensorRingOps Float64Vector Float64 .leaf where
--   tensorSum := sorry
--   tensorScal := sorry
--   tensorMul := sorry
--   tensorProd := sorry
--   tensorAxpy := sorry
--   tensorDot := sorry
--   tensorNeg := sorry
--   tensorSub := sorry
