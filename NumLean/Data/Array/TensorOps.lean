import NumLean.Data.Vector.Basic
import NumLean.Data.FinHTuple.Basic
import NumLean.Data.FinHTuple.FinHTupleMap
import NumLean.Data.TensorIndex.FinTIndexMap

set_option backward.do.legacy false

namespace NumLean

namespace Vector

open TensorIndex

@[grind =, grind_htuple_order =]
theorem t2 [LT α] {a : HTuple α .leaf} {b : α} : a.toScalar < b ↔ a <ₑ h(b) := by
  get_elem_tactic

set_option pp.coercions false

@[grind ←, grind_htuple_order ←]
theorem t1 {m : Nat}
    {r : HRank} {shape : Shape r} {dstMap : FinHTupleMap shape h(m)} {i : HTuple ℕ r}
    {h : i ∈ 0...shape} :
    (dstMap i).toScalar < m := by
  get_elem_tactic

/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i] -/
def copySlice {K r} {shape : Shape r} [HTuple.Range.ForInProfile r]
    (src : Array K) (srcMap : FinHTupleMap shape h(src.size))
    (dst : Array K) (dstMap : FinHTupleMap shape h(dst.size))
    (_h : dstMap.Injective) : Array K := Id.run do
  let mut dst := dst.toVector
  for h : i in 0...shape do
    dst[dstMap i]'(by apply t1; get_elem_tactic) := src[srcMap i]'(by apply t1; get_elem_tactic)
  return dst.toArray



-- /-- Extract a splice of `src` a nd copies it into a `dst` potentially enlagening `dst` in the process.

-- To preven uninitialized memory we require that dstLayout is compact and that does not start beyond
-- the end of `dst`.
-- If you want to copy into `dst` but with gaps used `copySlice` -/
-- def TensorOps.extractSlice {r} {shape : Shape r} [HTuple.Range.ForInProfile r]
--     (src : Array K) (srcMap : FinTIndexMap shape h(src.size))
--     (dst : Array K) (dstLayout : Layout shape Nat)
--     (h : dstLayout.Compact) (h' : dstLayout.offset ≤ dst.size) : Ks := sorry

-- instance : Coe (FinTIndex (h(m))) (Fin m) := ⟨fun ⟨.leaf val, h⟩ => ⟨val, h⟩⟩

-- /-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i] -/
-- def TensorOps.copySlice {r} {shape : Shape r} [HTuple.Range.ForInProfile r]
--     (src : Vector K n) (srcMap : FinTIndexMap shape h(n))
--     (dst : Vector K m) (dstMap : FinTIndexMap shape h(m))
--     (_h : dstMap.Injective) : Vector K m := Id.run do
--   let mut dst := dst
--   for h : i in 0...shape do
--     dst[dstMap[i]] := src[srcMap[i]]
--   return dst

-- theorem TensorOps.copySlice_in_dst_range {r} {shape : Shape r} [HTuple.Range.ForInProfile r]
--     (src : Vector K n) (srcMap : FinTIndexMap shape h(n))
--     (dst : Vector K m) (dstMap : FinTIndexMap shape h(m))
--     (h : dstMap.Injective) (i : Nat) (hi : i ∈ dstMap.range) : True := sorry


-- /-- this reverse along the first dimension of domain of `map` i.e. swaps src[map (i, j)] with src[map (k-i-1,j)] -/
-- def TensorOps.reverseSlice {n k} {r} {shape : Shape r} [HTuple.Range.ForInProfile r]
--     (xs : Vector K n) (map : FinTIndexMap (.prod (.leaf k) shape) h(n))
--     (_h : map.Injective) : Vector K n := Id.run do
--   let mut xs := xs
--   for h : i in 0...(k/2) do
--     for h : j in 0...shape do
--       let idx  := map[(HTuple.leaf i).prod j]
--       let idx' := map[(HTuple.leaf (k - i - 1)).prod j]
--       xs := xs.swap idx idx'
--   return xs

-- /-- transpose element of `src` based on `map` i.e. swaps src[map (i,j)] with src[map (j,i)]. -/
-- def TensorOps.transposeSlice {r} {shape : Shape r} [HTuple.Range.ForInProfile r]
--     (xs : Vector K n) (map : FinTIndexMap (.prod shape shape) h(n))
--     (_h : map.Injective) : Vector K n := Id.run do
--   let mut xs := xs
--   for h : i in 0...shape do
--     for h : j in 0...shape do
--       let ij := map[i.prod j]
--       let ji := map[j.prod i]
--       if ij.toFin < ji.toFin then
--         xs := xs.swap ij ji
--   return xs

-- /-- swap data between two arrays -/
-- def TensorOps.swapSlice {m n r} {shape : Shape r} [HTuple.Range.ForInProfile r]
--     (xs : Vector K m) (xmap : FinTIndexMap shape h(m))
--     (ys : Vector K n) (ymap : FinTIndexMap shape h(n))
--     (_h : xmap.Injective) (_h' : ymap.Injective) : Vector K m × Vector K n := Id.run do
--   let mut xs := xs
--   let mut ys := ys
--   for h : i in 0...shape do
--     let idx := xmap[i]
--     let jdx := ymap[i]
--     let tmp := xs[idx]
--     xs[idx] := ys[jdx]
--     ys[jdx] := tmp
--   return (xs, ys)


-- /-- Fill a strided tensor-shaped slice with one value. -/
-- def fillTensorSlice {r} (shape : Shape r)
--     (dst : Array K) (dstLayout : Layout shape Nat) (x : K) : Array K :=
--   Id.run do
--     let mut dst := dst
--     for (_linear, jt) in rowMajorIter shape do
--       let di := dstLayout.eval jt
--       if h : di < dst.size then
--         dst := dst.set di x h
--     return dst

-- /-- Copy one strided tensor-shaped slice into another. -/
-- def copyTensorSlice {r} (shape : Shape r)
--     (src : Array K) (srcLayout : Layout shape Nat)
--     (dst : Array K) (dstLayout : Layout shape Nat) : Array K :=
--   Id.run do
--     let mut dst := dst
--     for (_linear, jt) in rowMajorIter shape do
--       let si := srcLayout.eval jt
--       let di := dstLayout.eval jt
--       if hs : si < src.size then
--         if hd : di < dst.size then
--           dst := dst.set di src[si] hd
--     return dst

-- /-- Extract a strided tensor-shaped slice into a dense row-major array. -/
-- def extractTensorSlice [Inhabited K] {r} (shape : Shape r)
--     (src : Array K) (srcLayout : Layout shape Nat) : Array K :=
--   Id.run do
--     let mut out := Array.replicate shape.size default
--     for (oi, jt) in rowMajorIter shape do
--       let si := srcLayout.eval jt
--       if hs : si < src.size then
--         if ho : oi < out.size then
--           out := out.set oi src[si] ho
--     return out

-- end Array

-- end NumLean
