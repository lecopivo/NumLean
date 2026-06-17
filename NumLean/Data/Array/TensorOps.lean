import NumLean.Data.TensorIndex
import NumLean.Data.HTuple
import NumLean.Data.HTuple.RangeIterator
import NumLean.Data.HTuple.GetElemTactic
import NumLean.Data.TensorIndex.FinTIndexMap
import NumLean.Interfaces.SetElem

namespace NumLean

namespace Array

variable {K : Type}

open TensorIndex FinTIndex

instance : SetElem (Array α) Nat α (fun xs i => i < xs.size) where
  setElem xs i x h := xs.set i x h
  setElem_valid := by intros; simp

instance : SetElem (Vector α n) Nat α (fun xs i => i < n) where
  setElem xs i x h := xs.set i x h
  setElem_valid := by intros; simp

instance : SetElem (Vector α n) (Fin n) α (fun xs i => True) where
  setElem xs i x h := xs.set i.1 x i.2
  setElem_valid := by intros; simp

@[coe]
def _root_.NumLean.TensorIndex.FinTIndex.toFin {n} (i : FinTIndex (.leaf n)) : Fin n :=
  match i with
  | ⟨.leaf i, h⟩ => ⟨i, h⟩

instance : Coe (FinTIndex (.leaf n)) (Fin n) := ⟨fun i => i.toFin⟩
instance : CoeOut (FinTIndex (.leaf n)) Nat := ⟨fun i => i.toFin⟩

variable {n} (i : FinTIndex h(n)) (j : Fin n)

instance [GetElem cont (Fin n) elem dom] :
    GetElem cont (FinTIndex (.leaf n)) elem (fun xs i => dom xs i.toFin) where
  getElem xs i h := xs[i.toFin]'h

instance [SetElem cont (Fin n) elem dom] :
    SetElem cont (FinTIndex (.leaf n)) elem (fun xs i => dom xs i.toFin) where
  setElem xs i x h := setElem xs i.toFin x h
  setElem_valid := sorry

@[simp]
theorem getElem_toFin [GetElem cont (Fin n) elem dom] (xs : cont) (i : FinTIndex (.leaf n)) (h) :
  xs[i]'h = xs[i.toFin] := by rfl


-- a[i] := x
macro (priority:=high) x:ident noWs "[" i:term "]" " := " xi:term : doElem => do
  `(doElem| $x:ident := setElem $x $i $xi (by get_elem_tactic))


/-- Extract a splice of `src` a nd copies it into a `dst` potentially enlagening `dst` in the process.

To preven uninitialized memory we require that dstLayout is compact and that does not start beyond
the end of `dst`.
If you want to copy into `dst` but with gaps used `copySlice` -/
def TensorOps.extractSlice {r} {shape : Shape r} [HTuple.Range.ForInProfile r]
    (src : Array K) (srcMap : FinTIndexMap shape h(src.size))
    (dst : Array K) (dstLayout : Layout shape Nat)
    (h : dstLayout.Compact) (h' : dstLayout.offset ≤ dst.size) : Ks := sorry

instance : Coe (FinTIndex (h(m))) (Fin m) := ⟨fun ⟨.leaf val, h⟩ => ⟨val, h⟩⟩

/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i] -/
def TensorOps.copySlice {r} {shape : Shape r} [HTuple.Range.ForInProfile r]
    (src : Vector K n) (srcMap : FinTIndexMap shape h(n))
    (dst : Vector K m) (dstMap : FinTIndexMap shape h(m))
    (_h : dstMap.Injective) : Vector K m := Id.run do
  let mut dst := dst
  for h : i in 0...shape do
    dst[dstMap[i]] := src[srcMap[i]]
  return dst

/-- this reverse along the first dimension of domain of `map` i.e. swaps src[map (i, j)] with src[map (k-i-1,j)] -/
def TensorOps.reverseSlice {n k} {r} {shape : Shape r} [HTuple.Range.ForInProfile r]
    (xs : Vector K n) (map : FinTIndexMap (.prod (.leaf k) shape) h(n))
    (_h : map.Injective) : Vector K n := Id.run do
  let mut xs := xs
  for h : i in 0...(k/2) do
    for h : j in 0...shape do
      let idx  := map[(HTuple.leaf i).prod j]
      let idx' := map[(HTuple.leaf (k - i - 1)).prod j]
      xs := xs.swap idx idx'
  return xs

/-- transpose element of `src` based on `map` i.e. swaps src[map (i,j)] with src[map (j,i)]. -/
def TensorOps.transposeSlice {r} {shape : Shape r} [HTuple.Range.ForInProfile r]
    (xs : Vector K n) (map : FinTIndexMap (.prod shape shape) h(n))
    (_h : map.Injective) : Vector K n := Id.run do
  let mut xs := xs
  for h : i in 0...shape do
    for h : j in 0...shape do
      let ij := map[i.prod j]
      let ji := map[j.prod i]
      if ij.toFin < ji.toFin then
        xs := xs.swap ij ji
  return xs

/-- swap data between two arrays -/
def TensorOps.swapSlice {m n r} {shape : Shape r} [HTuple.Range.ForInProfile r]
    (xs : Vector K m) (xmap : FinTIndexMap shape h(m))
    (ys : Vector K n) (ymap : FinTIndexMap shape h(n))
    (_h : xmap.Injective) (_h' : ymap.Injective) : Vector K m × Vector K n := Id.run do
  let mut xs := xs
  let mut ys := ys
  for h : i in 0...shape do
    let idx := xmap[i]
    let jdx := ymap[i]
    let tmp := xs[idx]
    xs[idx] := ys[jdx]
    ys[jdx] := tmp
  return (xs, ys)


/-- Fill a strided tensor-shaped slice with one value. -/
def fillTensorSlice {r} (shape : Shape r)
    (dst : Array K) (dstLayout : Layout shape Nat) (x : K) : Array K :=
  Id.run do
    let mut dst := dst
    for (_linear, jt) in rowMajorIter shape do
      let di := dstLayout.eval jt
      if h : di < dst.size then
        dst := dst.set di x h
    return dst

/-- Copy one strided tensor-shaped slice into another. -/
def copyTensorSlice {r} (shape : Shape r)
    (src : Array K) (srcLayout : Layout shape Nat)
    (dst : Array K) (dstLayout : Layout shape Nat) : Array K :=
  Id.run do
    let mut dst := dst
    for (_linear, jt) in rowMajorIter shape do
      let si := srcLayout.eval jt
      let di := dstLayout.eval jt
      if hs : si < src.size then
        if hd : di < dst.size then
          dst := dst.set di src[si] hd
    return dst

/-- Extract a strided tensor-shaped slice into a dense row-major array. -/
def extractTensorSlice [Inhabited K] {r} (shape : Shape r)
    (src : Array K) (srcLayout : Layout shape Nat) : Array K :=
  Id.run do
    let mut out := Array.replicate shape.size default
    for (oi, jt) in rowMajorIter shape do
      let si := srcLayout.eval jt
      if hs : si < src.size then
        if ho : oi < out.size then
          out := out.set oi src[si] ho
    return out

end Array

end NumLean
