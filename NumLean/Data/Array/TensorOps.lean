import NumLean.Data.TensorIndex
import NumLean.Data.TensorIndex.FinTIndexMap

namespace NumLean

namespace Array

variable {K : Type u}

open TensorIndex FinTIndex

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
