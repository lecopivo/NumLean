import NumLean.Data.TensorIndex

namespace NumLean

namespace Array

variable {K : Type u}

/-- Fill a strided tensor-shaped slice with one value. -/
def fillTensorSlice {rank : Nat} (counts : Vector Nat rank)
    (dst : Array K) (dstOff : Nat) (dstStrides : Vector Nat rank) (x : K) : Array K :=
  Id.run do
    let mut dst := dst
    for jt in TensorIndex.range counts do
      let di := dstOff + jt.offset dstStrides
      if h : di < dst.size then
        dst := dst.set di x h
    return dst

/-- Copy one strided tensor-shaped slice into another. -/
def copyTensorSlice {rank : Nat} (counts : Vector Nat rank)
    (src : Array K) (srcOff : Nat) (srcStrides : Vector Nat rank)
    (dst : Array K) (dstOff : Nat) (dstStrides : Vector Nat rank) : Array K :=
  Id.run do
    let mut dst := dst
    for jt in TensorIndex.range counts do
      let si := srcOff + jt.offset srcStrides
      let di := dstOff + jt.offset dstStrides
      if hs : si < src.size then
        if hd : di < dst.size then
          dst := dst.set di src[si] hd
    return dst

/-- Extract a strided tensor-shaped slice into a dense row-major array. -/
def extractTensorSlice [Inhabited K] {rank : Nat} (counts : Vector Nat rank)
    (src : Array K) (srcOff : Nat) (srcStrides : Vector Nat rank) : Array K :=
  Id.run do
    let mut out := Array.replicate (TensorIndex.numel counts) default
    let denseStrides := TensorIndex.rowMajorStrides counts
    for jt in TensorIndex.range counts do
      let si := srcOff + jt.offset srcStrides
      let oi := jt.offset denseStrides
      if hs : si < src.size then
        if ho : oi < out.size then
          out := out.set oi src[si] ho
    return out

end Array

end NumLean
