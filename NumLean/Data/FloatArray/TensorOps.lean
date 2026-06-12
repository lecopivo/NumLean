import Batteries.Data.FloatArray

namespace NumLean

namespace FloatArray

private def natArrayGetD (xs : Array Nat) (i : Nat) : Nat :=
  xs.getD i 0

private def numel (counts : Array Nat) : Nat :=
  counts.foldl (init := 1) (· * ·)

private def offsetOfLinear (counts strides : Array Nat) (linear : Nat) : Nat :=
  Id.run do
    let rank := counts.size
    let mut linear := linear
    let mut off := 0
    for rev in [0:rank] do
      let k := rank - 1 - rev
      let count := natArrayGetD counts k
      if count != 0 then
        off := off + (linear % count) * natArrayGetD strides k
        linear := linear / count
    return off

private def fillTensorSliceArray (counts : Array Nat)
    (dst : Array Float) (dstOff : Nat) (dstStrides : Array Nat) (x : Float) : Array Float :=
  Id.run do
    let total := numel counts
    let mut dst := dst
    for linear in [0:total] do
      let di := dstOff + offsetOfLinear counts dstStrides linear
      if h : di < dst.size then
        dst := dst.set di x h
    return dst

private def copyTensorSliceArray (counts : Array Nat)
    (src : Array Float) (srcOff : Nat) (srcStrides : Array Nat)
    (dst : Array Float) (dstOff : Nat) (dstStrides : Array Nat) : Array Float :=
  Id.run do
    let total := numel counts
    let mut dst := dst
    for linear in [0:total] do
      let si := srcOff + offsetOfLinear counts srcStrides linear
      let di := dstOff + offsetOfLinear counts dstStrides linear
      if hs : si < src.size then
        if hd : di < dst.size then
          dst := dst.set di src[si] hd
    return dst

private def extractTensorSliceArray (counts : Array Nat)
    (src : Array Float) (srcOff : Nat) (srcStrides : Array Nat) : Array Float :=
  Id.run do
    let total := numel counts
    let mut out := Array.mkEmpty total
    for linear in [0:total] do
      let si := srcOff + offsetOfLinear counts srcStrides linear
      out := out.push (if h : si < src.size then src[si] else 0.0)
    return out

/-- Reference implementation for filling a strided tensor-shaped slice. -/
def fillTensorSliceRef {rank : Nat} (counts : Vector Nat rank)
    (dst : FloatArray) (dstOff : Nat) (dstStrides : Vector Nat rank) (x : Float) : FloatArray :=
  FloatArray.mk <| fillTensorSliceArray counts.toArray dst.data dstOff dstStrides.toArray x

/-- Reference implementation for copying one strided tensor-shaped slice into another. -/
def copyTensorSliceRef {rank : Nat} (counts : Vector Nat rank)
    (src : FloatArray) (srcOff : Nat) (srcStrides : Vector Nat rank)
    (dst : FloatArray) (dstOff : Nat) (dstStrides : Vector Nat rank) : FloatArray :=
  FloatArray.mk <|
    copyTensorSliceArray counts.toArray src.data srcOff srcStrides.toArray dst.data dstOff dstStrides.toArray

/-- Reference implementation for extracting a strided tensor-shaped slice into a dense array. -/
def extractTensorSliceRef [Inhabited Float] {rank : Nat} (counts : Vector Nat rank)
    (src : FloatArray) (srcOff : Nat) (srcStrides : Vector Nat rank) : FloatArray :=
  FloatArray.mk <| extractTensorSliceArray counts.toArray src.data srcOff srcStrides.toArray

/-- Fill a strided tensor-shaped slice.

Interpreted evaluation uses the Lean body; compiled code uses the native C implementation. -/
def fillTensorSliceCore (counts : @& Array Nat)
    (dst : FloatArray) (dstOff : @& Nat) (dstStrides : @& Array Nat)
    (x : Float) : FloatArray :=
  if h : dstStrides.size = counts.size then
    fillTensorSliceRef (Vector.mk counts rfl) dst dstOff (Vector.mk dstStrides h) x
  else
    dst

@[extern "lean_float_array_fill_tensor_slice"]
def fillTensorSliceCoreNative (counts : @& Array Nat)
    (dst : FloatArray) (dstOff : @& Nat) (dstStrides : @& Array Nat)
    (x : Float) : FloatArray :=
  fillTensorSliceCore counts dst dstOff dstStrides x

@[csimp]
theorem fillTensorSliceCore_eq_native : @fillTensorSliceCore = @fillTensorSliceCoreNative := rfl

/-- Fill a strided tensor-shaped slice using the fast C hook. -/
def fillTensorSlice {rank : Nat} (counts : Vector Nat rank)
    (dst : FloatArray) (dstOff : Nat) (dstStrides : Vector Nat rank)
    (x : Float) : FloatArray :=
  fillTensorSliceCore counts.toArray dst dstOff dstStrides.toArray x

/-- Copy one strided tensor-shaped slice into another.

Interpreted evaluation uses the Lean body; compiled code uses the native C implementation. -/
def copyTensorSliceCore (counts : @& Array Nat)
    (src : @& FloatArray) (srcOff : @& Nat) (srcStrides : @& Array Nat)
    (dst : FloatArray) (dstOff : @& Nat) (dstStrides : @& Array Nat) : FloatArray :=
  if hs : srcStrides.size = counts.size then
    if hd : dstStrides.size = counts.size then
      copyTensorSliceRef (Vector.mk counts rfl) src srcOff (Vector.mk srcStrides hs)
        dst dstOff (Vector.mk dstStrides hd)
    else
      dst
  else
    dst

@[extern "lean_float_array_copy_tensor_slice"]
def copyTensorSliceCoreNative (counts : @& Array Nat)
    (src : @& FloatArray) (srcOff : @& Nat) (srcStrides : @& Array Nat)
    (dst : FloatArray) (dstOff : @& Nat) (dstStrides : @& Array Nat) : FloatArray :=
  copyTensorSliceCore counts src srcOff srcStrides dst dstOff dstStrides

@[csimp]
theorem copyTensorSliceCore_eq_native : @copyTensorSliceCore = @copyTensorSliceCoreNative := rfl

/-- Copy one strided tensor-shaped slice into another using the fast C hook. -/
def copyTensorSlice {rank : Nat} (counts : Vector Nat rank)
    (src : FloatArray) (srcOff : Nat) (srcStrides : Vector Nat rank)
    (dst : FloatArray) (dstOff : Nat) (dstStrides : Vector Nat rank) : FloatArray :=
  copyTensorSliceCore counts.toArray src srcOff srcStrides.toArray dst dstOff dstStrides.toArray

/-- Extract a strided tensor-shaped slice into a dense array.

Interpreted evaluation uses the Lean body; compiled code uses the native C implementation. -/
def extractTensorSliceCore [Inhabited Float] (counts : @& Array Nat)
    (src : @& FloatArray) (srcOff : @& Nat) (srcStrides : @& Array Nat) : FloatArray :=
  if h : srcStrides.size = counts.size then
    extractTensorSliceRef (Vector.mk counts rfl) src srcOff (Vector.mk srcStrides h)
  else
    FloatArray.emptyWithCapacity 0

@[extern "lean_float_array_extract_tensor_slice"]
def extractTensorSliceCoreNative [Inhabited Float] (counts : @& Array Nat)
    (src : @& FloatArray) (srcOff : @& Nat) (srcStrides : @& Array Nat) : FloatArray :=
  extractTensorSliceCore counts src srcOff srcStrides

@[csimp]
theorem extractTensorSliceCore_eq_native : @extractTensorSliceCore = @extractTensorSliceCoreNative := rfl

/-- Extract a strided tensor-shaped slice into a dense row-major array using the fast C hook. -/
def extractTensorSlice [Inhabited Float] {rank : Nat} (counts : Vector Nat rank)
    (src : FloatArray) (srcOff : Nat) (srcStrides : Vector Nat rank) : FloatArray :=
  extractTensorSliceCore counts.toArray src srcOff srcStrides.toArray

end FloatArray

end NumLean
