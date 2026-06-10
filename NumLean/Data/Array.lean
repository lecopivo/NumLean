
def Array.copySlice {α} (n : Nat)
    (src : Array α) (srcOff srcInc : Nat)
    (dst : Array α) (dstOff dstInc : Nat) : Array α := Id.run do
  let mut dst := dst
  for i in [0:n] do
    let srcIdx := srcOff + i * srcInc
    let dstIdx := dstOff + i * dstInc
    if h : srcIdx < src.size ∧ dstIdx < dst.size then
      dst := dst.set dstIdx src[srcIdx]
  return dst

def Array.extractSlice {α} (n : Nat)
    (src : Array α) (srcOff srcInc : Nat) : Array α := Id.run do
  let mut r : Array α := .emptyWithCapacity n
  for i in [0:n] do
    let srcIdx := srcOff + i * srcInc
    if h : srcIdx < src.size then
      r := r.push src[srcIdx]
  return r
