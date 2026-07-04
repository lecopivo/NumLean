module

public import NumLean.Interfaces.TensorType
public import NumLean.Data.Scalars.Float64.VectorType

@[expose] public section

namespace NumLean
namespace Float64Vector

set_option backward.do.legacy false

open Tensor VectorType

unsafe def copySliceImplRec {r} (dim : Nat) (shape : Vector USize r)
    (src : FloatArray) (srcOff : USize) (srcStrides : Vector USize r)
    (dst : FloatArray) (dstOff : USize) (dstStrides : Vector USize r) :
    FloatArray := Id.run do
  let mut dst := dst
  if dim < r then
    let size := shape[dim]!
    let srcStride := srcStrides[dim]!
    let dstStride := dstStrides[dim]!
    if dim < r - 1 then
      for_all i in 0...size do
        dst := copySliceImplRec (dim + 1) shape
                 src (srcOff + i * srcStride) srcStrides
                 dst (dstOff + i * dstStride) dstStrides
    else if dim == r - 1 then
      for_all i in 0...size do
        let srcIdx := srcOff + i * srcStride
        let dstIdx := dstOff + i * dstStride
        dst := dst.uset dstIdx (src.uget srcIdx lcProof) lcProof
  return dst

unsafe def copySliceImpl {n m} {r : Rank} {shape : Shape r}
    (src : Float64Vector n) (srcMap : Layout shape h(n))
    (dst : Float64Vector m) (dstMap : Layout shape h(m)) :
    Float64Vector m :=
  let shape := shape.toVector.map (·.toUSize)
  let srcOff := srcMap.offset.toScalar.toUSize
  let srcStrides := srcMap.stride.toVector.map (·.toScalar.toUSize)
  let dstOff := dstMap.offset.toScalar.toUSize
  let dstStrides := dstMap.stride.toVector.map (·.toScalar.toUSize)
  let data := copySliceImplRec 0 shape
    src.data srcOff srcStrides
    dst.data dstOff dstStrides
  ⟨data, lcProof⟩

unsafe def copySliceSelfImplRec {r} (dim : Nat) (shape : Vector USize r)
    (data : FloatArray) (srcOff : USize) (srcStrides : Vector USize r)
    (dstOff : USize) (dstStrides : Vector USize r) :
    FloatArray := Id.run do
  let mut data := data
  if dim < r then
    let size := shape[dim]!
    let srcStride := srcStrides[dim]!
    let dstStride := dstStrides[dim]!
    if dim < r - 1 then
      for_all i in 0...size do
        data := copySliceSelfImplRec (dim + 1) shape
                  data (srcOff + i * srcStride) srcStrides
                  (dstOff + i * dstStride) dstStrides
    else if dim == r - 1 then
      for_all i in 0...size do
        let srcIdx := srcOff + i * srcStride
        let dstIdx := dstOff + i * dstStride
        data := data.uset dstIdx (data.uget srcIdx lcProof) lcProof
  return data

unsafe def copySliceSelfImpl {n} {r : Rank} {shape : Shape r}
    (data : Float64Vector n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n)) :
    Float64Vector n :=
  let shape := shape.toVector.map (·.toUSize)
  let srcOff := srcMap.offset.toScalar.toUSize
  let srcStrides := srcMap.stride.toVector.map (·.toScalar.toUSize)
  let dstOff := dstMap.offset.toScalar.toUSize
  let dstStrides := dstMap.stride.toVector.map (·.toScalar.toUSize)
  let data := copySliceSelfImplRec 0 shape
    data.data srcOff srcStrides
    dstOff dstStrides
  ⟨data, lcProof⟩

unsafe def swapSliceSelfImplRec {r} (dim : Nat) (shape : Vector USize r)
    (data : FloatArray) (off : USize) (strides : Vector USize r)
    (off' : USize) (strides' : Vector USize r) :
    FloatArray := Id.run do
  let mut data := data
  if dim < r then
    let size := shape[dim]!
    let stride := strides[dim]!
    let stride' := strides'[dim]!
    if dim < r - 1 then
      for_all i in 0...size do
        data := swapSliceSelfImplRec (dim + 1) shape
                  data (off + i * stride) strides
                  (off' + i * stride') strides'
    else if dim == r - 1 then
      for_all i in 0...size do
        let idx := off + i * stride
        let idx' := off' + i * stride'
        let x := data.uget idx lcProof
        let x' := data.uget idx' lcProof
        data := data.uset idx x' lcProof
        data := data.uset idx' x lcProof
  return data

unsafe def swapSliceSelfImpl {n} {r : Rank} {shape : Shape r}
    (data : Float64Vector n) (map : Layout shape h(n)) (map' : Layout shape h(n)) :
    Float64Vector n :=
  let shape := shape.toVector.map (·.toUSize)
  let off := map.offset.toScalar.toUSize
  let strides := map.stride.toVector.map (·.toScalar.toUSize)
  let off' := map'.offset.toScalar.toUSize
  let strides' := map'.stride.toVector.map (·.toScalar.toUSize)
  let data := swapSliceSelfImplRec 0 shape
    data.data off strides
    off' strides'
  ⟨data, lcProof⟩
