module

public import NumLean.Interfaces.TensorAlgebra
public import NumLean.Data.Scalars.Float64.VectorType
public import NumLean.Data.Scalars.Float64.Algebra

@[expose] public section

namespace NumLean
namespace Float64Vector

set_option backward.do.legacy false

open Tensor VectorType

unsafe def tensorSumImplRec {r} (dim : Nat) (shape : Vector USize r)
    (xs : FloatArray) (xOff : USize) (xStrides : Vector USize r) (acc : Float) :
    Float := Id.run do
  let mut acc := acc
  if dim < r then
    let size := shape[dim]!
    let xStride := xStrides[dim]!
    if dim < r - 1 then
      for_all i in 0...size do
        acc := tensorSumImplRec (dim + 1) shape xs (xOff + i * xStride) xStrides acc
    else if dim == r - 1 then
      for_all i in 0...size do
        acc := acc + xs.uget (xOff + i * xStride) lcProof
  return acc

unsafe def tensorSumImpl {r} {n : Nat} {shape : Shape r}
    (xs : Float64Vector n) (xmap : Layout shape h(n)) : Float :=
  let shape := shape.toVector.map (·.toUSize)
  let xOff := xmap.offset.toScalar.toUSize
  let xStrides := xmap.stride.toVector.map (·.toScalar.toUSize)
  tensorSumImplRec 0 shape xs.data xOff xStrides 0

unsafe def tensorAxpyImplRec {r} (dim : Nat) (shape : Vector USize r) (a : Float)
    (xs : FloatArray) (xOff : USize) (xStrides : Vector USize r)
    (ys : FloatArray) (yOff : USize) (yStrides : Vector USize r) :
    FloatArray := Id.run do
  let mut ys := ys
  if dim < r then
    let size := shape[dim]!
    let xStride := xStrides[dim]!
    let yStride := yStrides[dim]!
    if dim < r - 1 then
      for_all i in 0...size do
        ys := tensorAxpyImplRec (dim + 1) shape a
                xs (xOff + i * xStride) xStrides
                ys (yOff + i * yStride) yStrides
    else if dim == r - 1 then
      for_all i in 0...size do
        let xIdx := xOff + i * xStride
        let yIdx := yOff + i * yStride
        ys := ys.uset yIdx (ys.uget yIdx lcProof + a * xs.uget xIdx lcProof) lcProof
  return ys

unsafe def tensorAxpyImpl {r} {m n : Nat} {shape : Shape r} (a : Float)
    (xs : Float64Vector n) (xmap : Layout shape h(n))
    (ys : Float64Vector m) (ymap : Layout shape h(m))
    (_hymap : ymap.Injective) : Float64Vector m :=
  let shape := shape.toVector.map (·.toUSize)
  let xOff := xmap.offset.toScalar.toUSize
  let xStrides := xmap.stride.toVector.map (·.toScalar.toUSize)
  let yOff := ymap.offset.toScalar.toUSize
  let yStrides := ymap.stride.toVector.map (·.toScalar.toUSize)
  let data := tensorAxpyImplRec 0 shape a xs.data xOff xStrides ys.data yOff yStrides
  ⟨data, lcProof⟩

unsafe def tensorAxpySelfImpl {r} {n : Nat} {shape : Shape r} (a : Float)
    (data : Float64Vector n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (_hdst : dstMap.Injective) (_h : Disjoint srcMap.range dstMap.range) : Float64Vector n :=
  let shape := shape.toVector.map (·.toUSize)
  let srcOff := srcMap.offset.toScalar.toUSize
  let srcStrides := srcMap.stride.toVector.map (·.toScalar.toUSize)
  let dstOff := dstMap.offset.toScalar.toUSize
  let dstStrides := dstMap.stride.toVector.map (·.toScalar.toUSize)
  let data := tensorAxpyImplRec 0 shape a data.data srcOff srcStrides data.data dstOff dstStrides
  ⟨data, lcProof⟩

unsafe def tensorScalImplRec {r} (dim : Nat) (shape : Vector USize r) (a : Float)
    (xs : FloatArray) (xOff : USize) (xStrides : Vector USize r) :
    FloatArray := Id.run do
  let mut xs := xs
  if dim < r then
    let size := shape[dim]!
    let xStride := xStrides[dim]!
    if dim < r - 1 then
      for_all i in 0...size do
        xs := tensorScalImplRec (dim + 1) shape a xs (xOff + i * xStride) xStrides
    else if dim == r - 1 then
      for_all i in 0...size do
        let xIdx := xOff + i * xStride
        xs := xs.uset xIdx (a * xs.uget xIdx lcProof) lcProof
  return xs

unsafe def tensorScalImpl {r} {n : Nat} {shape : Shape r} (a : Float)
    (xs : Float64Vector n) (xmap : Layout shape h(n))
    (_hxmap : xmap.Injective) : Float64Vector n :=
  let shape := shape.toVector.map (·.toUSize)
  let xOff := xmap.offset.toScalar.toUSize
  let xStrides := xmap.stride.toVector.map (·.toScalar.toUSize)
  let data := tensorScalImplRec 0 shape a xs.data xOff xStrides
  ⟨data, lcProof⟩

unsafe def tensorDotImplRec {r} (dim : Nat) (shape : Vector USize r)
    (xs : FloatArray) (xOff : USize) (xStrides : Vector USize r)
    (ys : FloatArray) (yOff : USize) (yStrides : Vector USize r) (acc : Float) :
    Float := Id.run do
  let mut acc := acc
  if dim < r then
    let size := shape[dim]!
    let xStride := xStrides[dim]!
    let yStride := yStrides[dim]!
    if dim < r - 1 then
      for_all i in 0...size do
        acc := tensorDotImplRec (dim + 1) shape
                xs (xOff + i * xStride) xStrides
                ys (yOff + i * yStride) yStrides acc
    else if dim == r - 1 then
      for_all i in 0...size do
        acc := acc + xs.uget (xOff + i * xStride) lcProof * ys.uget (yOff + i * yStride) lcProof
  return acc

unsafe def tensorDotImpl {r} {m n : Nat} {shape : Shape r}
    (xs : Float64Vector n) (xmap : Layout shape h(n))
    (ys : Float64Vector m) (ymap : Layout shape h(m)) : Float :=
  let shape := shape.toVector.map (·.toUSize)
  let xOff := xmap.offset.toScalar.toUSize
  let xStrides := xmap.stride.toVector.map (·.toScalar.toUSize)
  let yOff := ymap.offset.toScalar.toUSize
  let yStrides := ymap.stride.toVector.map (·.toScalar.toUSize)
  tensorDotImplRec 0 shape xs.data xOff xStrides ys.data yOff yStrides 0

unsafe def tensorMulImplRec {r} (dim : Nat) (shape : Vector USize r)
    (xs : FloatArray) (xOff : USize) (xStrides : Vector USize r)
    (ys : FloatArray) (yOff : USize) (yStrides : Vector USize r) :
    FloatArray := Id.run do
  let mut ys := ys
  if dim < r then
    let size := shape[dim]!
    let xStride := xStrides[dim]!
    let yStride := yStrides[dim]!
    if dim < r - 1 then
      for_all i in 0...size do
        ys := tensorMulImplRec (dim + 1) shape
                xs (xOff + i * xStride) xStrides
                ys (yOff + i * yStride) yStrides
    else if dim == r - 1 then
      for_all i in 0...size do
        let xIdx := xOff + i * xStride
        let yIdx := yOff + i * yStride
        ys := ys.uset yIdx (ys.uget yIdx lcProof * xs.uget xIdx lcProof) lcProof
  return ys

unsafe def tensorMulImpl {r} {m n : Nat} {shape : Shape r}
    (xs : Float64Vector n) (xmap : Layout shape h(n))
    (ys : Float64Vector m) (ymap : Layout shape h(m))
    (_hymap : ymap.Injective) : Float64Vector m :=
  let shape := shape.toVector.map (·.toUSize)
  let xOff := xmap.offset.toScalar.toUSize
  let xStrides := xmap.stride.toVector.map (·.toScalar.toUSize)
  let yOff := ymap.offset.toScalar.toUSize
  let yStrides := ymap.stride.toVector.map (·.toScalar.toUSize)
  let data := tensorMulImplRec 0 shape xs.data xOff xStrides ys.data yOff yStrides
  ⟨data, lcProof⟩

unsafe def tensorGemvRowsImplRec {rr rc} (dim : Nat)
    (rows : Vector USize rr) (cols : Vector USize rc) (alpha beta : Float)
    (A : FloatArray) (aOff : USize) (aRowStrides : Vector USize rr) (aColStrides : Vector USize rc)
    (x : FloatArray) (xOff : USize) (xStrides : Vector USize rc)
    (y : FloatArray) (yOff : USize) (yStrides : Vector USize rr) :
    FloatArray := Id.run do
  let mut y := y
  if dim < rr then
    let size := rows[dim]!
    let aRowStride := aRowStrides[dim]!
    let yStride := yStrides[dim]!
    if dim < rr - 1 then
      for_all i in 0...size do
        y := tensorGemvRowsImplRec (dim + 1) rows cols alpha beta
              A (aOff + i * aRowStride) aRowStrides aColStrides
              x xOff xStrides
              y (yOff + i * yStride) yStrides
    else if dim == rr - 1 then
      for_all i in 0...size do
        let aBase := aOff + i * aRowStride
        let yIdx := yOff + i * yStride
        let acc := tensorDotImplRec 0 cols A aBase aColStrides x xOff xStrides 0
        y := y.uset yIdx (alpha * acc + beta * y.uget yIdx lcProof) lcProof
  return y

unsafe def tensorGemvImpl {an xn yn : Nat} {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : Float)
    (A : Float64Vector an) (amap : Layout (.prod rows cols) h(an))
    (x : Float64Vector xn) (xmap : Layout cols h(xn))
    (y : Float64Vector yn) (ymap : Layout rows h(yn))
    (_hymap : ymap.Injective) : Float64Vector yn :=
  let rows := rows.toVector.map (·.toUSize)
  let cols := cols.toVector.map (·.toUSize)
  let aOff := amap.offset.toScalar.toUSize
  let aRowStrides := amap.stride.fst.toVector.map (·.toScalar.toUSize)
  let aColStrides := amap.stride.snd.toVector.map (·.toScalar.toUSize)
  let xOff := xmap.offset.toScalar.toUSize
  let xStrides := xmap.stride.toVector.map (·.toScalar.toUSize)
  let yOff := ymap.offset.toScalar.toUSize
  let yStrides := ymap.stride.toVector.map (·.toScalar.toUSize)
  let data := tensorGemvRowsImplRec 0 rows cols alpha beta
    A.data aOff aRowStrides aColStrides
    x.data xOff xStrides
    y.data yOff yStrides
  ⟨data, lcProof⟩

unsafe def tensorGerColsImplRec {rc} (dim : Nat) (cols : Vector USize rc) (alpha xVal : Float)
    (y : FloatArray) (yOff : USize) (yStrides : Vector USize rc)
    (A : FloatArray) (aOff : USize) (aColStrides : Vector USize rc) :
    FloatArray := Id.run do
  let mut A := A
  if dim < rc then
    let size := cols[dim]!
    let yStride := yStrides[dim]!
    let aColStride := aColStrides[dim]!
    if dim < rc - 1 then
      for_all j in 0...size do
        A := tensorGerColsImplRec (dim + 1) cols alpha xVal
              y (yOff + j * yStride) yStrides
              A (aOff + j * aColStride) aColStrides
    else if dim == rc - 1 then
      for_all j in 0...size do
        let yIdx := yOff + j * yStride
        let aIdx := aOff + j * aColStride
        A := A.uset aIdx (A.uget aIdx lcProof + alpha * xVal * y.uget yIdx lcProof) lcProof
  return A

unsafe def tensorGerRowsImplRec {rr rc} (dim : Nat)
    (rows : Vector USize rr) (cols : Vector USize rc) (alpha : Float)
    (x : FloatArray) (xOff : USize) (xStrides : Vector USize rr)
    (y : FloatArray) (yOff : USize) (yStrides : Vector USize rc)
    (A : FloatArray) (aOff : USize) (aRowStrides : Vector USize rr) (aColStrides : Vector USize rc) :
    FloatArray := Id.run do
  let mut A := A
  if dim < rr then
    let size := rows[dim]!
    let xStride := xStrides[dim]!
    let aRowStride := aRowStrides[dim]!
    if dim < rr - 1 then
      for_all i in 0...size do
        A := tensorGerRowsImplRec (dim + 1) rows cols alpha
              x (xOff + i * xStride) xStrides
              y yOff yStrides
              A (aOff + i * aRowStride) aRowStrides aColStrides
    else if dim == rr - 1 then
      for_all i in 0...size do
        let xIdx := xOff + i * xStride
        let aBase := aOff + i * aRowStride
        A := tensorGerColsImplRec 0 cols alpha (x.uget xIdx lcProof)
              y yOff yStrides A aBase aColStrides
  return A

unsafe def tensorGerImpl {an xn yn : Nat} {rr rc : Rank} {rows : Shape rr} {cols : Shape rc}
    (alpha : Float)
    (x : Float64Vector xn) (xmap : Layout rows h(xn))
    (y : Float64Vector yn) (ymap : Layout cols h(yn))
    (A : Float64Vector an) (amap : Layout (.prod rows cols) h(an))
    (_hamap : amap.Injective) : Float64Vector an :=
  let rows := rows.toVector.map (·.toUSize)
  let cols := cols.toVector.map (·.toUSize)
  let xOff := xmap.offset.toScalar.toUSize
  let xStrides := xmap.stride.toVector.map (·.toScalar.toUSize)
  let yOff := ymap.offset.toScalar.toUSize
  let yStrides := ymap.stride.toVector.map (·.toScalar.toUSize)
  let aOff := amap.offset.toScalar.toUSize
  let aRowStrides := amap.stride.fst.toVector.map (·.toScalar.toUSize)
  let aColStrides := amap.stride.snd.toVector.map (·.toScalar.toUSize)
  let data := tensorGerRowsImplRec 0 rows cols alpha
    x.data xOff xStrides
    y.data yOff yStrides
    A.data aOff aRowStrides aColStrides
  ⟨data, lcProof⟩

unsafe def tensorGemmJsImplRec {rj rk} (dim : Nat)
    (js : Vector USize rj) (ks : Vector USize rk) (alpha beta : Float)
    (A : FloatArray) (aOff : USize) (aKStrides : Vector USize rk)
    (B : FloatArray) (bOff : USize) (bJStrides : Vector USize rj) (bKStrides : Vector USize rk)
    (C : FloatArray) (cOff : USize) (cJStrides : Vector USize rj) :
    FloatArray := Id.run do
  let mut C := C
  if dim < rj then
    let size := js[dim]!
    let bJStride := bJStrides[dim]!
    let cJStride := cJStrides[dim]!
    if dim < rj - 1 then
      for_all j in 0...size do
        C := tensorGemmJsImplRec (dim + 1) js ks alpha beta
              A aOff aKStrides
              B (bOff + j * bJStride) bJStrides bKStrides
              C (cOff + j * cJStride) cJStrides
    else if dim == rj - 1 then
      for_all j in 0...size do
        let bBase := bOff + j * bJStride
        let cIdx := cOff + j * cJStride
        let acc := tensorDotImplRec 0 ks A aOff aKStrides B bBase bKStrides 0
        C := C.uset cIdx (alpha * acc + beta * C.uget cIdx lcProof) lcProof
  return C

unsafe def tensorGemmIsImplRec {ri rj rk} (dim : Nat)
    (is : Vector USize ri) (js : Vector USize rj) (ks : Vector USize rk) (alpha beta : Float)
    (A : FloatArray) (aOff : USize) (aIStrides : Vector USize ri) (aKStrides : Vector USize rk)
    (B : FloatArray) (bOff : USize) (bJStrides : Vector USize rj) (bKStrides : Vector USize rk)
    (C : FloatArray) (cOff : USize) (cIStrides : Vector USize ri) (cJStrides : Vector USize rj) :
    FloatArray := Id.run do
  let mut C := C
  if dim < ri then
    let size := is[dim]!
    let aIStride := aIStrides[dim]!
    let cIStride := cIStrides[dim]!
    if dim < ri - 1 then
      for_all i in 0...size do
        C := tensorGemmIsImplRec (dim + 1) is js ks alpha beta
              A (aOff + i * aIStride) aIStrides aKStrides
              B bOff bJStrides bKStrides
              C (cOff + i * cIStride) cIStrides cJStrides
    else if dim == ri - 1 then
      for_all i in 0...size do
        C := tensorGemmJsImplRec 0 js ks alpha beta
              A (aOff + i * aIStride) aKStrides
              B bOff bJStrides bKStrides
              C (cOff + i * cIStride) cJStrides
  return C

unsafe def tensorGemmImpl {an bn cn : Nat} {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : Float)
    (A : Float64Vector an) (amap : Layout (.prod is ks) h(an))
    (B : Float64Vector bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Float64Vector cn) (cmap : Layout (.prod is js) h(cn))
    (_hcmap : cmap.Injective) : Float64Vector cn :=
  let is := is.toVector.map (·.toUSize)
  let js := js.toVector.map (·.toUSize)
  let ks := ks.toVector.map (·.toUSize)
  let aOff := amap.offset.toScalar.toUSize
  let aIStrides := amap.stride.fst.toVector.map (·.toScalar.toUSize)
  let aKStrides := amap.stride.snd.toVector.map (·.toScalar.toUSize)
  let bOff := bmap.offset.toScalar.toUSize
  let bKStrides := bmap.stride.fst.toVector.map (·.toScalar.toUSize)
  let bJStrides := bmap.stride.snd.toVector.map (·.toScalar.toUSize)
  let cOff := cmap.offset.toScalar.toUSize
  let cIStrides := cmap.stride.fst.toVector.map (·.toScalar.toUSize)
  let cJStrides := cmap.stride.snd.toVector.map (·.toScalar.toUSize)
  let data := tensorGemmIsImplRec 0 is js ks alpha beta
    A.data aOff aIStrides aKStrides
    B.data bOff bJStrides bKStrides
    C.data cOff cIStrides cJStrides
  ⟨data, lcProof⟩

end Float64Vector
end NumLean
