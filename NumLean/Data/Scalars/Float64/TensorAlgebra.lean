module

public import NumLean.Data.Scalars.Float64.TensorType
public import NumLean.Data.Scalars.Float64.Algebra
public import NumLean.Interfaces.TensorAlgebra

@[expose] public section

namespace NumLean
namespace Float64Vector

set_option backward.do.legacy false

open Tensor VectorType

def tensorSum {r} {n : Nat} {shape : Shape r}
    (xs : Float64Vector n) (xmap : Layout shape h(n)) : Float := Id.run do
  let mut acc := 0
  for_all i in 0...shape do
    acc := acc + xs[xmap i]
  return acc

def tensorAxpy {r} {m n : Nat} {shape : Shape r} (a : Float)
    (xs : Float64Vector n) (xmap : Layout shape h(n))
    (ys : Float64Vector m) (ymap : Layout shape h(m))
    (_hymap : ymap.Injective) : Float64Vector m := Id.run do
  let mut ys := ys
  for_all i in 0...shape do
    ys[ymap i] := ys[ymap i] + a * xs[xmap i]
  return ys

def tensorAxpySelf {r} {n : Nat} {shape : Shape r} (a : Float)
    (data : Float64Vector n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (_hdst : dstMap.Injective) (_h : Disjoint srcMap.range dstMap.range) : Float64Vector n := Id.run do
  let mut data := data
  for_all i in 0...shape do
    data[dstMap i] := data[dstMap i] + a * data[srcMap i]
  return data

def tensorScal {r} {n : Nat} {shape : Shape r} (a : Float)
    (xs : Float64Vector n) (xmap : Layout shape h(n))
    (_hxmap : xmap.Injective) : Float64Vector n := Id.run do
  let mut xs := xs
  for_all i in 0...shape do
    xs[xmap i] := a * xs[xmap i]
  return xs

def tensorDot {r} {m n : Nat} {shape : Shape r}
    (xs : Float64Vector n) (xmap : Layout shape h(n))
    (ys : Float64Vector m) (ymap : Layout shape h(m)) : Float := Id.run do
  let mut acc := 0
  for_all i in 0...shape do
    acc := acc + xs[xmap i] * ys[ymap i]
  return acc

def tensorMul {r} {m n : Nat} {shape : Shape r}
    (xs : Float64Vector n) (xmap : Layout shape h(n))
    (ys : Float64Vector m) (ymap : Layout shape h(m))
    (_hymap : ymap.Injective) : Float64Vector m := Id.run do
  let mut ys := ys
  for_all i in 0...shape do
    ys[ymap i] := ys[ymap i] * xs[xmap i]
  return ys

def tensorGemv {an xn yn : Nat} {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : Float)
    (A : Float64Vector an) (amap : Layout (.prod rows cols) h(an))
    (x : Float64Vector xn) (xmap : Layout cols h(xn))
    (y : Float64Vector yn) (ymap : Layout rows h(yn))
    (_hymap : ymap.Injective) : Float64Vector yn := Id.run do
  let mut y := y
  for_all i in 0...rows do
    let mut acc := 0
    for_all j in 0...cols do
      acc := acc + A[amap (i.prod j)] * x[xmap j]
    y[ymap i] := alpha * acc + beta * y[ymap i]
  return y

def tensorGer {an xn yn : Nat} {rr rc : Rank} {rows : Shape rr} {cols : Shape rc}
    (alpha : Float)
    (x : Float64Vector xn) (xmap : Layout rows h(xn))
    (y : Float64Vector yn) (ymap : Layout cols h(yn))
    (A : Float64Vector an) (amap : Layout (.prod rows cols) h(an))
    (_hamap : amap.Injective) : Float64Vector an := Id.run do
  let mut A := A
  for_all i in 0...rows do
    for_all j in 0...cols do
      A[amap (i.prod j)] := A[amap (i.prod j)] + alpha * x[xmap i] * y[ymap j]
  return A

def tensorGemm {an bn cn : Nat} {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : Float)
    (A : Float64Vector an) (amap : Layout (.prod is ks) h(an))
    (B : Float64Vector bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Float64Vector cn) (cmap : Layout (.prod is js) h(cn))
    (_hcmap : cmap.Injective) : Float64Vector cn := Id.run do
  let mut C := C
  for_all i in 0...is do
    for_all j in 0...js do
      let mut acc := 0
      for_all k in 0...ks do
        acc := acc + A[amap (i.prod k)] * B[bmap (k.prod j)]
      C[cmap (i.prod j)] := alpha * acc + beta * C[cmap (i.prod j)]
  return C

instance : TensorRingOps Float64Vector Float where
  tensorSum := tensorSum
  tensorAxpy := tensorAxpy
  tensorAxpySelf := tensorAxpySelf
  tensorScal := tensorScal
  tensorDot := tensorDot
  tensorMul := tensorMul
  tensorGemv := tensorGemv
  tensorGer := tensorGer
  tensorGemm := tensorGemm

end Float64Vector
end NumLean
