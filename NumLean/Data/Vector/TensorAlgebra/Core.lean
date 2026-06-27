import NumLean.Data.Vector.Basic
import NumLean.Data.Tensor
import NumLean.Interfaces.Fold.Lemmas
import NumLean.Meta.ForAll

set_option backward.do.legacy false
set_option linter.unusedVariables false

namespace NumLean
namespace Vector

open Tensor


def tensorSum [Add K] [Zero K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n)) : K := Id.run do
  let mut acc := 0
  for_all i in 0...shape do
    acc := acc + xs[xmap i]
  return acc


def tensorAxpy [Add K] [Mul K] {m n : Nat} {r : Rank} {shape : Shape r} (a : K)
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) : Vector K m := Id.run do
  let mut ys := ys
  for_all i in 0...shape do
    ys[ymap i] := ys[ymap i] + a * xs[xmap i]
  return ys


def tensorAxpySelf [Add K] [Mul K] {n : Nat} {r : Rank} {shape : Shape r} (a : K)
    (data : Vector K n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range) : Vector K n := Id.run do
  let mut data := data
  for_all i in 0...shape do
    data[dstMap i] := data[dstMap i] + a * data[srcMap i]
  return data


def tensorScal [Mul K] {n : Nat} {r : Rank} {shape : Shape r} (a : K)
    (xs : Vector K n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) : Vector K n := Id.run do
  let mut xs := xs
  for_all i in 0...shape do
    xs[xmap i] := a * xs[xmap i]
  return xs


def tensorDot [Add K] [Mul K] [Zero K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m)) : K := Id.run do
  let mut acc := 0
  for_all i in 0...shape do
    acc := acc + xs[xmap i] * ys[ymap i]
  return acc


def tensorMul [Mul K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) : Vector K m := Id.run do
  let mut ys := ys
  for_all i in 0...shape do
    ys[ymap i] := ys[ymap i] * xs[xmap i]
  return ys


def tensorProd [Mul K] [One K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n)) : K := Id.run do
  let mut acc := 1
  for_all i in 0...shape do
    acc := acc * xs[xmap i]
  return acc


def tensorDiv [Div K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) : Vector K m := Id.run do
  let mut ys := ys
  for_all i in 0...shape do
    ys[ymap i] := ys[ymap i] / xs[xmap i]
  return ys


def tensorInv [Inv K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) : Vector K n := Id.run do
  let mut xs := xs
  for_all i in 0...shape do
    xs[xmap i] := (xs[xmap i])⁻¹
  return xs


/-- Matrix vector multiplication. -/
def tensorGemv [Add K] [Mul K] [Zero K] {an xn yn : Nat}
    {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : K)
    (A : Vector K an) (amap : Layout (.prod rows cols) h(an))
    (x : Vector K xn) (xmap : Layout cols h(xn))
    (y : Vector K yn) (ymap : Layout rows h(yn))
    (hymap : ymap.Injective) : Vector K yn := Id.run do
  let mut y := y
  for_all i in 0...rows do
    let mut acc := 0
    for_all j in 0...cols do
      acc := acc + A[amap (i.prod j)] * x[xmap j]
    y[ymap i] := alpha * acc + beta * y[ymap i]
  return y


/-- Add an outer product of two vectors to a matrix. -/
def tensorGer [Add K] [Mul K] {an xn yn : Nat}
    {rr rc : Rank} {rows : Shape rr} {cols : Shape rc}
    (alpha : K)
    (x : Vector K xn) (xmap : Layout rows h(xn))
    (y : Vector K yn) (ymap : Layout cols h(yn))
    (A : Vector K an) (amap : Layout (.prod rows cols) h(an))
    (hamap : amap.Injective) : Vector K an := Id.run do
  let mut A := A
  for_all i in 0...rows do
    for_all j in 0...cols do
      A[amap (i.prod j)] := A[amap (i.prod j)] + alpha * x[xmap i] * y[ymap j]
  return A


/-- Matrix matrix multiplication -/
def tensorGemm [Add K] [Mul K] [Zero K] {an bn cn : Nat}
    {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Vector K an) (amap : Layout (.prod is ks) h(an))
    (B : Vector K bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Vector K cn) (cmap : Layout (.prod is js) h(cn))
    (hcmap : cmap.Injective) : Vector K cn := Id.run do
  let mut C := C
  for_all i in 0...is do
    for_all j in 0...js do
      let mut acc := 0
      for_all k in 0...ks do
        acc := acc + A[amap (i.prod k)] * B[bmap (k.prod j)]
      C[cmap (i.prod j)] := alpha * acc + beta * C[cmap (i.prod j)]
  return C
