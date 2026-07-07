module

public import NumLean.Data.Vector.LayoutMap
public import NumLean.Data.Tensor.Layout
public import NumLean.Interfaces.Fold.Lemmas
public import NumLean.Meta.ForAll

@[expose] public section

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
    (hymap : ymap.Injective) : Vector K m :=
  Layout.map ymap ys fun i yi => yi + a * xs[xmap i]


def tensorAxpySelf [Add K] [Mul K] {n : Nat} {r : Rank} {shape : Shape r} (a : K)
    (data : Vector K n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range) : Vector K n :=
  Layout.map₂ dstMap srcMap data fun _ x y => x + a * y


def tensorScal [Mul K] {n : Nat} {r : Rank} {shape : Shape r} (a : K)
    (xs : Vector K n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) : Vector K n :=
  Layout.map xmap xs fun _ xi => a * xi


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
    (hymap : ymap.Injective) : Vector K m :=
  Layout.map ymap ys fun i yi => yi * xs[xmap i]


def tensorProd [Mul K] [One K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n)) : K := Id.run do
  let mut acc := 1
  for_all i in 0...shape do
    acc := acc * xs[xmap i]
  return acc


def tensorDiv [Div K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) : Vector K m :=
  Layout.map ymap ys fun i yi => yi / xs[xmap i]


def tensorInv [Inv K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) : Vector K n :=
  Layout.map xmap xs fun _ xi => xi⁻¹


/-- Matrix vector multiplication. -/
def tensorGemv [Add K] [Mul K] [Zero K] {an xn yn : Nat}
    {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : K)
    (A : Vector K an) (amap : Layout (.prod rows cols) h(an))
    (x : Vector K xn) (xmap : Layout cols h(xn))
    (y : Vector K yn) (ymap : Layout rows h(yn))
    (hymap : ymap.Injective) : Vector K yn :=
  Layout.map ymap y fun i yi =>
    alpha * (Fold.fold (0...cols) 0 fun j _hj acc =>
      acc + A[amap (i.val.prod j)] * x[xmap j])
    + beta * yi


/-- Add an outer product of two vectors to a matrix. -/
def tensorGer [Add K] [Mul K] {an xn yn : Nat}
    {rr rc : Rank} {rows : Shape rr} {cols : Shape rc}
    (alpha : K)
    (x : Vector K xn) (xmap : Layout rows h(xn))
    (y : Vector K yn) (ymap : Layout cols h(yn))
    (A : Vector K an) (amap : Layout (.prod rows cols) h(an))
    (hamap : amap.Injective) : Vector K an :=
  Layout.map amap A fun ij Aij =>
    match ij with
    | ⟨.prod i j, _hij⟩ => Aij + alpha * x[xmap i] * y[ymap j]


/-- Matrix matrix multiplication -/
def tensorGemm [Add K] [Mul K] [Zero K] {an bn cn : Nat}
    {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Vector K an) (amap : Layout (.prod is ks) h(an))
    (B : Vector K bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Vector K cn) (cmap : Layout (.prod is js) h(cn))
    (hcmap : cmap.Injective) : Vector K cn :=
  Layout.map cmap C fun ij Cij =>
    match ij with
    | ⟨.prod i j, _hij⟩ =>
        alpha * (Fold.fold (0...ks) 0 fun k _hk acc =>
          acc + A[amap (i.prod k)] * B[bmap (k.prod j)])
        + beta * Cij
