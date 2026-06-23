import NumLean.Interfaces.TensorAlgebra.AddOps
import NumLean.Interfaces.TensorAlgebra.MulOps
import NumLean.Data.Vector.TensorAlgebra.SemiringOps

namespace NumLean

open Tensor

/-- Fast semiring-style operations on tensor-shaped slices of vector-like storage. -/
class TensorSemiringOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (r : Rank) extends TensorAddOps Ks K r, TensorMulOps Ks K r where
  /-- Tensor `axpy`: `ys[ymap i] := ys[ymap i] + a * xs[xmap i]`. -/
  tensorAxpy {m n : Nat} {shape : Shape r}
    (a : K)
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) : Ks m

  /-- Dot product of two tensor-shaped slices. -/
  tensorDot {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m)) : K

/-- Matrix-like semiring operations over selected row/column profiles. -/
class TensorMatrixSemiringOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (ri rj rk : Rank) where

  /-- Matrix-vector product over tensor layouts: `y := alpha * A * x + beta * y`. -/
  tensorGemv {an xn yn : Nat}
    {rows : Shape ri} {cols : Shape rk}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod rows cols) h(an))
    (x : Ks xn) (xmap : Layout cols h(xn))
    (y : Ks yn) (ymap : Layout rows h(yn))
    (hymap : ymap.Injective) : Ks yn

  /-- Rank-one update over tensor layouts: `A := alpha * x * yᵀ + A`. -/
  tensorGer {an xn yn : Nat}
    {rows : Shape ri} {cols : Shape rj}
    (alpha : K)
    (x : Ks xn) (xmap : Layout rows h(xn))
    (y : Ks yn) (ymap : Layout cols h(yn))
    (A : Ks an) (amap : Layout (.prod rows cols) h(an))
    (hamap : amap.Injective) : Ks an

  /-- Matrix-matrix product over tensor layouts: `C := alpha * A * B + beta * C`. -/
  tensorGemm {an bn cn : Nat}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod is ks) h(an))
    (B : Ks bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Ks cn) (cmap : Layout (.prod is js) h(cn))
    (hcmap : cmap.Injective) : Ks cn

/-- Laws for `TensorSemiringOps`. -/
class LawfulTensorSemiringOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (r : Rank) [TensorSemiringOps Ks K r] [Add K] [Mul K] [Zero K] [One K] : Prop
    extends LawfulTensorAddOps Ks K r, LawfulTensorMulOps Ks K r where
  tensorAxpy_spec {m n : Nat} {shape : Shape r}
    (a : K)
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) :
    VectorType.toVector (A:=K) (TensorSemiringOps.tensorAxpy a xs xmap ys ymap hymap) =
      Vector.tensorAxpy (K:=K) a (VectorType.toVector (A:=K) xs) xmap
        (VectorType.toVector (A:=K) ys) ymap hymap

  tensorDot_spec {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m)) :
    TensorSemiringOps.tensorDot xs xmap ys ymap =
      Vector.tensorDot (K:=K) (VectorType.toVector (A:=K) xs) xmap
        (VectorType.toVector (A:=K) ys) ymap

/-- Laws for matrix-like semiring operations. -/
class LawfulTensorMatrixSemiringOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (ri rj rk : Rank) [TensorMatrixSemiringOps Ks K ri rj rk]
    [Add K] [Mul K] [Zero K] : Prop where

  tensorGemv_spec {an xn yn : Nat}
    {rows : Shape ri} {cols : Shape rk}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod rows cols) h(an))
    (x : Ks xn) (xmap : Layout cols h(xn))
    (y : Ks yn) (ymap : Layout rows h(yn))
    (hymap : ymap.Injective) :
    VectorType.toVector (A:=K)
        (TensorMatrixSemiringOps.tensorGemv (ri := ri) (rj := rj) (rk := rk)
          alpha beta A amap x xmap y ymap hymap) =
      Vector.tensorGemv (K:=K) alpha beta (VectorType.toVector (A:=K) A) amap
        (VectorType.toVector (A:=K) x) xmap (VectorType.toVector (A:=K) y) ymap hymap

  tensorGer_spec {an xn yn : Nat}
    {rows : Shape ri} {cols : Shape rj}
    (alpha : K)
    (x : Ks xn) (xmap : Layout rows h(xn))
    (y : Ks yn) (ymap : Layout cols h(yn))
    (A : Ks an) (amap : Layout (.prod rows cols) h(an))
    (hamap : amap.Injective) :
    VectorType.toVector (A:=K)
        (TensorMatrixSemiringOps.tensorGer (ri := ri) (rj := rj) (rk := rk)
          alpha x xmap y ymap A amap hamap) =
      Vector.tensorGer (K:=K) alpha (VectorType.toVector (A:=K) x) xmap
        (VectorType.toVector (A:=K) y) ymap (VectorType.toVector (A:=K) A) amap hamap

  tensorGemm_spec {an bn cn : Nat}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod is ks) h(an))
    (B : Ks bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Ks cn) (cmap : Layout (.prod is js) h(cn))
    (hcmap : cmap.Injective) :
    VectorType.toVector (A:=K)
        (TensorMatrixSemiringOps.tensorGemm (ri := ri) (rj := rj) (rk := rk)
          alpha beta A amap B bmap C cmap hcmap) =
      Vector.tensorGemm (K:=K) alpha beta (VectorType.toVector (A:=K) A) amap
        (VectorType.toVector (A:=K) B) bmap (VectorType.toVector (A:=K) C) cmap hcmap

end NumLean
