import NumLean.Data.Vector.TensorAlgebra.MulOps
import NumLean.Interfaces.VectorType.Basic

namespace NumLean

open Tensor

/-- Fast multiplicative operations on tensor-shaped slices of vector-like storage. -/
class TensorMulOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (r : Rank) where
  /-- Scale a tensor-shaped slice in place: `xs[xmap i] := a * xs[xmap i]`. -/
  tensorScal {n : Nat} {shape : Shape r}
    (a : K) (xs : Ks n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) : Ks n

  /-- Multiply a destination tensor slice by a source tensor slice. -/
  tensorMul {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) : Ks m

  /-- Product of a tensor-shaped slice. -/
  tensorProd {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n)) : K

/-- Laws for `TensorMulOps`. -/
class LawfulTensorMulOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (r : Rank) [TensorMulOps Ks K r] [Mul K] [One K] : Prop where
  tensorScal_spec {n : Nat} {shape : Shape r}
    (a : K) (xs : Ks n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) :
    VectorType.toVector (A:=K) (TensorMulOps.tensorScal a xs xmap hxmap) =
      Vector.tensorScal (K:=K) a (VectorType.toVector (A:=K) xs) xmap hxmap

  tensorMul_spec {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) :
    VectorType.toVector (A:=K) (TensorMulOps.tensorMul xs xmap ys ymap hymap) =
      Vector.tensorMul (K:=K) (VectorType.toVector (A:=K) xs) xmap
        (VectorType.toVector (A:=K) ys) ymap hymap

  tensorProd_spec {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n)) :
    TensorMulOps.tensorProd xs xmap =
      Vector.tensorProd (K:=K) (VectorType.toVector (A:=K) xs) xmap

end NumLean
