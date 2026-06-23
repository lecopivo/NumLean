import NumLean.Data.Vector.TensorAlgebra.AddOps
import NumLean.Interfaces.VectorType.Basic

namespace NumLean

open Tensor

/-- Fast additive operations on tensor-shaped slices of vector-like storage. -/
class TensorAddOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (r : Rank) where
  /-- Sum a tensor-shaped slice. -/
  tensorSum {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n)) : K

/-- Laws for `TensorAddOps`. -/
class LawfulTensorAddOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (r : Rank) [TensorAddOps Ks K r] [Add K] [Zero K] : Prop where
  tensorSum_spec {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n)) :
    TensorAddOps.tensorSum xs xmap =
      Vector.tensorSum (K:=K) (VectorType.toVector (A:=K) xs) xmap

end NumLean
