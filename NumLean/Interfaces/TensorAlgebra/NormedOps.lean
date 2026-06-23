import NumLean.Data.Tensor.Layout
import NumLean.Interfaces.VectorType.Basic

namespace NumLean

open Tensor

/-- Fast norm/absolute-value reductions on tensor-shaped slices of vector-like storage. -/
class TensorNormedOps (Ks : Nat → Type u) (K : outParam Type) (R : outParam Type)
    [VectorType Ks K] (r : Rank) where
  /-- Sum of element norms or absolute values. -/
  tensorAsum {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n)) : R

  /-- Euclidean norm of a tensor-shaped slice. -/
  tensorNorm2 {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n)) : R

  /-- Index of an element with maximal norm or absolute value, in row-major tensor-domain order. -/
  tensorIamax {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n)) : Index r

/-- Laws for `TensorNormedOps`. -/
class LawfulTensorNormedOps (Ks : Nat → Type u) (K : outParam Type) (R : outParam Type)
    [VectorType Ks K] (r : Rank) [TensorNormedOps Ks K R r] : Prop where

end NumLean
