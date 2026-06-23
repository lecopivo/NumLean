import NumLean.Data.Vector.TensorAlgebra.RingOps
import NumLean.Interfaces.TensorAlgebra.SemiringOps

namespace NumLean

open Tensor

/-- Fast ring-style operations on tensor-shaped slices of vector-like storage. -/
class TensorRingOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (r : Rank) extends TensorSemiringOps Ks K r where
  /-- Negate a tensor-shaped slice in place. -/
  tensorNeg {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) : Ks n

  /-- Subtract a source tensor slice from a destination tensor slice. -/
  tensorSub {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) : Ks m

/-- Laws for `TensorRingOps`. -/
class LawfulTensorRingOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (r : Rank) [TensorRingOps Ks K r] [Add K] [Mul K] [Zero K] [One K] [Neg K] [Sub K] : Prop
    extends LawfulTensorSemiringOps Ks K r where
  tensorNeg_spec {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) :
    VectorType.toVector (A:=K) (TensorRingOps.tensorNeg xs xmap hxmap) =
      Vector.tensorNeg (K:=K) (VectorType.toVector (A:=K) xs) xmap hxmap

  tensorSub_spec {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) :
    VectorType.toVector (A:=K) (TensorRingOps.tensorSub xs xmap ys ymap hymap) =
      Vector.tensorSub (K:=K) (VectorType.toVector (A:=K) xs) xmap
        (VectorType.toVector (A:=K) ys) ymap hymap

end NumLean
