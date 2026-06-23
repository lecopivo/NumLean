import NumLean.Data.Vector.TensorAlgebra.FieldOps
import NumLean.Interfaces.TensorAlgebra.RingOps

namespace NumLean

open Tensor

/-- Fast field-style operations on tensor-shaped slices of vector-like storage. -/
class TensorFieldOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (r : Rank) extends TensorRingOps Ks K r where
  /-- Divide a destination tensor slice by a source tensor slice. -/
  tensorDiv {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) : Ks m

  /-- Invert a tensor-shaped slice in place. -/
  tensorInv {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) : Ks n

/-- Laws for `TensorFieldOps`. -/
class LawfulTensorFieldOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K]
    (r : Rank) [TensorFieldOps Ks K r] [Add K] [Mul K] [Zero K] [One K] [Neg K] [Sub K] [Div K] [Inv K] : Prop
    extends LawfulTensorRingOps Ks K r where
  tensorDiv_spec {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) :
    VectorType.toVector (A:=K) (TensorFieldOps.tensorDiv xs xmap ys ymap hymap) =
      Vector.tensorDiv (K:=K) (VectorType.toVector (A:=K) xs) xmap
        (VectorType.toVector (A:=K) ys) ymap hymap

  tensorInv_spec {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) :
    VectorType.toVector (A:=K) (TensorFieldOps.tensorInv xs xmap hxmap) =
      Vector.tensorInv (K:=K) (VectorType.toVector (A:=K) xs) xmap hxmap

end NumLean
