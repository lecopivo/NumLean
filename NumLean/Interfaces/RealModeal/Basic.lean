import NumLean.Algebra.Ops
import NumLean.Interfaces.Algebra.RCLike.Basic
import NumLean.Interfaces.Algebra.RCLike.Lawful
import NumLean.Interfaces.RingArrayOps
import NumLean.Interfaces.VectorType.Basic
import NumLean.Interfaces.TensorAlgebra
import NumLean.Data.FlatVector.Ops

namespace NumLean

class RealModelOps (R : Type) (Rs : outParam (Nat → Type)) extends
  ROps R,
  -- lawful data structure operations
  VectorType Rs R,
  TensorArrayOps Rs R,
  TensorRingOps Rs R .leaf


class LawfulDataRealModelOps (R : Type) {Rs : outParam (Nat → Type)} [RealModelOps R Rs] extends
    LawfulDataROps R,
    LawfulTensorRingOps Rs R .leaf

class LawfulRealModelOps (R : Type) {Rs : outParam (Nat → Type)}
    [RealModelOps R Rs] [LawfulDataRealModelOps R] : Prop extends
    LawfulROps R

class LawfulRealModel (R : semiOutParam Type) {Rs : outParam (Nat → Type)} [RealModelOps R Rs] extends
    LawfulDataRealModelOps R, LawfulRealModelOps R

-- if you introduce RealModelOps, we attach Rs to R as the default vector type!
instance [RealModelOps R Rs] : HasDefaultFlatRepr R Rs 1 where

variable {R Rs} [RealModelOps R Rs] [LawfulRealModel R]

-- todo: move NatCast and IntCast to some *Ops
example : AddGroupOps (FlatVector R (Fin 10)) := by infer_instance

@[reducible]
def hhihi : AddGroup (FlatVector R (Fin 10 × Fin 10)) := by infer_instance


example : SMul R (FlatVector R (Fin 10)) := by infer_instance

-- example : AddMonoid (FlatVector R (Fin 10)) :=

noncomputable
example {R Rs} [RealModelOps R Rs] [LawfulRealModel R] : NormedAddCommGroup R := by infer_instance


-- instance [NatCast R] [IntCast R] : RNorm R (FlatVector R (Fin 10)) := by infer_instance
