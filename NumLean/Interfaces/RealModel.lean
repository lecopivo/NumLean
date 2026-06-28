module

public import NumLean.Interfaces.Algebra.RNorm
public import NumLean.Interfaces.Algebra.RCLike.Basic
public import NumLean.Interfaces.Algebra.RCLike.Lawful
public import NumLean.Interfaces.VectorType.Basic
public import NumLean.Interfaces.TensorAlgebra
public import NumLean.Interfaces.TensorType
public import NumLean.Data.FlatVector.Ops

@[expose] public section

namespace NumLean

class RealModelOps (R : Type) (Rs : outParam (Nat → Type)) extends
  ROps R,
  -- lawful data structure operations
  VectorType Rs R,
  TensorType Rs,
  TensorRingOps Rs R .leaf


class LawfulDataRealModelOps (R : Type) {Rs : outParam (Nat → Type)} [RealModelOps R Rs] extends
    LawfulDataROps R

class LawfulRealModelOps (R : Type) {Rs : outParam (Nat → Type)}
    [RealModelOps R Rs] [LawfulDataRealModelOps R] : Prop extends
    LawfulROps R,
    LawfulTensorRingOps Rs R .leaf

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

noncomputable
example : NormedAddCommGroup (FlatVector R (Fin 10)) := by infer_instance
noncomputable
example : NormedSpace R (FlatVector R (Fin 10)) := by infer_instance

noncomputable
example {R Rs} [RealModelOps R Rs] [LawfulRealModel R] : NormedAddCommGroup R := by infer_instance
