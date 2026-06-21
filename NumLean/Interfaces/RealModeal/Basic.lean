import NumLean.Algebra.Ops
import NumLean.Interfaces.VectorType.Basic

import NumLean.Data.FlatVector.Ops

namespace NumLean

open FlatVector

-- todo: move this!

class RealModelOps (R : Type) (Rs : outParam (Nat → Type)) extends
  ROps R, VectorType Rs R, TensorArrayOps Rs R, BLASOps Rs R where

-- if you introduce RealModelOps, we attach Rs to R as the default vector type!
instance [RealModelOps R Rs] : HasDefaultFlatVector R Rs 1 where

variable {R RS} [RealModelOps R Rs]

-- todo: move NatCast and IntCast to some *Ops
instance [NatCast R] [IntCast R] : AddGroupOps (FlatVector R (Fin 10)) := by infer_instance

instance [NatCast R] [IntCast R] : SMul R (FlatVector R (Fin 10)) := by infer_instance

-- instance [NatCast R] [IntCast R] : RNorm R (FlatVector R (Fin 10)) := by infer_instance
