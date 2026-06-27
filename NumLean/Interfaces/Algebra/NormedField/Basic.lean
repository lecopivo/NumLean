import Mathlib.Analysis.Normed.Field.Basic
import NumLean.Interfaces.Algebra.NormedRing
import NumLean.Interfaces.Algebra.Field

namespace NumLean

@[hierarchy_graph algebra_ops]
class NormedFieldOps (R : outParam (Type u)) (K : Type v) extends
    NormedRingOps R K, FieldOps K

attribute [instance 200] NormedFieldOps.toNormedRingOps NormedFieldOps.toFieldOps

@[hierarchy_graph algebra_lawful]
class LawfulDataNormedFieldOps {R : outParam (Type u)} (K : Type v)
    [NormedFieldOps R K] extends LawfulDataNormedRingOps K

@[hierarchy_graph algebra_lawful]
class LawfulNormedFieldOps {R : outParam (Type u)} (K : Type v) [NormedFieldOps R K]
    [LawfulDataNormedFieldOps K] : Prop extends LawfulFieldOps K where
  dist_eq : ∀ x y : K, dist x y = ‖-x + y‖
  norm_mul : ∀ a b : K, ‖a * b‖ = ‖a‖ * ‖b‖

instance (priority := 50) [RNorm K R] [FieldOps K] : NormedFieldOps R K where

end NumLean
