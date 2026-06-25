import Mathlib.Analysis.Normed.Ring.Basic
import NumLean.Interfaces.Algebra.NormedGroup
import NumLean.Interfaces.Algebra.Ring

namespace NumLean

@[hierarchy_graph algebra_ops]
class NormedRingOps (R : outParam (Type u)) (K : Type v) extends
    NormedAddGroupOps R K, RingOps K

@[hierarchy_graph algebra_lawful]
class LawfulDataNormedRingOps {R : outParam (Type u)} (K : Type v)
    [NormedRingOps R K] extends LawfulDataNormedAddGroupOps K

@[hierarchy_graph algebra_lawful]
class LawfulNormedRingOps {R : outParam (Type u)} (K : Type v) [NormedRingOps R K]
    [LawfulDataNormedRingOps K] : Prop extends LawfulRingOps K where
  dist_eq : ∀ x y : K, dist x y = ‖-x + y‖
  norm_mul_le : ∀ a b : K, ‖a * b‖ ≤ ‖a‖ * ‖b‖

instance [RNorm K R] [RingOps K] : NormedRingOps R K where

end NumLean
