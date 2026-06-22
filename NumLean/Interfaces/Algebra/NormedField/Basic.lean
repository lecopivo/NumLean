import Mathlib.Analysis.Normed.Field.Basic
import NumLean.Interfaces.Algebra.NormedRing
import NumLean.Interfaces.Algebra.Field

namespace NumLean

class NormedFieldOps (R : outParam (Type u)) (K : Type v) extends
    NormedRingOps R K, FieldOps K

class LawfulDataNormedFieldOps {R : outParam (Type u)} (K : Type v)
    [NormedFieldOps R K] extends LawfulDataNormedRingOps K

class LawfulNormedFieldOps {R : outParam (Type u)} (K : Type v) [NormedFieldOps R K]
    [LawfulDataNormedFieldOps K] : Prop extends LawfulFieldOps K where
  dist_eq : ∀ x y : K, dist x y = ‖-x + y‖
  norm_mul : ∀ a b : K, ‖a * b‖ = ‖a‖ * ‖b‖

instance [RNorm K R] [FieldOps K] : NormedFieldOps R K where

end NumLean
