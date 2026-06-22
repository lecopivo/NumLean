import NumLean.Interfaces.Algebra.NormedRing.Lawful
import NumLean.Data.Prod.Algebra.Ring
import Mathlib.Analysis.Normed.Ring.Basic

namespace NumLean

instance {A B : Type _} [NormedRingOps ℝ A] [NormedRingOps ℝ B] :
    NormedRingOps ℝ (A × B) where
  rnorm x := max (RNorm.rnorm (R := ℝ) x.1) (RNorm.rnorm (R := ℝ) x.2)

end NumLean
