module

public import NumLean.Interfaces.Algebra.NormedRing.Lawful
public import NumLean.Data.Prod.Algebra.Ring
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

namespace NumLean

instance {A B : Type _} [NormedRingOps ℝ A] [NormedRingOps ℝ B] :
    NormedRingOps ℝ (A × B) where
  rnorm x := max (RNorm.rnorm (R := ℝ) x.1) (RNorm.rnorm (R := ℝ) x.2)

end NumLean
