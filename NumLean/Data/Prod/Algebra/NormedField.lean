import NumLean.Interfaces.Algebra.NormedField.Lawful
import NumLean.Data.Prod.Algebra.Field

namespace NumLean

instance {A B : Type _} [NormedFieldOps ℝ A] [NormedFieldOps ℝ B] :
    NormedFieldOps ℝ (A × B) where
  rnorm x := max (RNorm.rnorm (R := ℝ) x.1) (RNorm.rnorm (R := ℝ) x.2)

end NumLean
