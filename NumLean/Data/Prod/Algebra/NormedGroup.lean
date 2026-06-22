import NumLean.Interfaces.Algebra.NormedGroup.Lawful
import NumLean.Data.Prod.Algebra.Group
import Mathlib.Analysis.Normed.Group.Constructions

namespace NumLean

instance {A B : Type _} [NormedAddMonoidOps ℝ A] [NormedAddMonoidOps ℝ B] :
    NormedAddMonoidOps ℝ (A × B) where
  rnorm x := max (RNorm.rnorm (R := ℝ) x.1) (RNorm.rnorm (R := ℝ) x.2)

instance {A B : Type _} [NormedAddGroupOps ℝ A] [NormedAddGroupOps ℝ B] :
    NormedAddGroupOps ℝ (A × B) where
  rnorm x := max (RNorm.rnorm (R := ℝ) x.1) (RNorm.rnorm (R := ℝ) x.2)

instance {A B : Type _} [NormedMonoidOps ℝ A] [NormedMonoidOps ℝ B] :
    NormedMonoidOps ℝ (A × B) where
  rnorm x := max (RNorm.rnorm (R := ℝ) x.1) (RNorm.rnorm (R := ℝ) x.2)

instance {A B : Type _} [NormedGroupOps ℝ A] [NormedGroupOps ℝ B] :
    NormedGroupOps ℝ (A × B) where
  rnorm x := max (RNorm.rnorm (R := ℝ) x.1) (RNorm.rnorm (R := ℝ) x.2)

example {A B : Type _} [NormedAddCommGroup A] [NormedAddCommGroup B] :
    (instNormedAddCommGroupOfOps (R := ℝ) : NormedAddCommGroup (A × B)) =
      Prod.normedAddCommGroup :=
  rfl

example {A B : Type _} [NormedCommGroup A] [NormedCommGroup B] :
    (instNormedCommGroupOfOps (R := ℝ) : NormedCommGroup (A × B)) =
      Prod.normedCommGroup :=
  rfl

end NumLean
