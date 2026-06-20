import NumLean.Interfaces.Fold
import NumLean.Data.FinHTuple.Fold

namespace NumLean

namespace Tests

namespace FoldEmbedding

noncomputable example (n : Nat) :
    Fold.RangeMonoEmbedding (0...n : Std.Rco Nat) (0...n : Std.Rco Nat) :=
  Fold.RangeMonoEmbedding.refl _

example (n : Nat) :
    Fold.RangeMonoEmbedding (0...n : Std.Rco Nat) (0...n : Std.Rco Nat) :=
  Fold.RangeMonoEmbedding.ofRangeIso (Fold.RangeIso.refl (0...n : Std.Rco Nat))

example (n init : Nat) (f : (i : Nat) → i ∈ (0...n : Std.Rco Nat) → Nat → Nat) :
    Fold.fold (0...n : Std.Rco Nat) init f =
      Fold.fold (0...n : Std.Rco Nat) init fun i hi acc =>
        if h : (Fold.RangeMonoEmbedding.refl (0...n : Std.Rco Nat)).guard i hi then
          f ((Fold.RangeMonoEmbedding.refl (0...n : Std.Rco Nat)).invFun i hi h).1
            ((Fold.RangeMonoEmbedding.refl (0...n : Std.Rco Nat)).invFun i hi h).2 acc
        else
          acc := by
  exact Fold.RangeMonoEmbedding.fold_eq_guarded
    (Fold.RangeMonoEmbedding.refl (0...n : Std.Rco Nat)) init f

end FoldEmbedding

end Tests

end NumLean
