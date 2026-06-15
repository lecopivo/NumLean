import NumLean.Data.TensorIndex.Basic

namespace NumLean

namespace TensorIndex

namespace TIndex

/-- Bounds predicate for natural hierarchical coordinates. -/
@[inline] def NatInBounds {p : HRank} (shape : Shape p) (idx : TIndex Nat p) : Prop :=
  match shape, idx with
  | .leaf dim, .leaf i => i < dim
  | .prod shape₁ shape₂, .prod idx₁ idx₂ => NatInBounds shape₁ idx₁ ∧ NatInBounds shape₂ idx₂

end TIndex

/-- A bounded natural-coordinate tensor index.

This mirrors `FinTIndex`, but stores `TIndex Nat p` instead of `TIndex Int p`. The proof field is
propositional and should erase at runtime. -/
structure NatFinTIndex {p : HRank} (shape : Shape p) where
  val : TIndex Nat p
  isLt : TIndex.NatInBounds shape val

end TensorIndex
end NumLean
