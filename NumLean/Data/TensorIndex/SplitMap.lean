import NumLean.Data.TensorIndex.Layout

namespace NumLean

namespace TensorIndex

/-- A split of `shape` into a selected/tile shape and a complementary/grid shape.

The split is represented by two coordinate-valued layouts into `shape`. Their concatenation maps
`shape₁ × shape₂` coordinates back into `shape`, and the fields require that map to be bounded and
bijective on bounded coordinates. -/
structure SplitMap {p p₁ p₂ : HRank}
    (shape : Shape p) (shape₁ : Shape p₁) (shape₂ : Shape p₂) where
  left : Layout shape₁ (TIndex Int p)
  right : Layout shape₂ (TIndex Int p)
  inBounds : ∀ idx : FinTIndex (HTuple.prod shape₁ shape₂),
    TIndex.InBounds shape ((left.concat right).eval idx.val)
  bijective : Function.Bijective ((left.concat right).evalToFinTIndex inBounds)

namespace SplitMap

variable {p p₁ p₂ : HRank} {shape : Shape p} {shape₁ : Shape p₁} {shape₂ : Shape p₂}

/-- The coordinate-valued layout induced by a split. -/
def toLayout (s : SplitMap shape shape₁ shape₂) :
    Layout (HTuple.prod shape₁ shape₂) (TIndex Int p) :=
  s.left.concat s.right

@[simp]
theorem toLayout_eval (s : SplitMap shape shape₁ shape₂)
    (idx₁ : TIndex Int p₁) (idx₂ : TIndex Int p₂) :
    s.toLayout.eval (idx₁.prod idx₂) = s.left.eval idx₁ + s.right.eval idx₂ := by
  simp [toLayout]

/-- Compose an ordinary layout with the coordinate layout induced by a split. -/
def composeLayout {D : Type u} [Zero D] [Add D] [SMul Int D]
    (layout : Layout shape D) (s : SplitMap shape shape₁ shape₂) :
    Layout (HTuple.prod shape₁ shape₂) D :=
  layout.compose s.toLayout

@[simp]
theorem composeLayout_eval {D : Type u} [AddCommMonoid D] [Module Int D]
    (layout : Layout shape D) (s : SplitMap shape shape₁ shape₂)
    (idx₁ : TIndex Int p₁) (idx₂ : TIndex Int p₂) :
    (s.composeLayout layout).eval (idx₁.prod idx₂) =
      layout.eval (s.left.eval idx₁ + s.right.eval idx₂) := by
  simp [composeLayout, toLayout]

end SplitMap

end TensorIndex

end NumLean
