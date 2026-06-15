import NumLean.Data.TensorIndex.Basic

namespace NumLean

namespace TensorIndex

namespace FinIndex

/-- Bounded indices of a leaf shape are ordinary finite indices. -/
def leafEquiv (dim : Nat) : FinIndex (.leaf dim) ≃ Fin dim where
  toFun idx := match idx with | ⟨HTuple.leaf i, h⟩ => ⟨i, h⟩
  invFun i := ⟨HTuple.leaf i.1, i.2⟩
  left_inv := by
    intro idx
    cases idx with
    | mk val h =>
    cases val with
    | leaf i => rfl
  right_inv := by intro i; rfl

/-- Bounded indices of a product shape are pairs of bounded indices. -/
def prodEquiv {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q} :
    FinIndex (HTuple.prod shape₀ shape₁) ≃ FinIndex shape₀ × FinIndex shape₁ where
  toFun idx :=
    match idx with
    | ⟨HTuple.prod idx₀ idx₁, h⟩ => (⟨idx₀, h.1⟩, ⟨idx₁, h.2⟩)
  invFun idx := ⟨HTuple.prod idx.1.val idx.2.val, ⟨idx.1.isLt, idx.2.isLt⟩⟩
  left_inv := by
    intro idx
    cases idx with
    | mk val h =>
    cases val with
    | prod idx₀ idx₁ => rfl
  right_inv := by
    intro idx
    cases idx with
    | mk left right => rfl

@[implicit_reducible]
def fintype : {p : HRank} → (shape : Shape p) → Fintype (FinIndex shape)
  | .leaf, .leaf dim => Fintype.ofEquiv (Fin dim) (leafEquiv dim).symm
  | .prod _ _, .prod shape₀ shape₁ =>
      letI := fintype shape₀
      letI := fintype shape₁
      Fintype.ofEquiv (FinIndex shape₀ × FinIndex shape₁) FinIndex.prodEquiv.symm

instance {p : HRank} {shape : Shape p} : Fintype (FinIndex shape) :=
  fintype shape

theorem card_eq_shape_size {p : HRank} (shape : Shape p) :
    Fintype.card (FinIndex shape) = shape.size := by
  induction shape with
  | leaf dim =>
      simpa [Shape.size] using Fintype.card_congr (leafEquiv dim)
  | prod shape₀ shape₁ h₀ h₁ =>
      rw [Shape.size_prod]
      have hcard := Fintype.card_congr (FinIndex.prodEquiv (shape₀ := shape₀) (shape₁ := shape₁))
      simpa [Fintype.card_prod, h₀, h₁] using hcard

end FinIndex

end TensorIndex

end NumLean
