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

/-- Canonical dense row-major equivalence between bounded hierarchical indices and flat offsets. -/
def equivFin : {p : HRank} → (shape : Shape p) → FinIndex shape ≃ Fin shape.size
  | .leaf, .leaf dim => leafEquiv dim
  | .prod _ _, .prod shape₀ shape₁ =>
      prodEquiv.trans ((Equiv.prodCongr (equivFin shape₀) (equivFin shape₁)).trans finProdFinEquiv)

@[implicit_reducible]
def fintype {p : HRank} (shape : Shape p) : Fintype (FinIndex shape) :=
  Fintype.ofEquiv (Fin shape.size) (equivFin shape).symm

instance {p : HRank} {shape : Shape p} : Fintype (FinIndex shape) :=
  fintype shape

theorem card_eq_shape_size {p : HRank} (shape : Shape p) :
    Fintype.card (FinIndex shape) = shape.size := by
  simpa using Fintype.card_congr (equivFin shape)

end FinIndex

end TensorIndex

end NumLean
