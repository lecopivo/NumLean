import NumLean.Data.TensorIndex.Basic

namespace NumLean

namespace TensorIndex

/-- A bounded integer hierarchical tensor index, kept as the old `FinTIndex` representation. -/
structure IntFinTIndex {p : HRank} (shape : Shape p) where
  val : TIndex Int p
  isLt : TIndex.InBoundsInt shape val

attribute [inline] IntFinTIndex.val

namespace IntFinTIndex

/-- Bounded integer indices are equal when their underlying coordinates are equal. -/
theorem ext {p : HRank} {shape : Shape p} {idx idx' : IntFinTIndex shape}
    (h : idx.val = idx'.val) : idx = idx' := by
  cases idx
  cases idx'
  simp at h
  subst h
  rfl

instance {p : HRank} {shape : Shape p} : CoeOut (IntFinTIndex shape) (TIndex Int p) where
  coe idx := idx.val

/-- Bounded indices of a leaf shape are ordinary finite indices. -/
@[inline, simps]
def leafEquiv (dim : Nat) : IntFinTIndex (.leaf dim) ≃ Fin dim where
  toFun idx := match idx with
    | ⟨HTuple.leaf i, h⟩ =>
        ⟨i.toNat, by
          simp [TIndex.InBoundsInt] at h
          omega⟩
  invFun i := ⟨HTuple.leaf i.1, ⟨Int.natCast_nonneg _, by exact_mod_cast i.2⟩⟩
  left_inv := by
    intro idx
    cases idx with
    | mk val h =>
      cases val with
      | leaf i =>
          apply IntFinTIndex.ext
          simp [TIndex.InBoundsInt] at h
          exact congrArg HTuple.leaf (Int.toNat_of_nonneg h.1)
  right_inv := by intro i; rfl

/-- Bounded indices of a product shape are pairs of bounded indices. -/
@[inline, simps]
def prodEquiv {p q : HRank} (shape₀ : Shape p) (shape₁ : Shape q) :
    IntFinTIndex (HTuple.prod shape₀ shape₁) ≃ IntFinTIndex shape₀ × IntFinTIndex shape₁ where
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

/-- Canonical dense row-major equivalence for the old integer-backed index. -/
@[inline] def equivFin : {p : HRank} → (shape : Shape p) → IntFinTIndex shape ≃ Fin shape.size
  | .leaf, .leaf dim => leafEquiv dim
  | .prod _ _, .prod shape₀ shape₁ =>
      let f := prodEquiv shape₀ shape₁
      let g := Equiv.prodCongr (equivFin shape₀) (equivFin shape₁)
      let h := finProdFinEquiv
      f.trans (g.trans h)

theorem offset_rowMajorEquiv_eq_equivFin {r} {shape : Shape r} (idx : IntFinTIndex shape) :
    idx.val.offset (TIndex.rowMajorStride shape) = (equivFin shape idx) := by
  induction shape
  case leaf =>
    have ⟨.leaf idx, hidx⟩ := idx
    set_option backward.isDefEq.respectTransparency false in
    simp [TIndex.rowMajorStride, equivFin, leafEquiv, hidx.1]
  case prod shape₁ shape₂ h₁ h₂ =>
    have ⟨.prod idx₁ idx₂, hidx⟩ := idx
    set_option backward.isDefEq.respectTransparency false in
    simp [TIndex.rowMajorStride, equivFin, ← h₁, ← h₂, - nsmul_eq_mul, TIndex.offset_smul]
    rw [add_comm]

end IntFinTIndex

end TensorIndex
end NumLean
