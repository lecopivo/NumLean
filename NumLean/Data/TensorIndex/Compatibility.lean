import NumLean.Data.TensorIndex.FinTIndex

namespace NumLean

namespace TensorIndex

namespace Profile

/-- Paper-style weak congruence of HTuple profiles.

`WeakCongruent p q` means `p` coarsens `q`: a leaf profile may stand for any refined
subprofile, while product profiles must refine componentwise. -/
def WeakCongruent : HRank → HRank → Prop
  | .leaf, _ => True
  | .prod _ _, .leaf => False
  | .prod p₀ p₁, .prod q₀ q₁ => WeakCongruent p₀ q₀ ∧ WeakCongruent p₁ q₁

@[simp]
theorem weakCongruent_leaf_left (p : HRank) : WeakCongruent .leaf p := by
  cases p <;> trivial

@[simp]
theorem weakCongruent_leaf_right {p q : HRank} :
    WeakCongruent (.prod p q) .leaf = False := rfl

@[simp]
theorem weakCongruent_prod_prod {p₀ p₁ q₀ q₁ : HRank} :
    WeakCongruent (.prod p₀ p₁) (.prod q₀ q₁) =
      (WeakCongruent p₀ q₀ ∧ WeakCongruent p₁ q₁) := rfl

theorem weakCongruent_refl (p : HRank) : WeakCongruent p p := by
  induction p with
  | leaf => simp [WeakCongruent]
  | prod p q hp hq => simp [WeakCongruent, hp, hq]

theorem weakCongruent_trans {p q r : HRank}
    (hpq : WeakCongruent p q) (hqr : WeakCongruent q r) : WeakCongruent p r := by
  induction p generalizing q r with
  | leaf => simp [WeakCongruent]
  | prod p₀ p₁ hp₀ hp₁ =>
      cases q with
      | leaf => simp [WeakCongruent] at hpq
      | prod q₀ q₁ =>
          cases r with
          | leaf => simp [WeakCongruent] at hqr
          | prod r₀ r₁ =>
              exact ⟨hp₀ hpq.1 hqr.1, hp₁ hpq.2 hqr.2⟩

end Profile

namespace Shape

/-- Paper-style compatibility/coarsening of shapes.

`Coarsens coarse refined` corresponds to `coarse ⪯ refined` in the CUTE paper: a leaf shape
coarsens any refined shape with the same total size, and product shapes coarsen componentwise. -/
def Coarsens : {p q : HRank} → Shape p → Shape q → Prop
  | .leaf, _, .leaf n, refined => n = refined.size
  | .prod _ _, .leaf, .prod _ _, .leaf _ => False
  | .prod _ _, .prod _ _, .prod coarse₀ coarse₁, .prod refined₀ refined₁ =>
      Coarsens coarse₀ refined₀ ∧ Coarsens coarse₁ refined₁

@[simp]
theorem coarsens_leaf {q : HRank} (n : Nat) (refined : Shape q) :
    Coarsens (.leaf n) refined = (n = refined.size) := by
  cases refined <;> rfl

@[simp]
theorem coarsens_prod_leaf {p q : HRank} (coarse₀ : Shape p) (coarse₁ : Shape q)
    (n : Nat) :
    Coarsens (.prod coarse₀ coarse₁) (.leaf n) = False := rfl

@[simp]
theorem coarsens_prod_prod {p₀ p₁ q₀ q₁ : HRank}
    (coarse₀ : Shape p₀) (coarse₁ : Shape p₁)
    (refined₀ : Shape q₀) (refined₁ : Shape q₁) :
    Coarsens (.prod coarse₀ coarse₁) (.prod refined₀ refined₁) =
      (Coarsens coarse₀ refined₀ ∧ Coarsens coarse₁ refined₁) := rfl

theorem coarsens_refl {p : HRank} (shape : Shape p) : Coarsens shape shape := by
  induction shape with
  | leaf n => simp [Coarsens]
  | prod shape₀ shape₁ h₀ h₁ => simp [h₀, h₁]

theorem size_eq_of_coarsens {p q : HRank} {coarse : Shape p} {refined : Shape q}
    (h : Coarsens coarse refined) : coarse.size = refined.size := by
  induction coarse generalizing q with
  | leaf n =>
      cases refined <;> simpa [Coarsens]
  | prod coarse₀ coarse₁ h₀ h₁ =>
      cases refined with
      | leaf n => simp at h
      | prod refined₀ refined₁ =>
          rw [Shape.size_prod, Shape.size_prod, h₀ h.1, h₁ h.2]

theorem coarsens_trans {p q r : HRank} {a : Shape p} {b : Shape q} {c : Shape r}
    (hab : Coarsens a b) (hbc : Coarsens b c) : Coarsens a c := by
  induction a generalizing q r with
  | leaf n =>
      cases c <;>
        simpa [Coarsens] using ((size_eq_of_coarsens hab).trans (size_eq_of_coarsens hbc))
  | prod a₀ a₁ ha₀ ha₁ =>
      cases b with
      | leaf n => simp at hab
      | prod b₀ b₁ =>
          cases c with
          | leaf n => simp at hbc
          | prod c₀ c₁ =>
              exact ⟨ha₀ hab.1 hbc.1, ha₁ hab.2 hbc.2⟩

end Shape

end TensorIndex

end NumLean
