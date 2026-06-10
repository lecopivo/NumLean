import NumLean.Mathlib.FiberedAddTorsor.Basic

namespace NumLean

namespace FiberedAddTorsor

open FiberedAddTorsor

instance {G H} [AddGroup G] [AddGroup H]
    {P Q} [FiberedAddTorsor G P] [FiberedAddTorsor H Q] :
    FiberedAddTorsor (G × H) (MProd P Q) where
  vadd := fun g p => ⟨g.1 +ᵥ p.1, g.2 +ᵥ p.2⟩
  zero_vadd := by
    intro ⟨p, q⟩
    change MProd.mk ((0 : G) +ᵥ p) ((0 : H) +ᵥ q) = MProd.mk p q
    rw [MProd.mk.injEq]
    exact ⟨zero_vadd _ _, zero_vadd _ _⟩
  add_vadd := by
    intro ⟨g₁, g₂⟩ ⟨h₁, h₂⟩ ⟨p, q⟩
    change MProd.mk ((g₁ + h₁) +ᵥ p) ((g₂ + h₂) +ᵥ q) =
      MProd.mk (g₁ +ᵥ h₁ +ᵥ p) (g₂ +ᵥ h₂ +ᵥ q)
    rw [MProd.mk.injEq]
    exact ⟨add_vadd _ _ _, add_vadd _ _ _⟩
  vsub := fun p q => (p.1 -ᵥ q.1, p.2 -ᵥ q.2)
  fiber := fun p q => fiber p.1 q.1 ∧ fiber p.2 q.2
  fiber_equiv := by
    have ⟨_, _, _⟩ := fiber_equiv (G := G) (P := P)
    have ⟨_, _, _⟩ := fiber_equiv (G := H) (P := Q)
    constructor <;> grind
  vsub_vadd' p q h := by
    cases p
    cases q
    rw [MProd.mk.injEq]
    exact ⟨vsub_vadd' _ _ h.1, vsub_vadd' _ _ h.2⟩
  vadd_vsub' g p := by
    cases g
    cases p
    exact Prod.ext (vadd_vsub' _ _) (vadd_vsub' _ _)
  vadd_fiber := by
    intro (g, h) p
    cases p
    exact ⟨vadd_fiber g _, vadd_fiber h _⟩

@[simp]
theorem mprod_vadd {G H P Q} [AddGroup G] [AddGroup H]
    [FiberedAddTorsor G P] [FiberedAddTorsor H Q]
    (g : G × H) (p : MProd P Q) :
    g +ᵥ p = ⟨g.1 +ᵥ p.1, g.2 +ᵥ p.2⟩ := rfl

@[simp]
theorem mprod_vsub {G H P Q} [AddGroup G] [AddGroup H]
    [FiberedAddTorsor G P] [FiberedAddTorsor H Q]
    (p q : MProd P Q) :
    p -ᵥ q = (p.1 -ᵥ q.1, p.2 -ᵥ q.2) := rfl

@[simp]
theorem mprod_fiber {G H P Q} [AddGroup G] [AddGroup H]
    [FiberedAddTorsor G P] [FiberedAddTorsor H Q]
    (p q : MProd P Q) :
    fiber p q ↔ fiber p.1 q.1 ∧ fiber p.2 q.2 := Iff.rfl

end FiberedAddTorsor

end NumLean
