module

public import NumLean.Mathlib.FiberedAddTorsor.Basic

@[expose] public section

namespace NumLean

namespace FiberedAddTorsor

open FiberedAddTorsor

instance {G H} [AddGroup G] [AddGroup H]
    {P Q} [FiberedAddTorsor G P] [FiberedAddTorsor H Q] :
    FiberedAddTorsor (G × H) (P × Q) where
  vadd := fun (g, h) (p, q) => (g +ᵥ p, h +ᵥ q)
  zero_vadd _ := Prod.ext (zero_vadd _ _) (zero_vadd _ _)
  add_vadd _ _ _ := Prod.ext (add_vadd _ _ _) (add_vadd _ _ _)
  vsub := fun (p₁, q₁) (p₂, q₂) => (p₁ -ᵥ p₂, q₁ -ᵥ q₂)
  fiber := fun (p₁, q₁) (p₂, q₂) => fiber p₁ p₂ ∧ fiber q₁ q₂
  fiber_equiv := by
    have ⟨_, _, _⟩ := fiber_equiv (G := G) (P := P)
    have ⟨_, _, _⟩ := fiber_equiv (G := H) (P := Q)
    constructor <;> grind
  vsub_vadd' _ _ h := Prod.ext (vsub_vadd' _ _ h.1) (vsub_vadd' _ _ h.2)
  vadd_vsub' _ _ := Prod.ext (vadd_vsub' _ _) (vadd_vsub' _ _)
  vadd_fiber := by intro (g, h) (p, q); exact ⟨vadd_fiber g p, vadd_fiber h q⟩

@[simp]
theorem prod_vadd {G H P Q} [AddGroup G] [AddGroup H]
    [FiberedAddTorsor G P] [FiberedAddTorsor H Q]
    (g : G × H) (p : P × Q) :
    g +ᵥ p = (g.1 +ᵥ p.1, g.2 +ᵥ p.2) := rfl

@[simp]
theorem prod_vsub {G H P Q} [AddGroup G] [AddGroup H]
    [FiberedAddTorsor G P] [FiberedAddTorsor H Q]
    (p q : P × Q) :
    p -ᵥ q = (p.1 -ᵥ q.1, p.2 -ᵥ q.2) := rfl

@[simp]
theorem prod_fiber {G H P Q} [AddGroup G] [AddGroup H]
    [FiberedAddTorsor G P] [FiberedAddTorsor H Q]
    (p q : P × Q) :
    fiber p q ↔ fiber p.1 q.1 ∧ fiber p.2 q.2 := Iff.rfl

end FiberedAddTorsor

end NumLean
