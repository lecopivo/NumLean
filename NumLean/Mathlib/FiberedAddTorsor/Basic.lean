module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.AddTorsor.Defs
public import Mathlib.Algebra.AddTorsor.Basic

@[expose] public section

namespace NumLean

class FiberedAddTorsor (G : outParam Type*) (P : Type*) [AddGroup G]
    extends AddAction G P, VSub G P where
  fiber : P → P → Prop
  fiber_equiv : Equivalence fiber
  vsub_vadd' : ∀ p₁ p₂ : P, fiber p₁ p₂ → (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
  vadd_vsub' : ∀ (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
  vadd_fiber : ∀ (g : G) (p : P), fiber (g +ᵥ p) p

namespace FiberedAddTorsor

variable {G P : Type*} [AddGroup G] [FiberedAddTorsor G P]

theorem fiber_refl (p : P) : fiber p p :=
  fiber_equiv.refl p

theorem fiber_symm {p q : P} (h : fiber p q) : fiber q p :=
  fiber_equiv.symm h

theorem fiber_trans {p q r : P} (hpq : fiber p q) (hqr : fiber q r) : fiber p r :=
  fiber_equiv.trans hpq hqr

theorem vsub_vadd_of_fiber {p q : P} (h : fiber p q) : (p -ᵥ q) +ᵥ q = p :=
  vsub_vadd' p q h

theorem vadd_vsub (g : G) (p : P) : (g +ᵥ p) -ᵥ p = g :=
  vadd_vsub' g p

theorem fiber_vadd_left (g : G) (p : P) : fiber (g +ᵥ p) p :=
  vadd_fiber g p

theorem fiber_vadd_right (g : G) (p : P) : fiber p (g +ᵥ p) :=
  fiber_symm (vadd_fiber g p)

theorem fiber_vadd_vadd (g h : G) (p : P) : fiber (g +ᵥ p) (h +ᵥ p) :=
  fiber_trans (vadd_fiber g p) (fiber_symm (vadd_fiber h p))

theorem eq_of_vadd_eq_vadd {g h : G} {p : P} (hgh : g +ᵥ p = h +ᵥ p) : g = h := by
  calc
    g = (g +ᵥ p) -ᵥ p := (vadd_vsub g p).symm
    _ = (h +ᵥ p) -ᵥ p := by rw [hgh]
    _ = h := vadd_vsub h p

theorem vadd_eq_vadd_iff_eq {g h : G} (p : P) : g +ᵥ p = h +ᵥ p ↔ g = h := by
  constructor
  · exact eq_of_vadd_eq_vadd
  · intro hgh
    rw [hgh]

end FiberedAddTorsor

/-- `AddGroup` is `FiberedAddTorsor`. -/
instance {G} [AddGroup G] : FiberedAddTorsor G G where
  fiber _ _ := True
  fiber_equiv := by constructor <;> simp
  vsub_vadd' := by intros; simp
  vadd_vsub' := by intros; simp
  vadd_fiber := by intros; simp

end NumLean
