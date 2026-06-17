import Init.Data.Range.Polymorphic.Basic

public section

namespace NumLean
namespace Meta.ForAll

/-- No-break iteration with the state type as a class parameter. -/
class ForAllIn (ρ : Type u) (α : outParam (Type v)) (β : Type w) where
  forAllIn (xs : ρ) (init : β) (f : α → β → β) : β

attribute [always_inline, inline, specialize] ForAllIn.forAllIn

/-- Membership-aware no-break iteration with the state type as a class parameter. -/
class ForAllIn' (ρ : Type u) (α : outParam (Type v)) (β : Type w)
    (d : outParam (Membership α ρ)) where
  forAllIn' (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → β) : β

attribute [always_inline, inline, specialize] ForAllIn'.forAllIn'

@[always_inline, inline] instance {ρ : Type u} {α : Type v} {β : Type w}
    {d : Membership α ρ} [ForAllIn' ρ α β d] : ForAllIn ρ α β where
  forAllIn xs init f :=
    ForAllIn'.forAllIn' xs init fun a _ acc => f a acc

end Meta.ForAll
end NumLean
