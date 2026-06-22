import Init.Data.Range.Polymorphic.Basic
import Lean
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.Nodup

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

/-- Simple membership-aware no-break iteration.

Unlike `ForAllIn'`, the mutable state type is quantified by the method rather than by the
class, so instance search depends only on the range and index types. -/
class ForAllSimple (ρ : Type u) (α : outParam (Type v))
    (d : outParam (Membership α ρ)) where
  forAllSimple {β : Type w} (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → β) : β

attribute [always_inline, inline, specialize] ForAllSimple.forAllSimple

@[always_inline, inline] instance {ρ : Type u} {α : Type v} {β : Type w}
    {d : Membership α ρ} [ForAllIn' ρ α β d] : ForAllIn ρ α β where
  forAllIn xs init f :=
    ForAllIn'.forAllIn' xs init fun a _ acc => f a acc

/-- Reference semantics for membership-aware no-break iteration.

`entries xs` is a concrete enumeration of values together with membership proofs.  Lawful instances
state that `forAllIn'` is extensionally the corresponding left fold. -/
class LawfulForAllIn' (ρ : Type u) (α : outParam (Type v)) (β : Type w)
    (d : outParam (Membership α ρ)) [ForAllIn' ρ α β d] where
  entries : (xs : ρ) → List {a : α // a ∈ xs}
  mem_entries : ∀ {xs : ρ} {a : α}, (h : a ∈ xs) → ⟨a, h⟩ ∈ entries xs
  forAllIn'_eq_foldl : ∀ (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → β),
    ForAllIn'.forAllIn' xs init f =
      (entries xs).foldl (fun acc a => f a.1 a.2 acc) init

end Meta.ForAll
end NumLean
