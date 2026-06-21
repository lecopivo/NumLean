import Init.Data.Range.Polymorphic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.Nodup

public section

namespace NumLean

/-- Membership-aware left fold over a range-like container.

The accumulator type is quantified by the method, so instance search depends only on the range and
index types. -/
class Fold (ρ : Type u) (α : outParam (Type v))
    (d : outParam (Membership α ρ)) where
  fold {β : Type w} (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → β) : β
  entries : (xs : ρ) → List {a : α // a ∈ xs}

def entries (ρ : Type u) {α : Type v} {d : Membership α ρ} [inst : Fold ρ α d]
    (xs : ρ) : List {a : α // a ∈ xs} :=
  Fold.entries (self := inst) xs

attribute [always_inline, inline, specialize] Fold.fold

theorem List.foldl_append_singleton {α : Type u} (xs acc : List α) :
    xs.foldl (fun acc x => acc ++ [x]) acc = acc ++ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, List.append_assoc]

theorem List.foldl_append_singleton_nil {α : Type u} (xs : List α) :
    xs.foldl (fun acc x => acc ++ [x]) [] = xs := by
  simpa using List.foldl_append_singleton xs ([] : List α)

theorem List.flatten_map_singleton {α : Type u} {β : Type v} (xs : List α) (f : α → β) :
    (xs.map fun x => [f x]).flatten = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Laws connecting an executable `Fold` with its concrete reference enumeration.

This class is intentionally proof-only: the computational enumeration lives in `Fold.entries`, while
`LawfulFold` records only propositions about that canonical order. -/
class LawfulFold (ρ : Type u) (α : outParam (Type v))
    (d : outParam (Membership α ρ)) [inst : Fold ρ α d] : Prop where
  mem_entries : ∀ {xs : ρ} {a : α}, (h : a ∈ xs) →
    ⟨a, h⟩ ∈ Fold.entries (self := inst) xs
  entries_nodup : ∀ xs : ρ, (Fold.entries (self := inst) xs).Nodup
  fold_eq_foldl : ∀ {β : Type w} (xs : ρ) (init : β)
    (f : (a : α) → a ∈ xs → β → β),
      Fold.fold (self := inst) xs (init : β) f =
        (Fold.entries (self := inst) xs).foldl
          (fun acc a => f a.1 a.2 acc) init

namespace LawfulFold

  abbrev entries {ρ : Type u} {α : Type v} {d : Membership α ρ}
    [inst : Fold ρ α d] (xs : ρ) :
    List {a : α // a ∈ xs} :=
  Fold.entries (self := inst) xs

end LawfulFold

end NumLean
