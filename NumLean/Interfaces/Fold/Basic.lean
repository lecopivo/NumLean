import Init.Data.Range.Polymorphic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.Nodup

public section

namespace NumLean

class FoldEntries (ρ : Type u) (α : outParam (Type v))
    (d : outParam (Membership α ρ)) where
  entries : (xs : ρ) → List {a : α // a ∈ xs}

class Fold (ρ : Type u) {α : outParam (Type v)}
    {d : outParam (Membership α ρ)} [FoldEntries ρ α d] where
  fold {β : Type w} (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → β) : β

def entries {ρ : Type u} {α : Type v} {d : Membership α ρ} [FoldEntries ρ α d]
    (xs : ρ) : List {a : α // a ∈ xs} :=
  FoldEntries.entries xs

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

This class is intentionally proof-only: the computational enumeration lives in `FoldEntries`, while
`LawfulFold` records only propositions about that canonical order. -/
class LawfulFold (ρ : Type u) (α : outParam (Type v))
    (d : outParam (Membership α ρ)) [FoldEntries ρ α d] [inst : Fold ρ] : Prop where
  mem_entries : ∀ {xs : ρ} {a : α}, (h : a ∈ xs) →
    ⟨a, h⟩ ∈ entries xs
  entries_nodup : ∀ xs : ρ, (entries xs).Nodup
  fold_eq_foldl : ∀ {β : Type w} (xs : ρ) (init : β)
    (f : (a : α) → a ∈ xs → β → β),
      Fold.fold (self := inst) xs (init : β) f =
        (entries xs).foldl
          (fun acc a => f a.1 a.2 acc) init

namespace LawfulFold

  abbrev entries {ρ : Type u} {α : Type v} {d : Membership α ρ}
    [FoldEntries ρ α d] [Fold ρ] [LawfulFold ρ α d] (xs : ρ) :
    List {a : α // a ∈ xs} :=
  NumLean.entries xs

end LawfulFold

end NumLean
