module

public import NumLean.Interfaces.Fold.Basic
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Perm.Subperm

@[expose] public section

public section

namespace NumLean

namespace Fold

/-- Nodup lists with the same members are permutations of each other. -/
theorem List.Perm.of_nodup_of_forall_mem_iff {xs ys : List α}
    (hxs : xs.Nodup) (hys : ys.Nodup) (hmem : ∀ a, a ∈ xs ↔ a ∈ ys) :
    xs.Perm ys := by
  exact (hxs.subperm fun a ha => (hmem a).1 ha).antisymm
    (hys.subperm fun a ha => (hmem a).2 ha)

/-- A fold step commutes pairwise over distinct entries of a concrete entry list. -/
def ListPairwiseCommutes (entries : List α) (step : β → α → β) : Prop :=
  ∀ a b, a ∈ entries → b ∈ entries → ∀ acc,
    step (step acc a) b = step (step acc b) a

/-- Pairwise commutation only for distinct entries. This is the common condition for nodup ranges. -/
def ListPairwiseCommutesDistinct (entries : List α) (step : β → α → β) : Prop :=
  ∀ a b, a ∈ entries → b ∈ entries → a ≠ b → ∀ acc,
    step (step acc a) b = step (step acc b) a

/-- A membership-aware fold step commutes pairwise over distinct values in a range. -/
def PairwiseCommutes {ρ : Type u} {α : Type v} {β : Type w}
    [Membership α ρ] (xs : ρ) (f : (a : α) → a ∈ xs → β → β) : Prop :=
  ∀ i j : {a : α // a ∈ xs}, i ≠ j → ∀ acc,
    f j.1 j.2 (f i.1 i.2 acc) = f i.1 i.2 (f j.1 j.2 acc)

/-- A fold over a nodup list is invariant under permutations when all distinct entries commute. -/
theorem List.foldl_eq_of_perm_of_pairwise_commutes {entries entries' : List α}
    {step : β → α → β} (hperm : entries.Perm entries')
    (hcomm : ListPairwiseCommutes entries step) (init : β) :
    entries.foldl step init = entries'.foldl step init := by
  exact (hperm.foldl_eq' fun a ha b hb acc => hcomm a b ha hb acc) init

/-- `LawfulFold` can be evaluated with any permutation of its entries when the step commutes. -/
theorem LawfulFold.fold_eq_foldl_perm {ρ : Type u} {α : Type v} {β : Type w}
    {d : Membership α ρ} [FoldEntries ρ α d] [Fold ρ] [LawfulFold ρ α d]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → β)
    {entries' : List {a : α // a ∈ xs}}
    (hperm : (LawfulFold.entries (ρ := ρ) (α := α) xs).Perm entries')
    (hcomm : ListPairwiseCommutes (LawfulFold.entries (ρ := ρ) (α := α) xs)
      (fun acc a => f a.1 a.2 acc)) :
    Fold.fold xs init f = entries'.foldl (fun acc a => f a.1 a.2 acc) init := by
  rw [LawfulFold.fold_eq_foldl]
  exact List.foldl_eq_of_perm_of_pairwise_commutes hperm hcomm init

/-- Nodup version of permutation-invariance: commutation is required only for distinct entries. -/
theorem List.foldl_eq_of_perm_of_nodup_pairwise_commutes {entries entries' : List α}
    {step : β → α → β} (_hnodup : entries.Nodup) (hperm : entries.Perm entries')
    (hcomm : ListPairwiseCommutesDistinct entries step) (init : β) :
    entries.foldl step init = entries'.foldl step init := by
  apply List.foldl_eq_of_perm_of_pairwise_commutes hperm
  intro a b ha hb acc
  by_cases hab : a = b
  · subst b
    rfl
  · exact hcomm a b ha hb hab acc

/-- `LawfulFold` version of nodup permutation-invariance. -/
theorem LawfulFold.fold_eq_foldl_perm_of_pairwise_commutes {ρ : Type u} {α : Type v} {β : Type w}
    {d : Membership α ρ} [FoldEntries ρ α d] [Fold ρ] [LawfulFold ρ α d]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → β)
    {entries' : List {a : α // a ∈ xs}}
    (hperm : (LawfulFold.entries (ρ := ρ) (α := α) xs).Perm entries')
    (hcomm : PairwiseCommutes xs f) :
    Fold.fold xs init f = entries'.foldl (fun acc a => f a.1 a.2 acc) init := by
  rw [LawfulFold.fold_eq_foldl]
  apply List.foldl_eq_of_perm_of_nodup_pairwise_commutes
  · exact LawfulFold.entries_nodup (ρ := ρ) (α := α) xs
  · exact hperm
  · intro a b ha hb hne acc
    exact hcomm a b hne acc

end Fold

end NumLean
