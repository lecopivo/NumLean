import NumLean.Interfaces.Fold.Basic
import NumLean.Interfaces.Fold.Filter
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace NumLean

namespace Fold

private theorem List.foldl_add_eq_add_sum [AddCommMonoid A] (xs : List α) (f : α → A) (init : A) :
    xs.foldl (fun acc x => acc + f x) init = init + (xs.map f).sum := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, add_assoc]

private theorem List.eq_singleton_of_mem_nodup_unique {α : Type u} {xs : List α} {a : α}
    (ha : a ∈ xs) (hnd : xs.Nodup) (huniq : ∀ b ∈ xs, b = a) : xs = [a] := by
  cases xs with
  | nil => cases ha
  | cons b bs =>
      have hb : b = a := huniq b (by simp)
      subst b
      simp only [List.nodup_cons] at hnd
      have hbs : bs = [] := by
        apply List.eq_nil_iff_forall_not_mem.2
        intro c hc
        have hc_eq : c = a := huniq c (by simp [hc])
        subst c
        exact hnd.1 hc
      simp [hbs]

theorem foldl_guarded_eq_filterMap {α β : Type u} (xs : List α) (init : β)
    (p : α → Prop) [DecidablePred p] (f : (a : α) → p a → β → β) :
    xs.foldl (fun acc a => if h : p a then f a h acc else acc) init =
      (xs.filterMap fun a => if h : p a then some (⟨a, h⟩ : {a // p a}) else none).foldl
        (fun acc a => f a.1 a.2 acc) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : p x
      · simp [hx, ih]
      · simp [hx, ih]

open Fold Classical in
theorem fold_eq_sum {A ρ ι} [m : Membership ι ρ] [AddCommMonoid A]
    [FoldEntries ρ ι m] [Fold ρ]
    [LawfulFold ρ ι m]
    (range : ρ) (f : (i : ι) → i ∈ range → A) (init : A) :
    Fold.fold range (init := init) (fun i hi a => a + f i hi)
    =
    init + ∑ i ∈ (NumLean.entries range).toFinset, f i.1 i.2 := by
  rw [LawfulFold.fold_eq_foldl]
  rw [List.foldl_add_eq_add_sum]
  rw [← List.sum_toFinset]
  · exact LawfulFold.entries_nodup range

open Fold Classical Function in
theorem fold_eq_vector_map {α ρ ι n} [m : Membership ι ρ] [FoldEntries ρ ι m] [Fold ρ]
    [LawfulFold ρ ι m] (range : ρ)
    (imap : (i : ι) → i ∈ range → Nat) (f : (i : ι) → i ∈ range → α → α) (init : Vector α n)
    (himap : ∀ i hi, imap i hi < n)
    (himap' : Injective (fun i : {i' // i' ∈ range} => imap i.1 i.2)) :
    Fold.fold range (init := init) (fun i hi xs =>
      xs.set (imap i hi) (f i hi (getElem xs (imap i hi) (himap i hi))) (by grind))
    =
    init.mapFinIdx (fun j xj _ =>
      if h : ∃ i, ∃ hi : i ∈ range, imap i hi = j then
        let i := choose h
        let hi := choose (choose_spec h)
        f i hi xj
      else
        xj) := by
  rw [LawfulFold.fold_eq_foldl]
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_mapFinIdx]
  let step : Vector α n → {i' // i' ∈ range} → Vector α n := fun xs i =>
      xs.set (imap i.1 i.2)
        (f i.1 i.2 (getElem xs (imap i.1 i.2) (by grind)))
        (by grind)
  change ((NumLean.entries range).foldl step init)[j] = _
  have hfoldFin := FoldMap.foldl_get_eq_foldl_filter_affectors
      (entries := NumLean.entries range)
      (init := init)
      (step := step)
      (read := fun xs (j : Fin n) => xs[j])
      (deps := fun j : Fin n => {j})
      (affectors := fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1})
      (i := ⟨j, hj⟩)
      (by simp)
      (by
        intro k hk idx hidx xs
        simp only [Set.mem_singleton_iff] at hk
        subst k
        simp only [Set.mem_setOf_eq] at hidx
        change (step xs idx)[j] = xs[j]'hj
        simp [step, hidx])
      (by
        intro idx xs ys hagree k hk
        simp only [Set.mem_singleton_iff] at hk
        subst k
        by_cases hidx : imap idx.1 idx.2 = j
        · have hread : xs[j] = ys[j] := hagree ⟨j, hj⟩ (by simp)
          dsimp [step]
          have hreadIdx :
              xs[imap idx.1 idx.2]'(himap idx.1 idx.2) =
                ys[imap idx.1 idx.2]'(himap idx.1 idx.2) := by
            simpa [hidx] using hread
          simp [hidx]
          exact congrArg (f idx.1 idx.2) hread
        · dsimp [step]
          have hread : xs[j] = ys[j] := hagree ⟨j, hj⟩ (by simp)
          simp [hidx, hread])
  change (fun xs (j : Fin n) => xs[j])
      ((NumLean.entries range).foldl step init) ⟨j, hj⟩ = _
  rw [hfoldFin]
  · by_cases h : ∃ i, ∃ hi : i ∈ range, imap i hi = j
    · let i := choose h
      let hi := choose (choose_spec h)
      have hij : imap i hi = j := choose_spec (choose_spec h)
      have hfilter :
          ((NumLean.entries range).filter fun idx =>
              @decide (idx ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩))
                (Classical.propDecidable _)) =
            [⟨i, hi⟩] := by
        apply List.eq_singleton_of_mem_nodup_unique
        · exact List.mem_filter.mpr ⟨LawfulFold.mem_entries (xs := range) hi, by simp [hij]⟩
        · exact (LawfulFold.entries_nodup range).filter _
        · intro b hb
          simp only [List.mem_filter] at hb
          have hbmem : b ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩) :=
            @of_decide_eq_true _ (Classical.propDecidable _) hb.2
          have hbidx : imap b.1 b.2 = j := hbmem
          apply himap'
          simp [hbidx, hij]
      change (fun xs (j : Fin n) => xs[j])
        (((NumLean.entries range).filter fun idx =>
          @decide (idx ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩))
            (Classical.propDecidable _)).foldl step init)
        ⟨j, hj⟩ = _
      rw [hfilter]
      simp only [List.foldl_cons, List.foldl_nil]
      simp [step, hij, h]
      dsimp [i, hi]
    · have hfilter :
          ((NumLean.entries range).filter fun idx =>
              @decide (idx ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩))
                (Classical.propDecidable _)) = [] := by
        apply List.eq_nil_iff_forall_not_mem.2
        intro idx hidx
        simp only [List.mem_filter] at hidx
        have hmem : idx ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩) :=
          @of_decide_eq_true _ (Classical.propDecidable _) hidx.2
        exact h ⟨idx.1, idx.2, hmem⟩
      change (fun xs (j : Fin n) => xs[j])
        (((NumLean.entries range).filter fun idx =>
          @decide (idx ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩))
            (Classical.propDecidable _)).foldl step init)
        ⟨j, hj⟩ = _
      rw [hfilter]
      simp only [List.foldl_nil]
      simp [h]


open Fold Classical Function in
theorem fold_eq_vector_map' {α ρ ι n} [m : Membership ι ρ] [FoldEntries ρ ι m] [Fold ρ]
    [LawfulFold ρ ι m] (range : ρ)
    (imap : (i : ι) → i ∈ range → Nat) (f : (i : ι) → i ∈ range → α → α) (init : Vector α n)
    (himap : ∀ i hi, imap i hi < n)
    (himap' : Injective (fun i : {i' // i' ∈ range} => imap i.1 i.2)) :
    Fold.fold range (init := init) (fun i hi xs =>
      xs.set (imap i hi) (f i hi (getElem xs (imap i hi) (himap i hi))) (by grind))
    =
    init.mapFinIdx (fun j xj _ =>
      if h : j ∈ Set.range (fun i : {i' // i' ∈ range} => imap i.1 i.2) then
        have : Nonempty {i' // i' ∈ range} := by have ⟨i,_⟩ := h; exact ⟨i⟩
        let ⟨i,hi⟩ := invFun (fun i : {i' // i' ∈ range} => imap i.1 i.2) j
        f i hi xj
      else
        xj) := by
  rw [LawfulFold.fold_eq_foldl]
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_mapFinIdx]
  let step : Vector α n → {i' // i' ∈ range} → Vector α n := fun xs i =>
      xs.set (imap i.1 i.2)
        (f i.1 i.2 (getElem xs (imap i.1 i.2) (by grind)))
        (by grind)
  change ((NumLean.entries range).foldl step init)[j] = _
  have hfoldFin := FoldMap.foldl_get_eq_foldl_filter_affectors
      (entries := NumLean.entries range)
      (init := init)
      (step := step)
      (read := fun xs (j : Fin n) => xs[j])
      (deps := fun j : Fin n => {j})
      (affectors := fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1})
      (i := ⟨j, hj⟩)
      (by simp)
      (by
        intro k hk idx hidx xs
        simp only [Set.mem_singleton_iff] at hk
        subst k
        simp only [Set.mem_setOf_eq] at hidx
        change (step xs idx)[j] = xs[j]'hj
        simp [step, hidx])
      (by
        intro idx xs ys hagree k hk
        simp only [Set.mem_singleton_iff] at hk
        subst k
        by_cases hidx : imap idx.1 idx.2 = j
        · have hread : xs[j] = ys[j] := hagree ⟨j, hj⟩ (by simp)
          dsimp [step]
          have hreadIdx :
              xs[imap idx.1 idx.2]'(himap idx.1 idx.2) =
                ys[imap idx.1 idx.2]'(himap idx.1 idx.2) := by
            simpa [hidx] using hread
          simp [hidx]
          exact congrArg (f idx.1 idx.2) hread
        · dsimp [step]
          have hread : xs[j] = ys[j] := hagree ⟨j, hj⟩ (by simp)
          simp [hidx, hread])
  change (fun xs (j : Fin n) => xs[j])
      ((NumLean.entries range).foldl step init) ⟨j, hj⟩ = _
  rw [hfoldFin]
  · by_cases h : j ∈ Set.range (fun i : {i' // i' ∈ range} => imap i.1 i.2)
    · haveI : Nonempty {i' // i' ∈ range} := by
        rcases h with ⟨i, _⟩
        exact ⟨i⟩
      let idx := invFun (fun i : {i' // i' ∈ range} => imap i.1 i.2) j
      have hij : imap idx.1 idx.2 = j := Function.invFun_eq h
      have hfilter :
          ((NumLean.entries range).filter fun idx' =>
              @decide (idx' ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩))
                (Classical.propDecidable _)) =
            [idx] := by
        apply List.eq_singleton_of_mem_nodup_unique
        · exact List.mem_filter.mpr ⟨LawfulFold.mem_entries (xs := range) idx.2, by simp [hij]⟩
        · exact (LawfulFold.entries_nodup range).filter _
        · intro b hb
          simp only [List.mem_filter] at hb
          have hbmem : b ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩) :=
            @of_decide_eq_true _ (Classical.propDecidable _) hb.2
          have hbidx : imap b.1 b.2 = j := hbmem
          apply himap'
          simp [hbidx, hij]
      change (fun xs (j : Fin n) => xs[j])
        (((NumLean.entries range).filter fun idx' =>
          @decide (idx' ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩))
            (Classical.propDecidable _)).foldl step init)
        ⟨j, hj⟩ = _
      rw [hfilter]
      simp only [List.foldl_cons, List.foldl_nil]
      simp [step, hij, h, idx]
    · have hfilter :
          ((NumLean.entries range).filter fun idx =>
              @decide (idx ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩))
                (Classical.propDecidable _)) = [] := by
        apply List.eq_nil_iff_forall_not_mem.2
        intro idx hidx
        simp only [List.mem_filter] at hidx
        have hmem : idx ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩) :=
          @of_decide_eq_true _ (Classical.propDecidable _) hidx.2
        exact h ⟨idx, hmem⟩
      change (fun xs (j : Fin n) => xs[j])
        (((NumLean.entries range).filter fun idx =>
          @decide (idx ∈ ((fun j : Fin n => {i : {i' // i' ∈ range} | imap i.1 i.2 = j.1}) ⟨j, hj⟩))
            (Classical.propDecidable _)).foldl step init)
        ⟨j, hj⟩ = _
      rw [hfilter]
      simp only [List.foldl_nil]
      simp [h]

end Fold
