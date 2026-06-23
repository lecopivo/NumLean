import NumLean.Data.Vector.RingArrayOps.Basic
import NumLean.Interfaces.Fold.Filter

set_option backward.do.legacy false

namespace NumLean

namespace Vector

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

theorem mulRef_in_range {K : Type} [Mul K] {xn yn : Nat} (n : Nat)
    (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0)
    (i : Nat) (hi : i ∈ (0...n : Std.Rco Nat)) :
    (mulRef n xs xoff xinc ys yoff yinc hx hy)[yoff + i * yinc]'(by tbounds) =
      ys[yoff + i * yinc]'(by tbounds) * xs[xoff + i * xinc]'(by tbounds) := by
  classical
  unfold mulRef
  simp only [LawfulFold.fold_eq_foldl (ρ := Std.Rco Nat) (α := Nat)
    (d := (inferInstance : Membership Nat (Std.Rco Nat)))
    (xs := (0...n : Std.Rco Nat))]
  simp only [setElem_nat_eq_set, bind, Id.run, pure]
  rw [FoldMap.foldl_get_eq_foldl_filter_affectors_vector
      (entries := NumLean.entries (0...n : Std.Rco Nat))
      (deps := fun i : Fin yn => {i})
      (hself := by simp)
      (affectors := fun j : Fin yn =>
        {idx : {i : Nat // i ∈ (0...n : Std.Rco Nat)} | yoff + idx.1 * yinc = j.1})]
  case hpreserve =>
    intro j hj idx hidx zs
    simp only [Set.mem_singleton_iff] at hj
    subst hj
    simp only [Set.mem_setOf_eq] at hidx
    change (zs.set (yoff + idx.1 * yinc)
        (zs[yoff + idx.1 * yinc]'(TBounds.stride_lt_rco_of_bound hy idx.2) *
          xs[xoff + idx.1 * xinc]'(TBounds.stride_lt_rco_of_bound hx idx.2))
        (TBounds.stride_lt_rco_of_bound hy idx.2))[yoff + i * yinc]'(by tbounds) =
      zs[yoff + i * yinc]'(by tbounds)
    rw [Vector.getElem_set]
    simp only [Nat.add_left_cancel_iff, mul_eq_mul_right_iff]
    by_cases h : idx.1 = i ∨ yinc = 0
    · exfalso
      cases h with
      | inl hidx' => exact hidx (by rw [hidx'])
      | inr hzero => exact hy.2 hzero
    · simp [h]
  case hdeps =>
    intro idx zs ws hagree j hj
    simp only [Set.mem_singleton_iff] at hj
    subst hj
    by_cases hidx : yoff + idx.1 * yinc = yoff + i * yinc
    · have hread : zs[yoff + i * yinc]'(by tbounds) = ws[yoff + i * yinc]'(by tbounds) :=
        hagree ⟨yoff + i * yinc, by tbounds⟩ (by simp)
      simp [hidx]
      exact congrArg (fun y => y * xs[xoff + idx.1 * xinc]'(TBounds.stride_lt_rco_of_bound hx idx.2)) hread
    · have hread : zs[yoff + i * yinc]'(by tbounds) = ws[yoff + i * yinc]'(by tbounds) :=
        hagree ⟨yoff + i * yinc, by tbounds⟩ (by simp)
      have hcond : ¬(idx.1 = i ∨ yinc = 0) := by
        intro h
        cases h with
        | inl hi' => exact hidx (by rw [hi'])
        | inr hzero => exact hy.2 hzero
      simp [hcond]
      exact hread
  have hEntries :
      ((NumLean.entries (0...n : Std.Rco Nat)).filter fun idx =>
          @decide (idx ∈ ({idx | yoff + idx.1 * yinc =
            (⟨yoff + i * yinc, by tbounds⟩ : Fin yn).1} :
              Set {i : Nat // i ∈ (0...n : Std.Rco Nat)})) (Classical.propDecidable _)) =
        [⟨i, hi⟩] := by
    apply List.eq_singleton_of_mem_nodup_unique
    · simp only [List.mem_filter, Set.mem_setOf_eq]
      exact ⟨LawfulRcoNativeStep.mem_entries hi, rfl⟩
    · exact (LawfulRcoNativeStep.entries_nodup (0...n : Std.Rco Nat)).filter _
    · intro idx hidx
      simp at hidx
      apply Subtype.ext
      cases hidx.2 with
      | inl h => exact h
      | inr hzero => exact (hy.2 hzero).elim
  conv => enter [1, 1, 3]; rw [hEntries]
  simp only [List.foldl_cons, List.foldl_nil]
  simp

theorem mulRef_out_range {K : Type} [Mul K] {xn yn : Nat} (n : Nat)
    (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0)
    (j : Nat) (hj : j < yn) (hjout : ∀ i, i ∈ (0...n : Std.Rco Nat) → j ≠ yoff + i * yinc) :
    (mulRef n xs xoff xinc ys yoff yinc hx hy)[j] = ys[j] := by
  classical
  unfold mulRef
  simp only [LawfulFold.fold_eq_foldl (ρ := Std.Rco Nat) (α := Nat)
    (d := (inferInstance : Membership Nat (Std.Rco Nat)))
    (xs := (0...n : Std.Rco Nat))]
  simp only [setElem_nat_eq_set, bind, Id.run, pure]
  rw [FoldMap.foldl_get_eq_foldl_filter_affectors_vector
      (entries := NumLean.entries (0...n : Std.Rco Nat))
      (deps := fun i : Fin yn => {i})
      (hself := by simp)
      (affectors := fun j : Fin yn =>
        {idx : {i : Nat // i ∈ (0...n : Std.Rco Nat)} | yoff + idx.1 * yinc = j.1})]
  case hpreserve =>
    intro k hk idx hidx zs
    simp only [Set.mem_singleton_iff] at hk
    subst hk
    simp only [Set.mem_setOf_eq] at hidx
    change (zs.set (yoff + idx.1 * yinc)
        (zs[yoff + idx.1 * yinc]'(TBounds.stride_lt_rco_of_bound hy idx.2) *
          xs[xoff + idx.1 * xinc]'(TBounds.stride_lt_rco_of_bound hx idx.2))
        (TBounds.stride_lt_rco_of_bound hy idx.2))[j]'hj = zs[j]'hj
    rw [Vector.getElem_set]
    simp [hidx]
  case hdeps =>
    intro idx zs ws hagree k hk
    simp only [Set.mem_singleton_iff] at hk
    subst hk
    by_cases hidx : yoff + idx.1 * yinc = j
    · have hread : zs[j] = ws[j] := hagree ⟨j, hj⟩ (by simp)
      simp [hidx]
      exact congrArg (fun y => y * xs[xoff + idx.1 * xinc]'(TBounds.stride_lt_rco_of_bound hx idx.2)) hread
    · have hread : zs[j] = ws[j] := hagree ⟨j, hj⟩ (by simp)
      simp [hidx]
      exact hread
  have hEntries :
      ((NumLean.entries (0...n : Std.Rco Nat)).filter fun idx =>
          @decide (idx ∈ ({idx | yoff + idx.1 * yinc = (⟨j, hj⟩ : Fin yn).1} :
            Set {i : Nat // i ∈ (0...n : Std.Rco Nat)})) (Classical.propDecidable _)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro idx hidx
    simp at hidx
    exact hjout idx.1 idx.2 hidx.2.symm
  conv => enter [1, 1, 3]; rw [hEntries]
  simp only [List.foldl_nil]

theorem mulRef_full_ext {K : Type} [Mul K] {n : Nat} (xs ys : Vector K n) (i : Fin n) :
    (mulRef n xs 0 1 ys 0 1 (by simp) (by simp))[i] = ys[i] * xs[i] := by
  have hi : i.1 ∈ (0...n : Std.Rco Nat) := by
    rw [Std.Rco.mem_iff]
    exact ⟨Nat.zero_le i.1, i.2⟩
  simpa using mulRef_in_range n xs 0 1 ys 0 1 (by simp) (by simp) i.1 hi

theorem mulRef_full_eq_ofFn {K : Type} [Mul K] {n : Nat} (xs ys : Vector K n) :
    mulRef n xs 0 1 ys 0 1 (by simp) (by simp) =
      Vector.ofFn (fun i : Fin n => ys[i] * xs[i]) := by
  ext i hi
  simpa using mulRef_full_ext xs ys ⟨i, hi⟩

end Vector

end NumLean
