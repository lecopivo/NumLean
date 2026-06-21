import NumLean.Data.Vector.RingArrayOps.Basic
import NumLean.Data.Vector.TensorOps.FoldMap

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

theorem scalRef_in_range {K : Type} [Mul K] {xn : Nat} (n : Nat)
    (a : K) (xs : Vector K xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (i : Nat) (hi : i ∈ (0...n : Std.Rco Nat)) :
    (scalRef n a xs xoff xinc hx)[xoff + i * xinc]'(by tbounds) =
      a * xs[xoff + i * xinc]'(by tbounds) := by
  classical
  unfold scalRef
  rw [FoldMap.foldl_get_eq_foldl_filter_affectors_vector
      (entries := rcoNativeEntries (0...n : Std.Rco Nat))
      (deps := fun i : Fin xn => {i})
      (hself := by simp)
      (affectors := fun j : Fin xn =>
        {idx : {i : Nat // i ∈ (0...n : Std.Rco Nat)} | xoff + idx.1 * xinc = j.1})]
  case hpreserve =>
    intro j hj idx hidx ys
    simp only [Set.mem_singleton_iff] at hj
    subst hj
    simp only [Set.mem_setOf_eq] at hidx
    change (ys.set (xoff + idx.1 * xinc)
        (a * ys[xoff + idx.1 * xinc]'(TBounds.stride_lt_rco_of_bound hx idx.2))
        (TBounds.stride_lt_rco_of_bound hx idx.2))[xoff + i * xinc]'(by tbounds) =
      ys[xoff + i * xinc]'(by tbounds)
    rw [Vector.getElem_set]
    simp only [Nat.add_left_cancel_iff, mul_eq_mul_right_iff]
    by_cases h : idx.1 = i ∨ xinc = 0
    · exfalso
      cases h with
      | inl hidx' => exact hidx (by rw [hidx'])
      | inr hzero => exact hx.2 hzero
    · simp [h]
  case hdeps =>
    intro idx ys zs hagree j hj
    simp only [Set.mem_singleton_iff] at hj
    subst hj
    by_cases hidx : xoff + idx.1 * xinc = xoff + i * xinc
    · have hread : ys[xoff + i * xinc]'(by tbounds) = zs[xoff + i * xinc]'(by tbounds) :=
        hagree ⟨xoff + i * xinc, by tbounds⟩ (by simp)
      simp [hidx]
      exact congrArg (fun x => a * x) hread
    · have hread : ys[xoff + i * xinc]'(by tbounds) = zs[xoff + i * xinc]'(by tbounds) :=
        hagree ⟨xoff + i * xinc, by tbounds⟩ (by simp)
      have hcond : ¬(idx.1 = i ∨ xinc = 0) := by
        intro h
        cases h with
        | inl hi' => exact hidx (by rw [hi'])
        | inr hzero => exact hx.2 hzero
      simp [hcond]
      exact hread
  have hEntries :
      ((rcoNativeEntries (0...n : Std.Rco Nat)).filter fun idx =>
          @decide (idx ∈ ({idx | xoff + idx.1 * xinc =
            (⟨xoff + i * xinc, by tbounds⟩ : Fin xn).1} :
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
      | inr hzero => exact (hx.2 hzero).elim
  conv => enter [1, 1, 3]; rw [hEntries]
  simp only [List.foldl_cons, List.foldl_nil]
  simp

theorem scalRef_out_range {K : Type} [Mul K] {xn : Nat} (n : Nat)
    (a : K) (xs : Vector K xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (j : Nat) (hj : j < xn) (hjout : ∀ i, i ∈ (0...n : Std.Rco Nat) → j ≠ xoff + i * xinc) :
    (scalRef n a xs xoff xinc hx)[j] = xs[j] := by
  classical
  unfold scalRef
  rw [FoldMap.foldl_get_eq_foldl_filter_affectors_vector
      (entries := rcoNativeEntries (0...n : Std.Rco Nat))
      (deps := fun i : Fin xn => {i})
      (hself := by simp)
      (affectors := fun j : Fin xn =>
        {idx : {i : Nat // i ∈ (0...n : Std.Rco Nat)} | xoff + idx.1 * xinc = j.1})]
  case hpreserve =>
    intro k hk idx hidx ys
    simp only [Set.mem_singleton_iff] at hk
    subst hk
    simp only [Set.mem_setOf_eq] at hidx
    change (ys.set (xoff + idx.1 * xinc)
        (a * ys[xoff + idx.1 * xinc]'(TBounds.stride_lt_rco_of_bound hx idx.2))
        (TBounds.stride_lt_rco_of_bound hx idx.2))[j]'hj = ys[j]'hj
    rw [Vector.getElem_set]
    simp [hidx]
  case hdeps =>
    intro idx ys zs hagree k hk
    simp only [Set.mem_singleton_iff] at hk
    subst hk
    by_cases hidx : xoff + idx.1 * xinc = j
    · have hread : ys[j] = zs[j] := hagree ⟨j, hj⟩ (by simp)
      simp [hidx]
      exact congrArg (fun x => a * x) hread
    · have hread : ys[j] = zs[j] := hagree ⟨j, hj⟩ (by simp)
      simp [hidx]
      exact hread
  have hEntries :
      ((rcoNativeEntries (0...n : Std.Rco Nat)).filter fun idx =>
          @decide (idx ∈ ({idx | xoff + idx.1 * xinc = (⟨j, hj⟩ : Fin xn).1} :
            Set {i : Nat // i ∈ (0...n : Std.Rco Nat)})) (Classical.propDecidable _)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro idx hidx
    simp at hidx
    exact hjout idx.1 idx.2 hidx.2.symm
  conv => enter [1, 1, 3]; rw [hEntries]
  simp only [List.foldl_nil]

theorem scalRef_full_ext {K : Type} [Mul K] {n : Nat} (a : K) (xs : Vector K n) (i : Fin n) :
    (scalRef n a xs 0 1 (by simp))[i] = a * xs[i] := by
  have hi : i.1 ∈ (0...n : Std.Rco Nat) := by
    rw [Std.Rco.mem_iff]
    exact ⟨Nat.zero_le i.1, i.2⟩
  simpa using scalRef_in_range n a xs 0 1 (by simp) i.1 hi

theorem scalRef_full_eq_ofFn {K : Type} [Mul K] {n : Nat} (a : K) (xs : Vector K n) :
    scalRef n a xs 0 1 (by simp) = Vector.ofFn (fun i : Fin n => a * xs[i]) := by
  ext i hi
  simpa using scalRef_full_ext a xs ⟨i, hi⟩

end Vector

end NumLean
