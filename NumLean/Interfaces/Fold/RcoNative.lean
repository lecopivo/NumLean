import NumLean.Interfaces.Fold.Basic

public section

namespace NumLean

/-- Native stepping support for half-open ranges.

The executable loop uses `next`; `measure` and its laws are only for termination proofs. -/
class RcoNativeStep (α : Type u) [LE α] [LT α] where
  next : α → α
  measure : Std.Rco α → α → Nat
  le_refl : ∀ a : α, a ≤ a
  lower_le_next : ∀ {xs : Std.Rco α} {i : α}, xs.lower ≤ i → i < xs.upper → xs.lower ≤ next i
  measure_next_lt : ∀ {xs : Std.Rco α} {i : α}, i < xs.upper → measure xs (next i) < measure xs i

attribute [always_inline, inline] RcoNativeStep.next

/-- Reference enumeration for native-step ranges, starting from `i`.

This follows the same step relation as the executable loop. The `measure` recursion is only for
termination and is erased from runtime code. -/
def rcoNativeEntriesFrom {α : Type u} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) : List {a : α // a ∈ xs} :=
  if hhi : i < xs.upper then
    ⟨i, by exact ⟨hlo, hhi⟩⟩ ::
      rcoNativeEntriesFrom xs (RcoNativeStep.next i) (RcoNativeStep.lower_le_next hlo hhi)
  else
    []
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

/-- Reference enumeration for native-step half-open ranges. -/
def rcoNativeEntries {α : Type u} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) : List {a : α // a ∈ xs} :=
  rcoNativeEntriesFrom xs xs.lower (RcoNativeStep.le_refl xs.lower)

/-- Lawful native stepping support for half-open ranges. -/
class LawfulRcoNativeStep (α : Type u) [LE α] [LT α] [DecidableLT α]
    [RcoNativeStep α] : Prop where
  mem_entries : ∀ {xs : Std.Rco α} {a : α}, (h : a ∈ xs) →
    ⟨a, h⟩ ∈ rcoNativeEntries xs
  entries_nodup : ∀ xs : Std.Rco α, (rcoNativeEntries xs).Nodup

theorem mem_rcoNativeEntries {α : Type u} [LE α] [LT α] [DecidableLT α]
    [RcoNativeStep α] [LawfulRcoNativeStep α] {xs : Std.Rco α} {j : α} (hj : j ∈ xs) :
    ⟨j, hj⟩ ∈ rcoNativeEntries xs := by
  exact LawfulRcoNativeStep.mem_entries hj

@[always_inline, inline, specialize] def foldRcoNativeLoop {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (acc : β)
    (f : (a : α) → a ∈ xs → β → β) : β :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    foldRcoNativeLoop xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) (f i hmem acc) f
  else
    acc
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

theorem foldRcoNativeLoop_eq_foldl {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (acc : β)
    (f : (a : α) → a ∈ xs → β → β) :
    foldRcoNativeLoop xs i hlo acc f =
      (rcoNativeEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc) acc := by
  unfold foldRcoNativeLoop rcoNativeEntriesFrom
  split
  · rename_i hhi
    exact foldRcoNativeLoop_eq_foldl xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) (f i (by exact ⟨hlo, hhi⟩) acc) f
  · rfl
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

@[always_inline, inline, default_instance low] instance instFoldRcoNative {α : Type u}
    [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    Fold (Std.Rco α) α inferInstance where
  fold xs init f :=
    foldRcoNativeLoop xs xs.lower (RcoNativeStep.le_refl xs.lower) init f
  entries := rcoNativeEntries

instance (priority := low) instLawfulFoldRcoNative {α : Type u}
    [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] [LawfulRcoNativeStep α] :
    LawfulFold (Std.Rco α) α inferInstance where
  mem_entries {xs} {a} h := by
    exact mem_rcoNativeEntries h
  entries_nodup xs := by
    exact LawfulRcoNativeStep.entries_nodup xs
  fold_eq_foldl xs init f := by
    change foldRcoNativeLoop xs xs.lower (RcoNativeStep.le_refl xs.lower) init f =
      (rcoNativeEntries xs).foldl (fun acc a => f a.1 a.2 acc) init
    exact foldRcoNativeLoop_eq_foldl xs xs.lower (RcoNativeStep.le_refl xs.lower) init f

theorem UInt64.toNat_add_one_of_lt {i upper : UInt64} (h : i < upper) :
    (i + 1).toNat = i.toNat + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat]
  have hiu : i.toNat < upper.toNat := UInt64.lt_iff_toNat_lt.mp h
  have hup : upper.toNat < 2 ^ 64 := UInt64.toNat_lt upper
  have hs : i.toNat + 1 < 2 ^ 64 := by omega
  have hone : 1 % 2 ^ 64 = 1 := by omega
  rw [hone]
  exact Nat.mod_eq_of_lt hs

theorem USize.toNat_add_one_of_lt {i upper : USize} (h : i < upper) :
    (i + 1).toNat = i.toNat + 1 := by
  rw [USize.toNat_add, USize.toNat_ofNat]
  have hiu : i.toNat < upper.toNat := USize.lt_iff_toNat_lt.mp h
  have hup : upper.toNat < USize.size := USize.toNat_lt_size upper
  have hs : i.toNat + 1 < USize.size := by omega
  have hone : 1 % 2 ^ System.Platform.numBits = 1 := by
    have h1 : 1 < USize.size := by
      have hle : 2 ^ 32 ≤ USize.size := USize.le_size
      omega
    simp [Nat.mod_eq_of_lt h1]
  rw [hone]
  exact Nat.mod_eq_of_lt (by simpa [USize.size] using hs)

@[always_inline, inline] instance instRcoNativeStepNat : RcoNativeStep Nat where
  next i := i + 1
  measure xs i := xs.upper - i
  le_refl := Nat.le_refl
  lower_le_next := by
    intro xs i hlo _hhi
    exact Nat.le_trans hlo (Nat.le_succ i)
  measure_next_lt := by
    intro xs i hhi
    omega

@[always_inline, inline] instance instRcoNativeStepInt : RcoNativeStep Int where
  next i := i + 1
  measure xs i := (xs.upper - i).toNat
  le_refl := by
    intro a
    exact Int.le_refl a
  lower_le_next := by
    intro xs i hlo _hhi
    omega
  measure_next_lt := by
    intro xs i hhi
    omega

@[always_inline, inline] instance instRcoNativeStepUInt64 : RcoNativeStep UInt64 where
  next i := i + 1
  measure xs i := xs.upper.toNat - i.toNat
  le_refl := by
    intro a
    exact UInt64.le_iff_toNat_le.mpr (Nat.le_refl a.toNat)
  lower_le_next := by
    intro xs i hlo hhi
    rw [UInt64.le_iff_toNat_le] at hlo ⊢
    rw [UInt64.toNat_add_one_of_lt hhi]
    omega
  measure_next_lt := by
    intro xs i hhi
    rw [UInt64.toNat_add_one_of_lt hhi]
    have hlt : i.toNat < xs.upper.toNat := UInt64.lt_iff_toNat_lt.mp hhi
    omega

@[always_inline, inline] instance instRcoNativeStepUSize : RcoNativeStep USize where
  next i := i + 1
  measure xs i := xs.upper.toNat - i.toNat
  le_refl := by
    intro a
    exact USize.le_iff_toNat_le.mpr (Nat.le_refl a.toNat)
  lower_le_next := by
    intro xs i hlo hhi
    rw [USize.le_iff_toNat_le] at hlo ⊢
    rw [USize.toNat_add_one_of_lt hhi]
    omega
  measure_next_lt := by
    intro xs i hhi
    rw [USize.toNat_add_one_of_lt hhi]
    have hlt : i.toNat < xs.upper.toNat := USize.lt_iff_toNat_lt.mp hhi
    omega

private theorem rcoNativeEntriesFrom_nat_ge (xs : Std.Rco Nat)
    (i : Nat) (hlo : xs.lower ≤ i) {a : {a : Nat // a ∈ xs}}
    (ha : a ∈ rcoNativeEntriesFrom xs i hlo) : i ≤ a.1 := by
  unfold rcoNativeEntriesFrom at ha
  split at ha
  · rename_i hhi
    simp only [List.mem_cons] at ha
    rcases ha with hhead | htail
    · subst hhead
      exact Nat.le_refl i
    · have hge := rcoNativeEntriesFrom_nat_ge xs (i + 1)
        (RcoNativeStep.lower_le_next hlo hhi) htail
      omega
  · rename_i hhi
    cases ha
termination_by xs.upper - i
decreasing_by omega

private theorem rcoNativeEntriesFrom_nat_nodup (xs : Std.Rco Nat)
    (i : Nat) (hlo : xs.lower ≤ i) :
    (rcoNativeEntriesFrom xs i hlo).Nodup := by
  unfold rcoNativeEntriesFrom
  split
  · rename_i hhi
    rw [List.nodup_cons]
    constructor
    · intro hmem
      have hge := rcoNativeEntriesFrom_nat_ge xs (i + 1)
        (RcoNativeStep.lower_le_next hlo hhi) hmem
      change i + 1 ≤ i at hge
      omega
    · exact rcoNativeEntriesFrom_nat_nodup xs (i + 1) (RcoNativeStep.lower_le_next hlo hhi)
  · exact List.nodup_nil
termination_by xs.upper - i
decreasing_by omega

private theorem rcoNativeEntries_nat_nodup (xs : Std.Rco Nat) :
    (rcoNativeEntries xs).Nodup :=
  rcoNativeEntriesFrom_nat_nodup xs xs.lower (RcoNativeStep.le_refl xs.lower)

private theorem rcoNativeEntriesFrom_nat_mem (xs : Std.Rco Nat)
    (i : Nat) (hlo : xs.lower ≤ i) {j : Nat}
    (hij : i ≤ j) (hjhi : j < xs.upper) :
    ⟨j, by exact ⟨Nat.le_trans hlo hij, hjhi⟩⟩ ∈ rcoNativeEntriesFrom xs i hlo := by
  unfold rcoNativeEntriesFrom
  split
  · rename_i hhi
    by_cases hji : j = i
    · subst hji
      simp
    · simp only [List.mem_cons]
      right
      exact rcoNativeEntriesFrom_nat_mem xs (i + 1)
        (RcoNativeStep.lower_le_next hlo hhi) (by omega) hjhi
  · rename_i hhi
    omega
termination_by xs.upper - i
decreasing_by omega

private theorem rcoNativeEntries_nat_mem {xs : Std.Rco Nat} {j : Nat} (hj : j ∈ xs) :
    ⟨j, hj⟩ ∈ rcoNativeEntries xs := by
  rw [Std.Rco.mem_iff] at hj
  simpa [rcoNativeEntries] using
    rcoNativeEntriesFrom_nat_mem xs xs.lower (RcoNativeStep.le_refl xs.lower) hj.1 hj.2

theorem rcoNativeEntriesFrom_nat_map_val (xs : Std.Rco Nat)
    (i : Nat) (hlo : xs.lower ≤ i) :
    (rcoNativeEntriesFrom xs i hlo).map Subtype.val = List.range' i (xs.upper - i) := by
  unfold rcoNativeEntriesFrom
  split
  · rename_i hhi
    change i :: (rcoNativeEntriesFrom xs (i + 1) (RcoNativeStep.lower_le_next hlo hhi)).map Subtype.val =
      List.range' i (xs.upper - i)
    rw [rcoNativeEntriesFrom_nat_map_val xs (i + 1) (RcoNativeStep.lower_le_next hlo hhi)]
    have hsub : xs.upper - i = (xs.upper - (i + 1)) + 1 := by omega
    rw [hsub]
    simp [List.range'_succ]
  · rename_i hhi
    have hsub : xs.upper - i = 0 := by omega
    simp [hsub]
termination_by xs.upper - i
decreasing_by omega

theorem rcoNativeEntries_nat_map_val (xs : Std.Rco Nat) :
    (rcoNativeEntries xs).map Subtype.val = List.range' xs.lower (xs.upper - xs.lower) := by
  exact rcoNativeEntriesFrom_nat_map_val xs xs.lower (RcoNativeStep.le_refl xs.lower)

theorem rcoNativeEntries_zero_nat_map_val (n : Nat) :
    (rcoNativeEntries (0...n : Std.Rco Nat)).map Subtype.val = List.range n := by
  rw [List.range_eq_range']
  simpa using rcoNativeEntries_nat_map_val (0...n : Std.Rco Nat)

private theorem rcoNativeEntriesFrom_int_ge (xs : Std.Rco Int)
    (i : Int) (hlo : xs.lower ≤ i) {a : {a : Int // a ∈ xs}}
    (ha : a ∈ rcoNativeEntriesFrom xs i hlo) : i ≤ a.1 := by
  unfold rcoNativeEntriesFrom at ha
  split at ha
  · rename_i hhi
    simp only [List.mem_cons] at ha
    rcases ha with hhead | htail
    · subst hhead
      exact Int.le_refl i
    · have hge := rcoNativeEntriesFrom_int_ge xs (i + 1)
        (RcoNativeStep.lower_le_next hlo hhi) htail
      omega
  · rename_i hhi
    cases ha
termination_by (xs.upper - i).toNat
decreasing_by omega

private theorem rcoNativeEntriesFrom_int_nodup (xs : Std.Rco Int)
    (i : Int) (hlo : xs.lower ≤ i) :
    (rcoNativeEntriesFrom xs i hlo).Nodup := by
  unfold rcoNativeEntriesFrom
  split
  · rename_i hhi
    rw [List.nodup_cons]
    constructor
    · intro hmem
      have hge := rcoNativeEntriesFrom_int_ge xs (i + 1)
        (RcoNativeStep.lower_le_next hlo hhi) hmem
      change i + 1 ≤ i at hge
      omega
    · exact rcoNativeEntriesFrom_int_nodup xs (i + 1) (RcoNativeStep.lower_le_next hlo hhi)
  · exact List.nodup_nil
termination_by (xs.upper - i).toNat
decreasing_by omega

private theorem rcoNativeEntries_int_nodup (xs : Std.Rco Int) :
    (rcoNativeEntries xs).Nodup :=
  rcoNativeEntriesFrom_int_nodup xs xs.lower (RcoNativeStep.le_refl xs.lower)

private theorem rcoNativeEntriesFrom_int_mem (xs : Std.Rco Int)
    (i : Int) (hlo : xs.lower ≤ i) {j : Int}
    (hij : i ≤ j) (hjhi : j < xs.upper) :
    ⟨j, by exact ⟨Int.le_trans hlo hij, hjhi⟩⟩ ∈ rcoNativeEntriesFrom xs i hlo := by
  unfold rcoNativeEntriesFrom
  split
  · rename_i hhi
    by_cases hji : j = i
    · subst hji
      simp
    · simp only [List.mem_cons]
      right
      exact rcoNativeEntriesFrom_int_mem xs (i + 1)
        (RcoNativeStep.lower_le_next hlo hhi) (by omega) hjhi
  · rename_i hhi
    omega
termination_by (xs.upper - i).toNat
decreasing_by omega

private theorem rcoNativeEntries_int_mem {xs : Std.Rco Int} {j : Int} (hj : j ∈ xs) :
    ⟨j, hj⟩ ∈ rcoNativeEntries xs := by
  rw [Std.Rco.mem_iff] at hj
  simpa [rcoNativeEntries] using
    rcoNativeEntriesFrom_int_mem xs xs.lower (RcoNativeStep.le_refl xs.lower) hj.1 hj.2

private theorem rcoNativeEntriesFrom_uint64_ge (xs : Std.Rco UInt64)
    (i : UInt64) (hlo : xs.lower ≤ i) {a : {a : UInt64 // a ∈ xs}}
    (ha : a ∈ rcoNativeEntriesFrom xs i hlo) : i.toNat ≤ a.1.toNat := by
  unfold rcoNativeEntriesFrom at ha
  split at ha
  · rename_i hhi
    simp only [List.mem_cons] at ha
    rcases ha with hhead | htail
    · subst hhead
      exact Nat.le_refl i.toNat
    · have hge := rcoNativeEntriesFrom_uint64_ge xs (i + 1)
        (RcoNativeStep.lower_le_next hlo hhi) htail
      have hnext := UInt64.toNat_add_one_of_lt hhi
      omega
  · rename_i hhi
    cases ha
termination_by xs.upper.toNat - i.toNat
decreasing_by
  have hlt := UInt64.lt_iff_toNat_lt.mp (by assumption)
  have hfit : i.toNat + 1 < 2 ^ 64 := by
    have hupper := UInt64.toNat_lt xs.upper
    omega
  change xs.upper.toNat - ((i.toNat + 1) % 2 ^ 64) < xs.upper.toNat - i.toNat
  rw [Nat.mod_eq_of_lt hfit]
  omega

private theorem rcoNativeEntriesFrom_uint64_nodup (xs : Std.Rco UInt64)
    (i : UInt64) (hlo : xs.lower ≤ i) :
    (rcoNativeEntriesFrom xs i hlo).Nodup := by
  unfold rcoNativeEntriesFrom
  split
  · rename_i hhi
    rw [List.nodup_cons]
    constructor
    · intro hmem
      have hge := rcoNativeEntriesFrom_uint64_ge xs (i + 1)
        (RcoNativeStep.lower_le_next hlo hhi) hmem
      have hnext := UInt64.toNat_add_one_of_lt hhi
      change (i + 1).toNat ≤ i.toNat at hge
      omega
    · exact rcoNativeEntriesFrom_uint64_nodup xs (i + 1) (RcoNativeStep.lower_le_next hlo hhi)
  · exact List.nodup_nil
termination_by xs.upper.toNat - i.toNat
decreasing_by
  rw [UInt64.toNat_add_one_of_lt (by assumption)]
  have hlt := UInt64.lt_iff_toNat_lt.mp (by assumption)
  omega

private theorem rcoNativeEntries_uint64_nodup (xs : Std.Rco UInt64) :
    (rcoNativeEntries xs).Nodup :=
  rcoNativeEntriesFrom_uint64_nodup xs xs.lower (RcoNativeStep.le_refl xs.lower)

private theorem rcoNativeEntriesFrom_uint64_mem (xs : Std.Rco UInt64)
    (i : UInt64) (hlo : xs.lower ≤ i) {j : UInt64}
    (hij : i ≤ j) (hjhi : j < xs.upper) :
    ⟨j, by exact ⟨UInt64.le_iff_toNat_le.mpr
      (Nat.le_trans (UInt64.le_iff_toNat_le.mp hlo) (UInt64.le_iff_toNat_le.mp hij)), hjhi⟩⟩ ∈
      rcoNativeEntriesFrom xs i hlo := by
  unfold rcoNativeEntriesFrom
  split
  · rename_i hhi
    by_cases hji : j = i
    · subst hji
      simp
    · simp only [List.mem_cons]
      right
      have hnext : i + 1 ≤ j := by
        rw [UInt64.le_iff_toNat_le]
        rw [UInt64.toNat_add_one_of_lt hhi]
        have hijNat := UInt64.le_iff_toNat_le.mp hij
        have hneNat : i.toNat ≠ j.toNat := by
          intro h
          apply hji
          exact UInt64.toNat_inj.mp h.symm
        omega
      exact rcoNativeEntriesFrom_uint64_mem xs (i + 1)
        (RcoNativeStep.lower_le_next hlo hhi) hnext hjhi
  · rename_i hhi
    exact False.elim (hhi (UInt64.lt_iff_toNat_lt.mpr
      (Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp hij) (UInt64.lt_iff_toNat_lt.mp hjhi))))
termination_by xs.upper.toNat - i.toNat
decreasing_by
  rw [UInt64.toNat_add_one_of_lt (by assumption)]
  have hlt := UInt64.lt_iff_toNat_lt.mp (by assumption)
  omega

private theorem rcoNativeEntries_uint64_mem {xs : Std.Rco UInt64} {j : UInt64} (hj : j ∈ xs) :
    ⟨j, hj⟩ ∈ rcoNativeEntries xs := by
  rw [Std.Rco.mem_iff] at hj
  simpa [rcoNativeEntries] using
    rcoNativeEntriesFrom_uint64_mem xs xs.lower (RcoNativeStep.le_refl xs.lower) hj.1 hj.2

instance instLawfulRcoNativeStepNat : LawfulRcoNativeStep Nat where
  mem_entries := rcoNativeEntries_nat_mem
  entries_nodup := rcoNativeEntries_nat_nodup

/-- Scalar finite indices are exactly the zero-origin native range `0...n`. -/
def finEquivZeroRange (n : Nat) : Fin n ≃ {i : Nat // i ∈ (0...n : Std.Rco Nat)} where
  toFun i := ⟨i.1, by
    rw [Std.Rco.mem_iff]
    exact ⟨Nat.zero_le i.1, i.2⟩⟩
  invFun i := ⟨i.1, by
    have hmem := i.2
    rw [Std.Rco.mem_iff] at hmem
    exact hmem.2⟩
  left_inv := by
    intro i
    apply Fin.ext
    rfl
  right_inv := by
    intro i
    apply Subtype.ext
    rfl

instance instLawfulRcoNativeStepInt : LawfulRcoNativeStep Int where
  mem_entries := rcoNativeEntries_int_mem
  entries_nodup := rcoNativeEntries_int_nodup

instance instLawfulRcoNativeStepUInt64 : LawfulRcoNativeStep UInt64 where
  mem_entries := rcoNativeEntries_uint64_mem
  entries_nodup := rcoNativeEntries_uint64_nodup

end NumLean
