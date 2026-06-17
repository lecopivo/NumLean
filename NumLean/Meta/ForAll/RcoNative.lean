import NumLean.Meta.ForAll.Basic

public section

namespace NumLean
namespace Meta.ForAll

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

@[always_inline, inline, specialize] def forAllInRcoNativeLoop {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (acc : β)
    (f : (a : α) → a ∈ xs → β → β) : β :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    forAllInRcoNativeLoop xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) (f i hmem acc) f
  else
    acc
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

theorem forAllInRcoNativeLoop_eq_foldl {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (acc : β)
    (f : (a : α) → a ∈ xs → β → β) :
    forAllInRcoNativeLoop xs i hlo acc f =
      (rcoNativeEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc) acc := by
  unfold forAllInRcoNativeLoop rcoNativeEntriesFrom
  split
  · rename_i hhi
    exact forAllInRcoNativeLoop_eq_foldl xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) (f i (by exact ⟨hlo, hhi⟩) acc) f
  · rfl
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

@[always_inline, inline, specialize] def forAllInRcoNativeMProd2Loop {α : Type u}
    {β γ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (b : β) (g : γ)
    (f : (a : α) → a ∈ xs → MProd β γ → MProd β γ) : MProd β γ :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    let ⟨b', g'⟩ := f i hmem (MProd.mk b g)
    forAllInRcoNativeMProd2Loop xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) b' g' f
  else
    MProd.mk b g
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

@[always_inline, inline, specialize] def forAllInRcoNativeMProd3Loop {α : Type u}
    {β γ δ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ)
    (f : (a : α) → a ∈ xs → MProd β (MProd γ δ) → MProd β (MProd γ δ)) :
    MProd β (MProd γ δ) :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    let ⟨b', ⟨g', d'⟩⟩ := f i hmem (MProd.mk b (MProd.mk g d))
    forAllInRcoNativeMProd3Loop xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) b' g' d' f
  else
    MProd.mk b (MProd.mk g d)
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

@[always_inline, inline, specialize] def forAllInRcoNativeMProd4Loop {α : Type u}
    {β γ δ ε : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε)
    (f : (a : α) → a ∈ xs → MProd β (MProd γ (MProd δ ε)) →
      MProd β (MProd γ (MProd δ ε))) : MProd β (MProd γ (MProd δ ε)) :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    let ⟨b', ⟨g', ⟨d', e'⟩⟩⟩ := f i hmem (MProd.mk b (MProd.mk g (MProd.mk d e)))
    forAllInRcoNativeMProd4Loop xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) b' g' d' e' f
  else
    MProd.mk b (MProd.mk g (MProd.mk d e))
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

@[always_inline, inline, specialize] def forAllInRcoNativeMProd5Loop {α : Type u}
    {β γ δ ε ζ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε) (z : ζ)
    (f : (a : α) → a ∈ xs → MProd β (MProd γ (MProd δ (MProd ε ζ))) →
      MProd β (MProd γ (MProd δ (MProd ε ζ)))) : MProd β (MProd γ (MProd δ (MProd ε ζ))) :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    let ⟨b', ⟨g', ⟨d', ⟨e', z'⟩⟩⟩⟩ :=
      f i hmem (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e z))))
    forAllInRcoNativeMProd5Loop xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) b' g' d' e' z' f
  else
    MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e z)))
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

@[always_inline, inline, specialize] def forAllInRcoNativeMProd6Loop {α : Type u}
    {β γ δ ε ζ η : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε) (z : ζ) (n : η)
    (f : (a : α) → a ∈ xs → MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η)))) →
      MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η))))) :
      MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η)))) :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    let ⟨b', ⟨g', ⟨d', ⟨e', ⟨z', n'⟩⟩⟩⟩⟩ :=
      f i hmem (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e (MProd.mk z n)))))
    forAllInRcoNativeMProd6Loop xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) b' g' d' e' z' n' f
  else
    MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e (MProd.mk z n))))
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

theorem forAllInRcoNativeMProd2Loop_eq_foldl {α : Type u} {β γ : Type v}
    [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (b : β) (g : γ)
    (f : (a : α) → a ∈ xs → MProd β γ → MProd β γ) :
    forAllInRcoNativeMProd2Loop xs i hlo b g f =
      (rcoNativeEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc) (MProd.mk b g) := by
  unfold forAllInRcoNativeMProd2Loop rcoNativeEntriesFrom
  split
  · rename_i hhi
    let next := f i (by exact ⟨hlo, hhi⟩) (MProd.mk b g)
    exact forAllInRcoNativeMProd2Loop_eq_foldl xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) next.fst next.snd f
  · rfl
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

theorem forAllInRcoNativeMProd3Loop_eq_foldl {α : Type u} {β γ δ : Type v}
    [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ)
    (f : (a : α) → a ∈ xs → MProd β (MProd γ δ) → MProd β (MProd γ δ)) :
    forAllInRcoNativeMProd3Loop xs i hlo b g d f =
      (rcoNativeEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc)
        (MProd.mk b (MProd.mk g d)) := by
  unfold forAllInRcoNativeMProd3Loop rcoNativeEntriesFrom
  split
  · rename_i hhi
    let next := f i (by exact ⟨hlo, hhi⟩) (MProd.mk b (MProd.mk g d))
    exact forAllInRcoNativeMProd3Loop_eq_foldl xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) next.fst next.snd.fst next.snd.snd f
  · rfl
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

theorem forAllInRcoNativeMProd4Loop_eq_foldl {α : Type u} {β γ δ ε : Type v}
    [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε)
    (f : (a : α) → a ∈ xs → MProd β (MProd γ (MProd δ ε)) →
      MProd β (MProd γ (MProd δ ε))) :
    forAllInRcoNativeMProd4Loop xs i hlo b g d e f =
      (rcoNativeEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc)
        (MProd.mk b (MProd.mk g (MProd.mk d e))) := by
  unfold forAllInRcoNativeMProd4Loop rcoNativeEntriesFrom
  split
  · rename_i hhi
    let next := f i (by exact ⟨hlo, hhi⟩) (MProd.mk b (MProd.mk g (MProd.mk d e)))
    exact forAllInRcoNativeMProd4Loop_eq_foldl xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) next.fst next.snd.fst next.snd.snd.fst
      next.snd.snd.snd f
  · rfl
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

theorem forAllInRcoNativeMProd5Loop_eq_foldl {α : Type u} {β γ δ ε ζ : Type v}
    [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε) (z : ζ)
    (f : (a : α) → a ∈ xs → MProd β (MProd γ (MProd δ (MProd ε ζ))) →
      MProd β (MProd γ (MProd δ (MProd ε ζ)))) :
    forAllInRcoNativeMProd5Loop xs i hlo b g d e z f =
      (rcoNativeEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc)
        (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e z)))) := by
  unfold forAllInRcoNativeMProd5Loop rcoNativeEntriesFrom
  split
  · rename_i hhi
    let next := f i (by exact ⟨hlo, hhi⟩)
      (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e z))))
    exact forAllInRcoNativeMProd5Loop_eq_foldl xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) next.fst next.snd.fst next.snd.snd.fst
      next.snd.snd.snd.fst next.snd.snd.snd.snd f
  · rfl
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

theorem forAllInRcoNativeMProd6Loop_eq_foldl {α : Type u} {β γ δ ε ζ η : Type v}
    [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    (xs : Std.Rco α) (i : α) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε) (z : ζ) (n : η)
    (f : (a : α) → a ∈ xs → MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η)))) →
      MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η))))) :
    forAllInRcoNativeMProd6Loop xs i hlo b g d e z n f =
      (rcoNativeEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc)
        (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e (MProd.mk z n))))) := by
  unfold forAllInRcoNativeMProd6Loop rcoNativeEntriesFrom
  split
  · rename_i hhi
    let next := f i (by exact ⟨hlo, hhi⟩)
      (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e (MProd.mk z n)))))
    exact forAllInRcoNativeMProd6Loop_eq_foldl xs (RcoNativeStep.next i)
      (RcoNativeStep.lower_le_next hlo hhi) next.fst next.snd.fst next.snd.snd.fst
      next.snd.snd.snd.fst next.snd.snd.snd.snd.fst next.snd.snd.snd.snd.snd f
  · rfl
termination_by RcoNativeStep.measure xs i
decreasing_by exact RcoNativeStep.measure_next_lt (by assumption)

@[always_inline, inline, default_instance low] instance instForAllIn'RcoNative {α : Type u}
    {β : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    ForAllIn' (Std.Rco α) α β inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNativeLoop xs xs.lower (RcoNativeStep.le_refl xs.lower) init f

@[always_inline, inline, default_instance low] instance instLawfulForAllIn'RcoNative {α : Type u}
    {β : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α β inferInstance where
  entries := rcoNativeEntries
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNativeLoop_eq_foldl xs xs.lower (RcoNativeStep.le_refl xs.lower) init f

@[always_inline, inline, default_instance 100] instance instForAllIn'RcoNativeMProd2 {α : Type u}
    {β γ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    ForAllIn' (Std.Rco α) α (MProd β γ) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNativeMProd2Loop xs xs.lower (RcoNativeStep.le_refl xs.lower) init.fst init.snd f

@[always_inline, inline, default_instance 100] instance instLawfulForAllIn'RcoNativeMProd2 {α : Type u}
    {β γ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α (MProd β γ) inferInstance where
  entries := rcoNativeEntries
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNativeMProd2Loop_eq_foldl xs xs.lower (RcoNativeStep.le_refl xs.lower)
      init.fst init.snd f

@[always_inline, inline, default_instance 200] instance instForAllIn'RcoNativeMProd3 {α : Type u}
    {β γ δ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    ForAllIn' (Std.Rco α) α (MProd β (MProd γ δ)) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNativeMProd3Loop xs xs.lower (RcoNativeStep.le_refl xs.lower) init.fst init.snd.fst init.snd.snd f

@[always_inline, inline, default_instance 200] instance instLawfulForAllIn'RcoNativeMProd3 {α : Type u}
    {β γ δ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α (MProd β (MProd γ δ)) inferInstance where
  entries := rcoNativeEntries
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNativeMProd3Loop_eq_foldl xs xs.lower (RcoNativeStep.le_refl xs.lower)
      init.fst init.snd.fst init.snd.snd f

@[always_inline, inline, default_instance 300] instance instForAllIn'RcoNativeMProd4 {α : Type u}
    {β γ δ ε : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    ForAllIn' (Std.Rco α) α (MProd β (MProd γ (MProd δ ε))) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNativeMProd4Loop xs xs.lower (RcoNativeStep.le_refl xs.lower) init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd f

@[always_inline, inline, default_instance 300] instance instLawfulForAllIn'RcoNativeMProd4 {α : Type u}
    {β γ δ ε : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α (MProd β (MProd γ (MProd δ ε))) inferInstance where
  entries := rcoNativeEntries
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNativeMProd4Loop_eq_foldl xs xs.lower (RcoNativeStep.le_refl xs.lower)
      init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd f

@[always_inline, inline, default_instance 400] instance instForAllIn'RcoNativeMProd5 {α : Type u}
    {β γ δ ε ζ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    ForAllIn' (Std.Rco α) α (MProd β (MProd γ (MProd δ (MProd ε ζ)))) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNativeMProd5Loop xs xs.lower (RcoNativeStep.le_refl xs.lower) init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd.fst init.snd.snd.snd.snd f

@[always_inline, inline, default_instance 400] instance instLawfulForAllIn'RcoNativeMProd5 {α : Type u}
    {β γ δ ε ζ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α (MProd β (MProd γ (MProd δ (MProd ε ζ)))) inferInstance where
  entries := rcoNativeEntries
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNativeMProd5Loop_eq_foldl xs xs.lower (RcoNativeStep.le_refl xs.lower)
      init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd.fst
      init.snd.snd.snd.snd f

@[always_inline, inline, default_instance 500] instance instForAllIn'RcoNativeMProd6 {α : Type u}
    {β γ δ ε ζ η : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    ForAllIn' (Std.Rco α) α (MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η))))) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNativeMProd6Loop xs xs.lower (RcoNativeStep.le_refl xs.lower) init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd.fst init.snd.snd.snd.snd.fst init.snd.snd.snd.snd.snd f

@[always_inline, inline, default_instance 500] instance instLawfulForAllIn'RcoNativeMProd6 {α : Type u}
    {β γ δ ε ζ η : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α (MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η))))) inferInstance where
  entries := rcoNativeEntries
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNativeMProd6Loop_eq_foldl xs xs.lower (RcoNativeStep.le_refl xs.lower)
      init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd.fst
      init.snd.snd.snd.snd.fst init.snd.snd.snd.snd.snd f

theorem UInt64.toNat_add_one_of_lt {i upper : UInt64} (h : i < upper) :
    (i + 1).toNat = i.toNat + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat]
  have hiu : i.toNat < upper.toNat := UInt64.lt_iff_toNat_lt.mp h
  have hup : upper.toNat < 2 ^ 64 := UInt64.toNat_lt upper
  have hs : i.toNat + 1 < 2 ^ 64 := by omega
  have hone : 1 % 2 ^ 64 = 1 := by omega
  rw [hone]
  exact Nat.mod_eq_of_lt hs

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

end Meta.ForAll
end NumLean
