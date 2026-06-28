module

public import NumLean.Meta.ForAll.Basic

@[expose] public section

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

/-- Lawful native stepping support for half-open ranges.

This refines `RcoNativeStep` without changing it.  The executable loop still only needs
`RcoNativeStep`; this class supplies the finite enumeration data needed for lawful
`ForAllSimple` instances. -/
class LawfulRcoNativeStep (α : Type u) [LE α] [LT α] [DecidableLT α]
    [RcoNativeStep α] where
  card : Std.Rco α → Nat
  entryEquiv : (xs : Std.Rco α) → Equiv (Fin (card xs)) ({a : α // a ∈ xs})
  entries_eq_finRange : ∀ xs,
    rcoNativeEntries xs = (List.finRange (card xs)).map (entryEquiv xs)

theorem mem_rcoNativeEntries {α : Type u} [LE α] [LT α] [DecidableLT α]
    [RcoNativeStep α] [LawfulRcoNativeStep α] {xs : Std.Rco α} {j : α} (hj : j ∈ xs) :
    ⟨j, hj⟩ ∈ rcoNativeEntries xs := by
  let e := LawfulRcoNativeStep.entryEquiv xs
  rw [LawfulRcoNativeStep.entries_eq_finRange]
  rw [List.mem_map]
  exact ⟨e.symm ⟨j, hj⟩, by simp only [List.mem_finRange], e.right_inv ⟨j, hj⟩⟩

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
    {β : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    [LawfulRcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α β inferInstance where
  entries := rcoNativeEntries
  mem_entries h := mem_rcoNativeEntries h
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNativeLoop_eq_foldl xs xs.lower (RcoNativeStep.le_refl xs.lower) init f

@[always_inline, inline, default_instance 100] instance instForAllIn'RcoNativeMProd2 {α : Type u}
    {β γ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    ForAllIn' (Std.Rco α) α (MProd β γ) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNativeMProd2Loop xs xs.lower (RcoNativeStep.le_refl xs.lower) init.fst init.snd f

@[always_inline, inline, default_instance 100] instance instLawfulForAllIn'RcoNativeMProd2 {α : Type u}
    {β γ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    [LawfulRcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α (MProd β γ) inferInstance where
  entries := rcoNativeEntries
  mem_entries h := mem_rcoNativeEntries h
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNativeMProd2Loop_eq_foldl xs xs.lower (RcoNativeStep.le_refl xs.lower)
      init.fst init.snd f

@[always_inline, inline, default_instance 200] instance instForAllIn'RcoNativeMProd3 {α : Type u}
    {β γ δ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    ForAllIn' (Std.Rco α) α (MProd β (MProd γ δ)) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNativeMProd3Loop xs xs.lower (RcoNativeStep.le_refl xs.lower) init.fst init.snd.fst init.snd.snd f

@[always_inline, inline, default_instance 200] instance instLawfulForAllIn'RcoNativeMProd3 {α : Type u}
    {β γ δ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    [LawfulRcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α (MProd β (MProd γ δ)) inferInstance where
  entries := rcoNativeEntries
  mem_entries h := mem_rcoNativeEntries h
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNativeMProd3Loop_eq_foldl xs xs.lower (RcoNativeStep.le_refl xs.lower)
      init.fst init.snd.fst init.snd.snd f

@[always_inline, inline, default_instance 300] instance instForAllIn'RcoNativeMProd4 {α : Type u}
    {β γ δ ε : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    ForAllIn' (Std.Rco α) α (MProd β (MProd γ (MProd δ ε))) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNativeMProd4Loop xs xs.lower (RcoNativeStep.le_refl xs.lower) init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd f

@[always_inline, inline, default_instance 300] instance instLawfulForAllIn'RcoNativeMProd4 {α : Type u}
    {β γ δ ε : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    [LawfulRcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α (MProd β (MProd γ (MProd δ ε))) inferInstance where
  entries := rcoNativeEntries
  mem_entries h := mem_rcoNativeEntries h
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNativeMProd4Loop_eq_foldl xs xs.lower (RcoNativeStep.le_refl xs.lower)
      init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd f

@[always_inline, inline, default_instance 400] instance instForAllIn'RcoNativeMProd5 {α : Type u}
    {β γ δ ε ζ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α] :
    ForAllIn' (Std.Rco α) α (MProd β (MProd γ (MProd δ (MProd ε ζ)))) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNativeMProd5Loop xs xs.lower (RcoNativeStep.le_refl xs.lower) init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd.fst init.snd.snd.snd.snd f

@[always_inline, inline, default_instance 400] instance instLawfulForAllIn'RcoNativeMProd5 {α : Type u}
    {β γ δ ε ζ : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    [LawfulRcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α (MProd β (MProd γ (MProd δ (MProd ε ζ)))) inferInstance where
  entries := rcoNativeEntries
  mem_entries h := mem_rcoNativeEntries h
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
    {β γ δ ε ζ η : Type v} [LE α] [LT α] [DecidableLT α] [RcoNativeStep α]
    [LawfulRcoNativeStep α] :
    LawfulForAllIn' (Std.Rco α) α (MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η))))) inferInstance where
  entries := rcoNativeEntries
  mem_entries h := mem_rcoNativeEntries h
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

theorem rcoNativeEntries_nat_nodup (xs : Std.Rco Nat) :
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
      exact rcoNativeEntriesFrom_nat_mem xs (i + 1) (RcoNativeStep.lower_le_next hlo hhi)
        (by omega) hjhi
  · rename_i hhi
    omega
termination_by xs.upper - i
decreasing_by omega

private theorem rcoNativeEntries_nat_mem {xs : Std.Rco Nat} {j : Nat} (hj : j ∈ xs) :
    ⟨j, hj⟩ ∈ rcoNativeEntries xs := by
  rw [Std.Rco.mem_iff] at hj
  simpa [rcoNativeEntries] using
    rcoNativeEntriesFrom_nat_mem xs xs.lower (RcoNativeStep.le_refl xs.lower) hj.1 hj.2

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

theorem rcoNativeEntries_int_nodup (xs : Std.Rco Int) :
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
      exact rcoNativeEntriesFrom_int_mem xs (i + 1) (RcoNativeStep.lower_le_next hlo hhi)
        (by omega) hjhi
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

theorem rcoNativeEntries_uint64_nodup (xs : Std.Rco UInt64) :
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

@[always_inline, inline] instance instLawfulRcoNativeStepNat : LawfulRcoNativeStep Nat where
  card xs := (rcoNativeEntries xs).length
  entryEquiv xs :=
    let entries := rcoNativeEntries xs
    let nd : entries.Nodup := rcoNativeEntries_nat_nodup xs
    { toFun := fun i => entries.get i
      invFun := fun a =>
        ⟨entries.idxOf a, by
          rw [List.idxOf_lt_length_iff]
          exact rcoNativeEntries_nat_mem a.2⟩
      left_inv := by
        intro i
        apply Fin.ext
        exact List.get_idxOf nd i
      right_inv := by
        intro a
        exact List.idxOf_get (List.idxOf_lt_length_iff.2 (rcoNativeEntries_nat_mem a.2)) }
  entries_eq_finRange := by
    classical
    intro xs
    let entries := rcoNativeEntries xs
    change entries = (List.finRange entries.length).map (fun i => entries.get i)
    simp [List.get_eq_getElem]

@[always_inline, inline] instance instLawfulRcoNativeStepInt : LawfulRcoNativeStep Int where
  card xs := (rcoNativeEntries xs).length
  entryEquiv xs :=
    let entries := rcoNativeEntries xs
    let nd : entries.Nodup := rcoNativeEntries_int_nodup xs
    { toFun := fun i => entries.get i
      invFun := fun a =>
        ⟨entries.idxOf a, by
          rw [List.idxOf_lt_length_iff]
          exact rcoNativeEntries_int_mem a.2⟩
      left_inv := by
        intro i
        apply Fin.ext
        exact List.get_idxOf nd i
      right_inv := by
        intro a
        exact List.idxOf_get (List.idxOf_lt_length_iff.2 (rcoNativeEntries_int_mem a.2)) }
  entries_eq_finRange := by
    classical
    intro xs
    let entries := rcoNativeEntries xs
    change entries = (List.finRange entries.length).map (fun i => entries.get i)
    simp [List.get_eq_getElem]

@[always_inline, inline] instance instLawfulRcoNativeStepUInt64 : LawfulRcoNativeStep UInt64 where
  card xs := (rcoNativeEntries xs).length
  entryEquiv xs :=
    let entries := rcoNativeEntries xs
    let nd : entries.Nodup := rcoNativeEntries_uint64_nodup xs
    { toFun := fun i => entries.get i
      invFun := fun a =>
        ⟨entries.idxOf a, by
          rw [List.idxOf_lt_length_iff]
          exact rcoNativeEntries_uint64_mem a.2⟩
      left_inv := by
        intro i
        apply Fin.ext
        exact List.get_idxOf nd i
      right_inv := by
        intro a
        exact List.idxOf_get (List.idxOf_lt_length_iff.2 (rcoNativeEntries_uint64_mem a.2)) }
  entries_eq_finRange := by
    classical
    intro xs
    let entries := rcoNativeEntries xs
    change entries = (List.finRange entries.length).map (fun i => entries.get i)
    simp [List.get_eq_getElem]

end Meta.ForAll
end NumLean
