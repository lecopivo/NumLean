import NumLean.Meta.ForAll.Basic

public section

namespace NumLean
namespace Meta.ForAll

/-- Concrete reference enumeration for half-open natural ranges, starting from `i`. -/
def rcoNatEntriesFrom (xs : Std.Rco Nat) (i : Nat) (hlo : xs.lower ≤ i) :
    List {j : Nat // j ∈ xs} :=
  if hhi : i < xs.upper then
    ⟨i, by exact ⟨hlo, hhi⟩⟩ ::
      rcoNatEntriesFrom xs (i + 1) (Nat.le_trans hlo (Nat.le_succ i))
  else
    []
termination_by xs.upper - i
decreasing_by omega

/-- Concrete reference enumeration for half-open natural ranges. -/
def rcoNatEntries (xs : Std.Rco Nat) : List {i : Nat // i ∈ xs} :=
  rcoNatEntriesFrom xs xs.lower (Nat.le_refl xs.lower)

theorem mem_rcoNatEntriesFrom {xs : Std.Rco Nat} {i j : Nat} (hlo : xs.lower ≤ i)
    (hij : i ≤ j) (hj : j ∈ xs) : ⟨j, hj⟩ ∈ rcoNatEntriesFrom xs i hlo := by
  unfold rcoNatEntriesFrom
  split
  · rename_i hhi
    by_cases hji : j = i
    · subst hji
      simp
    · have hne : i ≠ j := by intro h; exact hji h.symm
      have hij' : i + 1 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hij hne)
      have hnext : xs.lower ≤ i + 1 := Nat.le_trans hlo (Nat.le_succ i)
      exact List.mem_cons_of_mem _ (mem_rcoNatEntriesFrom hnext hij' hj)
  · rename_i hnhi
    have : ¬ j ∈ xs := by
      intro hmem
      exact hnhi (Nat.lt_of_le_of_lt hij hmem.2)
    exact False.elim (this hj)
termination_by xs.upper - i
decreasing_by omega

theorem mem_rcoNatEntries {xs : Std.Rco Nat} {j : Nat} (hj : j ∈ xs) :
    ⟨j, hj⟩ ∈ rcoNatEntries xs :=
  mem_rcoNatEntriesFrom (xs := xs) (i := xs.lower) (Nat.le_refl xs.lower) hj.1 hj

@[always_inline, inline, specialize] def forAllInRcoNatLoop {β : Type v} (xs : Std.Rco Nat)
    (i : Nat) (hlo : xs.lower ≤ i) (acc : β)
    (f : (a : Nat) → a ∈ xs → β → β) : β :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by
      exact ⟨hlo, hhi⟩
    forAllInRcoNatLoop xs (i + 1) (Nat.le_trans hlo (Nat.le_succ i)) (f i hmem acc) f
  else
    acc
termination_by xs.upper - i
decreasing_by omega

theorem forAllInRcoNatLoop_eq_foldl {β : Type v} (xs : Std.Rco Nat)
    (i : Nat) (hlo : xs.lower ≤ i) (acc : β)
    (f : (a : Nat) → a ∈ xs → β → β) :
    forAllInRcoNatLoop xs i hlo acc f =
      (rcoNatEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc) acc := by
  unfold forAllInRcoNatLoop rcoNatEntriesFrom
  split
  · exact forAllInRcoNatLoop_eq_foldl xs (i + 1)
      (Nat.le_trans hlo (Nat.le_succ i))
      (f i (by exact ⟨hlo, ‹i < xs.upper›⟩) acc) f
  · rfl
termination_by xs.upper - i
decreasing_by omega

@[always_inline, inline, specialize] def forAllInRcoNatMProd2Loop {β γ : Type v}
    (xs : Std.Rco Nat) (i : Nat) (hlo : xs.lower ≤ i) (b : β) (g : γ)
    (f : (a : Nat) → a ∈ xs → MProd β γ → MProd β γ) : MProd β γ :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    let ⟨b', g'⟩ := f i hmem (MProd.mk b g)
    forAllInRcoNatMProd2Loop xs (i + 1) (Nat.le_trans hlo (Nat.le_succ i)) b' g' f
  else
    MProd.mk b g
termination_by xs.upper - i
decreasing_by omega

@[always_inline, inline, specialize] def forAllInRcoNatMProd3Loop {β γ δ : Type v}
    (xs : Std.Rco Nat) (i : Nat) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ)
    (f : (a : Nat) → a ∈ xs → MProd β (MProd γ δ) → MProd β (MProd γ δ)) :
    MProd β (MProd γ δ) :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    let ⟨b', ⟨g', d'⟩⟩ := f i hmem (MProd.mk b (MProd.mk g d))
    forAllInRcoNatMProd3Loop xs (i + 1) (Nat.le_trans hlo (Nat.le_succ i)) b' g' d' f
  else
    MProd.mk b (MProd.mk g d)
termination_by xs.upper - i
decreasing_by omega

@[always_inline, inline, specialize] def forAllInRcoNatMProd4Loop {β γ δ ε : Type v}
    (xs : Std.Rco Nat) (i : Nat) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε)
    (f : (a : Nat) → a ∈ xs → MProd β (MProd γ (MProd δ ε)) →
      MProd β (MProd γ (MProd δ ε))) : MProd β (MProd γ (MProd δ ε)) :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    let ⟨b', ⟨g', ⟨d', e'⟩⟩⟩ := f i hmem (MProd.mk b (MProd.mk g (MProd.mk d e)))
    forAllInRcoNatMProd4Loop xs (i + 1) (Nat.le_trans hlo (Nat.le_succ i)) b' g' d' e' f
  else
    MProd.mk b (MProd.mk g (MProd.mk d e))
termination_by xs.upper - i
decreasing_by omega

@[always_inline, inline, specialize] def forAllInRcoNatMProd5Loop {β γ δ ε ζ : Type v}
    (xs : Std.Rco Nat) (i : Nat) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε) (z : ζ)
    (f : (a : Nat) → a ∈ xs → MProd β (MProd γ (MProd δ (MProd ε ζ))) →
      MProd β (MProd γ (MProd δ (MProd ε ζ)))) : MProd β (MProd γ (MProd δ (MProd ε ζ))) :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    let ⟨b', ⟨g', ⟨d', ⟨e', z'⟩⟩⟩⟩ := f i hmem (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e z))))
    forAllInRcoNatMProd5Loop xs (i + 1) (Nat.le_trans hlo (Nat.le_succ i)) b' g' d' e' z' f
  else
    MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e z)))
termination_by xs.upper - i
decreasing_by omega

@[always_inline, inline, specialize] def forAllInRcoNatMProd6Loop {β γ δ ε ζ η : Type v}
    (xs : Std.Rco Nat) (i : Nat) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε) (z : ζ) (n : η)
    (f : (a : Nat) → a ∈ xs → MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η)))) →
      MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η))))) : MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η)))) :=
  if hhi : i < xs.upper then
    let hmem : i ∈ xs := by exact ⟨hlo, hhi⟩
    let ⟨b', ⟨g', ⟨d', ⟨e', ⟨z', n'⟩⟩⟩⟩⟩ := f i hmem (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e (MProd.mk z n)))))
    forAllInRcoNatMProd6Loop xs (i + 1) (Nat.le_trans hlo (Nat.le_succ i)) b' g' d' e' z' n' f
  else
    MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e (MProd.mk z n))))
termination_by xs.upper - i
decreasing_by omega

theorem forAllInRcoNatMProd2Loop_eq_foldl {β γ : Type v} (xs : Std.Rco Nat)
    (i : Nat) (hlo : xs.lower ≤ i) (b : β) (g : γ)
    (f : (a : Nat) → a ∈ xs → MProd β γ → MProd β γ) :
    forAllInRcoNatMProd2Loop xs i hlo b g f =
      (rcoNatEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc) (MProd.mk b g) := by
  unfold forAllInRcoNatMProd2Loop rcoNatEntriesFrom
  split
  · rename_i hhi
    let next := f i (by exact ⟨hlo, hhi⟩) (MProd.mk b g)
    exact forAllInRcoNatMProd2Loop_eq_foldl xs (i + 1)
      (Nat.le_trans hlo (Nat.le_succ i)) next.fst next.snd f
  · rfl
termination_by xs.upper - i
decreasing_by omega

theorem forAllInRcoNatMProd3Loop_eq_foldl {β γ δ : Type v} (xs : Std.Rco Nat)
    (i : Nat) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ)
    (f : (a : Nat) → a ∈ xs → MProd β (MProd γ δ) → MProd β (MProd γ δ)) :
    forAllInRcoNatMProd3Loop xs i hlo b g d f =
      (rcoNatEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc)
        (MProd.mk b (MProd.mk g d)) := by
  unfold forAllInRcoNatMProd3Loop rcoNatEntriesFrom
  split
  · rename_i hhi
    let next := f i (by exact ⟨hlo, hhi⟩) (MProd.mk b (MProd.mk g d))
    exact forAllInRcoNatMProd3Loop_eq_foldl xs (i + 1)
      (Nat.le_trans hlo (Nat.le_succ i)) next.fst next.snd.fst next.snd.snd f
  · rfl
termination_by xs.upper - i
decreasing_by omega

theorem forAllInRcoNatMProd4Loop_eq_foldl {β γ δ ε : Type v} (xs : Std.Rco Nat)
    (i : Nat) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε)
    (f : (a : Nat) → a ∈ xs → MProd β (MProd γ (MProd δ ε)) →
      MProd β (MProd γ (MProd δ ε))) :
    forAllInRcoNatMProd4Loop xs i hlo b g d e f =
      (rcoNatEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc)
        (MProd.mk b (MProd.mk g (MProd.mk d e))) := by
  unfold forAllInRcoNatMProd4Loop rcoNatEntriesFrom
  split
  · rename_i hhi
    let next := f i (by exact ⟨hlo, hhi⟩) (MProd.mk b (MProd.mk g (MProd.mk d e)))
    exact forAllInRcoNatMProd4Loop_eq_foldl xs (i + 1)
      (Nat.le_trans hlo (Nat.le_succ i)) next.fst next.snd.fst next.snd.snd.fst
      next.snd.snd.snd f
  · rfl
termination_by xs.upper - i
decreasing_by omega

theorem forAllInRcoNatMProd5Loop_eq_foldl {β γ δ ε ζ : Type v} (xs : Std.Rco Nat)
    (i : Nat) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε) (z : ζ)
    (f : (a : Nat) → a ∈ xs → MProd β (MProd γ (MProd δ (MProd ε ζ))) →
      MProd β (MProd γ (MProd δ (MProd ε ζ)))) :
    forAllInRcoNatMProd5Loop xs i hlo b g d e z f =
      (rcoNatEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc)
        (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e z)))) := by
  unfold forAllInRcoNatMProd5Loop rcoNatEntriesFrom
  split
  · rename_i hhi
    let next := f i (by exact ⟨hlo, hhi⟩)
      (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e z))))
    exact forAllInRcoNatMProd5Loop_eq_foldl xs (i + 1)
      (Nat.le_trans hlo (Nat.le_succ i)) next.fst next.snd.fst next.snd.snd.fst
      next.snd.snd.snd.fst next.snd.snd.snd.snd f
  · rfl
termination_by xs.upper - i
decreasing_by omega

theorem forAllInRcoNatMProd6Loop_eq_foldl {β γ δ ε ζ η : Type v} (xs : Std.Rco Nat)
    (i : Nat) (hlo : xs.lower ≤ i) (b : β) (g : γ) (d : δ) (e : ε) (z : ζ) (n : η)
    (f : (a : Nat) → a ∈ xs → MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η)))) →
      MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η))))) :
    forAllInRcoNatMProd6Loop xs i hlo b g d e z n f =
      (rcoNatEntriesFrom xs i hlo).foldl (fun acc a => f a.1 a.2 acc)
        (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e (MProd.mk z n))))) := by
  unfold forAllInRcoNatMProd6Loop rcoNatEntriesFrom
  split
  · rename_i hhi
    let next := f i (by exact ⟨hlo, hhi⟩)
      (MProd.mk b (MProd.mk g (MProd.mk d (MProd.mk e (MProd.mk z n)))))
    exact forAllInRcoNatMProd6Loop_eq_foldl xs (i + 1)
      (Nat.le_trans hlo (Nat.le_succ i)) next.fst next.snd.fst next.snd.snd.fst
      next.snd.snd.snd.fst next.snd.snd.snd.snd.fst next.snd.snd.snd.snd.snd f
  · rfl
termination_by xs.upper - i
decreasing_by omega

@[always_inline, inline, default_instance low] instance instForAllIn'RcoNat {β : Type v} :
    ForAllIn' (Std.Rco Nat) Nat β inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatLoop xs xs.lower (Nat.le_refl xs.lower) init f

@[always_inline, inline, default_instance low] instance instLawfulForAllIn'RcoNat {β : Type v} :
    LawfulForAllIn' (Std.Rco Nat) Nat β inferInstance where
  entries := rcoNatEntries
  mem_entries h := mem_rcoNatEntries h
  forAllIn'_eq_foldl xs init f := by
    exact forAllInRcoNatLoop_eq_foldl xs xs.lower (Nat.le_refl xs.lower) init f

@[always_inline, inline, default_instance 100] instance instForAllIn'RcoNatMProd2 {β γ : Type v} :
    ForAllIn' (Std.Rco Nat) Nat (MProd β γ) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatMProd2Loop xs xs.lower (Nat.le_refl xs.lower) init.fst init.snd f

@[always_inline, inline, default_instance 100] instance instLawfulForAllIn'RcoNatMProd2 {β γ : Type v} :
    LawfulForAllIn' (Std.Rco Nat) Nat (MProd β γ) inferInstance where
  entries := rcoNatEntries
  mem_entries h := mem_rcoNatEntries h
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNatMProd2Loop_eq_foldl xs xs.lower (Nat.le_refl xs.lower) init.fst init.snd f

@[always_inline, inline, default_instance 200] instance instForAllIn'RcoNatMProd3 {β γ δ : Type v} :
    ForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ δ)) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatMProd3Loop xs xs.lower (Nat.le_refl xs.lower) init.fst init.snd.fst init.snd.snd f

@[always_inline, inline, default_instance 200] instance instLawfulForAllIn'RcoNatMProd3 {β γ δ : Type v} :
    LawfulForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ δ)) inferInstance where
  entries := rcoNatEntries
  mem_entries h := mem_rcoNatEntries h
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNatMProd3Loop_eq_foldl xs xs.lower (Nat.le_refl xs.lower)
      init.fst init.snd.fst init.snd.snd f

@[always_inline, inline, default_instance 300] instance instForAllIn'RcoNatMProd4 {β γ δ ε : Type v} :
    ForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ (MProd δ ε))) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatMProd4Loop xs xs.lower (Nat.le_refl xs.lower) init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd f

@[always_inline, inline, default_instance 300] instance instLawfulForAllIn'RcoNatMProd4 {β γ δ ε : Type v} :
    LawfulForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ (MProd δ ε))) inferInstance where
  entries := rcoNatEntries
  mem_entries h := mem_rcoNatEntries h
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNatMProd4Loop_eq_foldl xs xs.lower (Nat.le_refl xs.lower)
      init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd f

@[always_inline, inline, default_instance 400] instance instForAllIn'RcoNatMProd5 {β γ δ ε ζ : Type v} :
    ForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ (MProd δ (MProd ε ζ)))) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatMProd5Loop xs xs.lower (Nat.le_refl xs.lower) init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd.fst init.snd.snd.snd.snd f

@[always_inline, inline, default_instance 400] instance instLawfulForAllIn'RcoNatMProd5 {β γ δ ε ζ : Type v} :
    LawfulForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ (MProd δ (MProd ε ζ)))) inferInstance where
  entries := rcoNatEntries
  mem_entries h := mem_rcoNatEntries h
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNatMProd5Loop_eq_foldl xs xs.lower (Nat.le_refl xs.lower)
      init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd.fst
      init.snd.snd.snd.snd f

@[always_inline, inline, default_instance 500] instance instForAllIn'RcoNatMProd6 {β γ δ ε ζ η : Type v} :
    ForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η))))) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatMProd6Loop xs xs.lower (Nat.le_refl xs.lower) init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd.fst init.snd.snd.snd.snd.fst init.snd.snd.snd.snd.snd f

@[always_inline, inline, default_instance 500] instance instLawfulForAllIn'RcoNatMProd6 {β γ δ ε ζ η : Type v} :
    LawfulForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η))))) inferInstance where
  entries := rcoNatEntries
  mem_entries h := mem_rcoNatEntries h
  forAllIn'_eq_foldl xs init f :=
    forAllInRcoNatMProd6Loop_eq_foldl xs xs.lower (Nat.le_refl xs.lower)
      init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd.fst
      init.snd.snd.snd.snd.fst init.snd.snd.snd.snd.snd f

end Meta.ForAll
end NumLean
