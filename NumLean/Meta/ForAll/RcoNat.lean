import NumLean.Meta.ForAll.Basic

public section

namespace NumLean
namespace Meta.ForAll

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

@[always_inline, inline, default_instance low] instance instForAllIn'RcoNat {β : Type v} :
    ForAllIn' (Std.Rco Nat) Nat β inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatLoop xs xs.lower (Nat.le_refl xs.lower) init f

@[always_inline, inline, default_instance 100] instance instForAllIn'RcoNatMProd2 {β γ : Type v} :
    ForAllIn' (Std.Rco Nat) Nat (MProd β γ) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatMProd2Loop xs xs.lower (Nat.le_refl xs.lower) init.fst init.snd f

@[always_inline, inline, default_instance 200] instance instForAllIn'RcoNatMProd3 {β γ δ : Type v} :
    ForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ δ)) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatMProd3Loop xs xs.lower (Nat.le_refl xs.lower) init.fst init.snd.fst init.snd.snd f

@[always_inline, inline, default_instance 300] instance instForAllIn'RcoNatMProd4 {β γ δ ε : Type v} :
    ForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ (MProd δ ε))) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatMProd4Loop xs xs.lower (Nat.le_refl xs.lower) init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd f

@[always_inline, inline, default_instance 400] instance instForAllIn'RcoNatMProd5 {β γ δ ε ζ : Type v} :
    ForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ (MProd δ (MProd ε ζ)))) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatMProd5Loop xs xs.lower (Nat.le_refl xs.lower) init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd.fst init.snd.snd.snd.snd f

@[always_inline, inline, default_instance 500] instance instForAllIn'RcoNatMProd6 {β γ δ ε ζ η : Type v} :
    ForAllIn' (Std.Rco Nat) Nat (MProd β (MProd γ (MProd δ (MProd ε (MProd ζ η))))) inferInstance where
  forAllIn' xs init f :=
    forAllInRcoNatMProd6Loop xs xs.lower (Nat.le_refl xs.lower) init.fst init.snd.fst init.snd.snd.fst init.snd.snd.snd.fst init.snd.snd.snd.snd.fst init.snd.snd.snd.snd.snd f

end Meta.ForAll
end NumLean
