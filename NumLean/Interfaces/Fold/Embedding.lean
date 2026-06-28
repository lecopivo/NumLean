module

public import NumLean.Interfaces.Fold.RangeIso

@[expose] public section

public section

namespace NumLean

namespace Fold

/-- An injective map from one folded range into another, equipped with a decidable guard and a
guarded inverse on the target range.

This is intended for padded/extended iteration domains: entries satisfying `guard` correspond to
source entries, while entries failing `guard` are extra target entries that should take a neutral
branch in a guarded fold. -/
structure RangeEmbedding {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    (xs : ρ) (ys : σ) where
  toFun : {a : α // a ∈ xs} → {b : β // b ∈ ys}
  guard : (b : β) → b ∈ ys → Prop
  guard_decidable : ∀ b hb, Decidable (guard b hb)
  guard_toFun : ∀ a, guard (toFun a).1 (toFun a).2
  invFun : (b : β) → (hb : b ∈ ys) → guard b hb → {a : α // a ∈ xs}
  right_inv : ∀ b hb h, toFun (invFun b hb h) = ⟨b, hb⟩
  left_inv : ∀ a, invFun (toFun a).1 (toFun a).2 (guard_toFun a) = a

namespace RangeEmbedding

instance {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : RangeEmbedding xs ys) (b : β) (hb : b ∈ ys) :
    Decidable (e.guard b hb) :=
  e.guard_decidable b hb

/-- Every range embeds into itself with guard always true. -/
def refl {ρ : Type u} {α : Type v}
    {d : Membership α ρ} [FoldEntries ρ α d] [Fold ρ] [LawfulFold ρ α d]
    (xs : ρ) : RangeEmbedding xs xs where
  toFun := id
  guard := fun _ _ => True
  guard_decidable := fun _ _ => inferInstance
  guard_toFun := fun _ => trivial
  invFun := fun b hb _ => ⟨b, hb⟩
  right_inv := by
    intro b hb h
    rfl
  left_inv := by
    intro a
    rfl

/-- Ordered range isomorphisms are range embeddings with guard always true. -/
def ofRangeIso {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : RangeIso xs ys) : RangeEmbedding xs ys where
  toFun := e.toEquiv
  guard := fun _ _ => True
  guard_decidable := fun _ _ => inferInstance
  guard_toFun := fun _ => trivial
  invFun := fun b hb _ => e.toEquiv.symm ⟨b, hb⟩
  right_inv := by
    intro b hb h
    exact e.toEquiv.apply_symm_apply ⟨b, hb⟩
  left_inv := by
    intro a
    exact e.toEquiv.symm_apply_apply a

theorem toFun_injective {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : RangeEmbedding xs ys) :
    Function.Injective e.toFun := by
  intro a b h
  have ha := e.left_inv a
  have hb := e.left_inv b
  rw [← ha, ← hb]
  congr

/-- Composition of guarded range embeddings.

The composed guard is positive: a target entry is valid when it passes the outer guard and its
outer preimage passes the inner guard. -/
def trans {ρ : Type u} {σ : Type v} {τ : Type w} {α : Type x} {β : Type y} {γ : Type z}
    {dρ : Membership α ρ} {dσ : Membership β σ} {dτ : Membership γ τ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [FoldEntries τ γ dτ]
    [Fold ρ] [Fold σ] [Fold τ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ] [LawfulFold τ γ dτ]
    {xs : ρ} {ys : σ} {zs : τ}
    (e : RangeEmbedding xs ys) (f : RangeEmbedding ys zs) : RangeEmbedding xs zs where
  toFun a := f.toFun (e.toFun a)
  guard c hc :=
    if hfc : f.guard c hc then
      e.guard (f.invFun c hc hfc).1 (f.invFun c hc hfc).2
    else
      False
  guard_decidable c hc := by
    by_cases hfc : f.guard c hc
    · exact decidable_of_iff (e.guard (f.invFun c hc hfc).1 (f.invFun c hc hfc).2)
        (by simp [hfc])
    · exact isFalse (by simp [hfc])
  guard_toFun a := by
    have hf := f.guard_toFun (e.toFun a)
    simp [hf]
    have hleft := f.left_inv (e.toFun a)
    simpa [hleft] using e.guard_toFun a
  invFun c hc h := by
    by_cases hfc : f.guard c hc
    · exact e.invFun (f.invFun c hc hfc).1 (f.invFun c hc hfc).2 (by simpa [hfc] using h)
    · simp [hfc] at h
  right_inv := by
    intro c hc h
    by_cases hfc : f.guard c hc
    · simp [hfc]
      have heq := e.right_inv (f.invFun c hc hfc).1 (f.invFun c hc hfc).2 (by simpa [hfc] using h)
      rw [heq]
      exact f.right_inv c hc hfc
    · simp [hfc] at h
  left_inv := by
    intro a
    have hf := f.guard_toFun (e.toFun a)
    simp [hf]
    have hleft := f.left_inv (e.toFun a)
    simpa [hleft] using e.left_inv a

end RangeEmbedding

/-- A guarded range embedding whose guarded target entries appear in the same order as the source
entries.

This is the ordered form needed for fold transport without commutativity: target entries failing
`guard` are neutral, and target entries satisfying `guard` enumerate the source entries in order via
`invFun`. -/
structure RangeMonoEmbedding {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    (xs : ρ) (ys : σ) extends RangeEmbedding xs ys where
  entries_filterMap_invFun_eq :
    (LawfulFold.entries (ρ := σ) (α := β) ys).filterMap
        (fun b =>
          if h : guard b.1 b.2 then
            some (invFun b.1 b.2 h)
          else
            none) =
      LawfulFold.entries (ρ := ρ) (α := α) xs

namespace RangeMonoEmbedding

private theorem foldl_guarded_eq_filterMap {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {γ : Type y} {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : RangeMonoEmbedding xs ys)
    (entries : List {b : β // b ∈ ys}) (init : γ)
    (f : (a : α) → a ∈ xs → γ → γ) :
    entries.foldl
        (fun acc b =>
          if h : e.guard b.1 b.2 then
            f (e.invFun b.1 b.2 h).1 (e.invFun b.1 b.2 h).2 acc
          else
            acc) init =
      (entries.filterMap fun b =>
          if h : e.guard b.1 b.2 then
            some (e.invFun b.1 b.2 h)
          else
            none).foldl (fun acc a => f a.1 a.2 acc) init := by
  induction entries generalizing init with
  | nil => rfl
  | cons b entries ih =>
      simp only [List.foldl_cons]
      by_cases h : e.guard b.1 b.2
      · simp [h, ih]
      · simp [h, ih]

/-- Every range is an ordered guarded embedding into itself. -/
def refl {ρ : Type u} {α : Type v}
    {d : Membership α ρ} [FoldEntries ρ α d] [Fold ρ] [LawfulFold ρ α d]
    (xs : ρ) : RangeMonoEmbedding xs xs where
  toRangeEmbedding := RangeEmbedding.refl xs
  entries_filterMap_invFun_eq := by
    simp [RangeEmbedding.refl]

/-- Ordered range isomorphisms are ordered guarded embeddings with guard always true. -/
def ofRangeIso {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : RangeIso xs ys) : RangeMonoEmbedding xs ys where
  toRangeEmbedding := RangeEmbedding.ofRangeIso e
  entries_filterMap_invFun_eq := by
    rw [e.entries_eq]
    simp [RangeEmbedding.ofRangeIso]

/-- Transport a fold across an ordered guarded embedding. Target entries outside the embedded image
take the neutral branch. No commutativity hypothesis is needed because the guarded target entries
are source entries in order. -/
theorem fold_eq_guarded {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {γ : Type y} {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : RangeMonoEmbedding xs ys) (init : γ)
    (f : (a : α) → a ∈ xs → γ → γ) :
    Fold.fold xs init f =
      Fold.fold ys init fun b hb acc =>
        if h : e.guard b hb then
          f (e.invFun b hb h).1 (e.invFun b hb h).2 acc
        else
          acc := by
  rw [LawfulFold.fold_eq_foldl (xs := xs) (init := init) (f := f)]
  rw [LawfulFold.fold_eq_foldl (xs := ys) (init := init)
    (f := fun b hb acc =>
      if h : e.guard b hb then
        f (e.invFun b hb h).1 (e.invFun b hb h).2 acc
      else
        acc)]
  rw [foldl_guarded_eq_filterMap e]
  rw [e.entries_filterMap_invFun_eq]

end RangeMonoEmbedding

end Fold

end NumLean
