import NumLean.Interfaces.Fold.Commute

public section

namespace NumLean

namespace Fold

/-- Unordered isomorphism between two lawful folded ranges. -/
structure RangeEquiv {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    (xs : ρ) (ys : σ) extends {a : α // a ∈ xs} ≃ {b : β // b ∈ ys} where
  entries_perm :
    (LawfulFold.entries (ρ := σ) (α := β) ys).Perm
      ((LawfulFold.entries (ρ := ρ) (α := α) xs).map toEquiv)

/-- Order-preserving isomorphism between two lawful folded ranges. -/
structure RangeIso {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    (xs : ρ) (ys : σ) extends RangeEquiv xs ys where
  entries_eq :
    LawfulFold.entries (ρ := σ) (α := β) ys =
      (LawfulFold.entries (ρ := ρ) (α := α) xs).map toEquiv

namespace RangeEquiv

def ofSubtypeEquiv {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ}
    (e : {a : α // a ∈ xs} ≃ {b : β // b ∈ ys})
    (hentries :
      (LawfulFold.entries (ρ := σ) (α := β) ys).Perm
        ((LawfulFold.entries (ρ := ρ) (α := α) xs).map e)) :
    RangeEquiv xs ys where
  toEquiv := e
  entries_perm := hentries

def ofSubtypeEquivAll {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ}
    (e : {a : α // a ∈ xs} ≃ {b : β // b ∈ ys}) :
    RangeEquiv xs ys :=
  ofSubtypeEquiv e <|
    List.Perm.of_nodup_of_forall_mem_iff
      (LawfulFold.entries_nodup (ρ := σ) (α := β) ys)
      (by
        apply List.Nodup.map
        · intro a b h
          exact e.injective h
        · exact LawfulFold.entries_nodup (ρ := ρ) (α := α) xs)
      (by
        intro b
        constructor
        · intro _
          rw [List.mem_map]
          refine ⟨e.symm b, ?_, ?_⟩
          · exact LawfulFold.mem_entries (ρ := ρ) (α := α) (xs := xs) (e.symm b).2
          · simp
        · intro _
          exact LawfulFold.mem_entries (ρ := σ) (α := β) (xs := ys) b.2)

def refl {ρ : Type u} {α : Type v}
    {d : Membership α ρ} [FoldEntries ρ α d] [Fold ρ] [LawfulFold ρ α d]
    (xs : ρ) : RangeEquiv xs xs where
  toEquiv := Equiv.refl _
  entries_perm := by simp

def symm {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : RangeEquiv xs ys) : RangeEquiv ys xs where
  toEquiv := e.toEquiv.symm
  entries_perm := by
    have hmap := e.entries_perm.map e.toEquiv.symm
    refine (List.Perm.of_eq ?_).trans hmap.symm
    simp [List.map_map]

def trans {ρ : Type u} {σ : Type v} {τ : Type w} {α : Type x} {β : Type y} {γ : Type z}
    {dρ : Membership α ρ} {dσ : Membership β σ} {dτ : Membership γ τ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [FoldEntries τ γ dτ]
    [Fold ρ] [Fold σ] [Fold τ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ] [LawfulFold τ γ dτ]
    {xs : ρ} {ys : σ} {zs : τ} (e : RangeEquiv xs ys) (f : RangeEquiv ys zs) :
    RangeEquiv xs zs where
  toEquiv := e.toEquiv.trans f.toEquiv
  entries_perm := by
    refine f.entries_perm.trans ?_
    have hmap := e.entries_perm.map f.toEquiv
    refine hmap.trans (List.Perm.of_eq ?_)
    simp [List.map_map]

theorem fold_eq_of_pairwise_commutes {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {γ : Type y} {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : RangeEquiv xs ys) (init : γ)
    (f : (b : β) → b ∈ ys → γ → γ) (hcomm : PairwiseCommutes ys f) :
    Fold.fold ys init f =
      Fold.fold xs init fun a ha acc =>
        f (e.toEquiv ⟨a, ha⟩).1 (e.toEquiv ⟨a, ha⟩).2 acc := by
  rw [LawfulFold.fold_eq_foldl (xs := ys) (init := init) (f := f)]
  rw [LawfulFold.fold_eq_foldl (xs := xs) (init := init)
    (f := fun a ha acc => f (e.toEquiv ⟨a, ha⟩).1 (e.toEquiv ⟨a, ha⟩).2 acc)]
  calc
    (LawfulFold.entries (ρ := σ) (α := β) ys).foldl
        (fun acc b => f b.1 b.2 acc) init =
      ((LawfulFold.entries (ρ := ρ) (α := α) xs).map e.toEquiv).foldl
        (fun acc b => f b.1 b.2 acc) init := by
        apply List.foldl_eq_of_perm_of_nodup_pairwise_commutes
        · exact LawfulFold.entries_nodup (ρ := σ) (α := β) ys
        · exact e.entries_perm
        · intro a b ha hb hne acc
          exact hcomm a b hne acc
    _ = (LawfulFold.entries (ρ := ρ) (α := α) xs).foldl
        (fun acc a => f (e.toEquiv a).1 (e.toEquiv a).2 acc) init := by
        simp [List.foldl_map]

end RangeEquiv

namespace RangeIso

def ofSubtypeEquiv {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ}
    (e : {a : α // a ∈ xs} ≃ {b : β // b ∈ ys})
    (hentries :
      LawfulFold.entries (ρ := σ) (α := β) ys =
        (LawfulFold.entries (ρ := ρ) (α := α) xs).map e) :
    RangeIso xs ys where
  toEquiv := e
  entries_perm := by rw [hentries]
  entries_eq := hentries

def refl {ρ : Type u} {α : Type v}
    {d : Membership α ρ} [FoldEntries ρ α d] [Fold ρ] [LawfulFold ρ α d]
    (xs : ρ) : RangeIso xs xs where
  toEquiv := Equiv.refl _
  entries_perm := by simp
  entries_eq := by simp

def symm {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : RangeIso xs ys) : RangeIso ys xs where
  toEquiv := e.toEquiv.symm
  entries_perm := (RangeEquiv.symm e.toRangeEquiv).entries_perm
  entries_eq := by
    rw [e.entries_eq]
    simp [List.map_map]

def trans {ρ : Type u} {σ : Type v} {τ : Type w} {α : Type x} {β : Type y} {γ : Type z}
    {dρ : Membership α ρ} {dσ : Membership β σ} {dτ : Membership γ τ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [FoldEntries τ γ dτ]
    [Fold ρ] [Fold σ] [Fold τ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ] [LawfulFold τ γ dτ]
    {xs : ρ} {ys : σ} {zs : τ} (e : RangeIso xs ys) (f : RangeIso ys zs) :
    RangeIso xs zs where
  toEquiv := e.toEquiv.trans f.toEquiv
  entries_perm := (RangeEquiv.trans e.toRangeEquiv f.toRangeEquiv).entries_perm
  entries_eq := by
    rw [f.entries_eq, e.entries_eq]
    simp [List.map_map]

theorem fold_eq {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {γ : Type y} {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : RangeIso xs ys) (init : γ)
    (f : (b : β) → b ∈ ys → γ → γ) :
    Fold.fold ys init f =
      Fold.fold xs init fun a ha acc =>
        f (e.toEquiv ⟨a, ha⟩).1 (e.toEquiv ⟨a, ha⟩).2 acc := by
  rw [LawfulFold.fold_eq_foldl (xs := ys) (init := init) (f := f)]
  rw [LawfulFold.fold_eq_foldl (xs := xs) (init := init)
    (f := fun a ha acc => f (e.toEquiv ⟨a, ha⟩).1 (e.toEquiv ⟨a, ha⟩).2 acc)]
  change (LawfulFold.entries (ρ := σ) (α := β) ys).foldl
      (fun acc a => f a.1 a.2 acc) init =
    (LawfulFold.entries (ρ := ρ) (α := α) xs).foldl
      (fun acc a => f (e.toEquiv a).1 (e.toEquiv a).2 acc) init
  rw [e.entries_eq]
  simp [List.foldl_map]

end RangeIso

end Fold

end NumLean
