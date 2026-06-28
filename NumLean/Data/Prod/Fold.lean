module

public import NumLean.Data.Prod.Order
public import NumLean.Interfaces.Fold.RangeIso

@[expose] public section

public section

namespace NumLean

namespace Fold

instance instMembershipRcoProd {α : Type u} {β : Type v}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)] :
    Membership (α × β) (Std.Rco (α × β)) where
  mem xs x := x.1 ∈ (xs.lower.1...xs.upper.1 : Std.Rco α) ∧
    x.2 ∈ (xs.lower.2...xs.upper.2 : Std.Rco β)

theorem mem_rco_prod_iff {α : Type u} {β : Type v}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)]
    {lo hi x : α × β} :
    x ∈ (lo...hi : Std.Rco (α × β)) ↔
      x.1 ∈ (lo.1...hi.1 : Std.Rco α) ∧ x.2 ∈ (lo.2...hi.2 : Std.Rco β) := by
  rfl

def prodEntry {α : Type u} {β : Type v}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)]
    (xs : Std.Rco α) (ys : Std.Rco β)
    (a : {a : α // a ∈ xs}) (b : {b : β // b ∈ ys}) :
    {p : α × β // p ∈ ((xs.lower, ys.lower)...(xs.upper, ys.upper) : Std.Rco (α × β))} :=
  ⟨(a.1, b.1), by
    rw [mem_rco_prod_iff]
    exact ⟨a.2, b.2⟩⟩

def prodEntries {α : Type u} {β : Type v}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)]
    [FoldEntries (Std.Rco α) α inferInstance] [FoldEntries (Std.Rco β) β inferInstance]
    (xs : Std.Rco α) (ys : Std.Rco β) :
    List {p : α × β // p ∈ ((xs.lower, ys.lower)...(xs.upper, ys.upper) : Std.Rco (α × β))} :=
  (NumLean.entries xs).flatMap fun a =>
    (NumLean.entries ys).map fun b => prodEntry xs ys a b

private theorem mem_prodEntries {α : Type u} {β : Type v}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)]
    [FoldEntries (Std.Rco α) α inferInstance] [FoldEntries (Std.Rco β) β inferInstance]
    [Fold (Std.Rco α)] [Fold (Std.Rco β)]
    [LawfulFold (Std.Rco α) α inferInstance] [LawfulFold (Std.Rco β) β inferInstance]
    {xs : Std.Rco α} {ys : Std.Rco β}
    (p : {p : α × β // p ∈ ((xs.lower, ys.lower)...(xs.upper, ys.upper) : Std.Rco (α × β))}) :
    p ∈ prodEntries xs ys := by
  rcases p with ⟨⟨a, b⟩, hp⟩
  rw [mem_rco_prod_iff] at hp
  rw [prodEntries, List.mem_flatMap]
  refine ⟨⟨a, hp.1⟩, LawfulFold.mem_entries hp.1, ?_⟩
  rw [List.mem_map]
  refine ⟨⟨b, hp.2⟩, LawfulFold.mem_entries hp.2, ?_⟩
  rfl

private theorem prodEntries_nodup {α : Type u} {β : Type v}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)]
    [FoldEntries (Std.Rco α) α inferInstance] [FoldEntries (Std.Rco β) β inferInstance]
    [Fold (Std.Rco α)] [Fold (Std.Rco β)]
    [LawfulFold (Std.Rco α) α inferInstance] [LawfulFold (Std.Rco β) β inferInstance]
    (xs : Std.Rco α) (ys : Std.Rco β) :
    (prodEntries xs ys).Nodup := by
  classical
  unfold prodEntries
  rw [List.nodup_flatMap]
  constructor
  · intro a ha
    apply List.Nodup.map
    · intro b c h
      apply Subtype.ext
      exact congrArg (fun p : {p : α × β // p ∈ ((xs.lower, ys.lower)...(xs.upper, ys.upper) : Std.Rco (α × β))} => p.1.2) h
    · exact LawfulFold.entries_nodup ys
  · exact (LawfulFold.entries_nodup xs).imp fun hne p hp_a hp_b => by
      rw [List.mem_map] at hp_a hp_b
      rcases hp_a with ⟨pa, hpa, rfl⟩
      rcases hp_b with ⟨pb, hpb, hp_b_eq⟩
      apply hne
      apply Subtype.ext
      exact (congrArg (fun p : {p : α × β // p ∈ ((xs.lower, ys.lower)...(xs.upper, ys.upper) : Std.Rco (α × β))} => p.1.1) hp_b_eq).symm

/-- Row-major fold over a product range: first component is outer, second component is inner. -/
@[always_inline, inline, default_instance low] instance instFoldEntriesRcoProd {α : Type u} {β : Type v}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)]
    [FoldEntries (Std.Rco α) α inferInstance] [FoldEntries (Std.Rco β) β inferInstance]
    :
    FoldEntries (Std.Rco (α × β)) (α × β) inferInstance where
  entries xs := prodEntries (xs.lower.1...xs.upper.1 : Std.Rco α)
    (xs.lower.2...xs.upper.2 : Std.Rco β)

@[always_inline, inline, default_instance low] instance instFoldRcoProd {α : Type u} {β : Type v}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)]
    [FoldEntries (Std.Rco α) α inferInstance] [FoldEntries (Std.Rco β) β inferInstance]
    [Fold (Std.Rco α)] [Fold (Std.Rco β)] :
    Fold (Std.Rco (α × β)) where
  fold xs init f :=
    Fold.fold (xs.lower.1...xs.upper.1 : Std.Rco α) init fun a ha acc =>
      Fold.fold (xs.lower.2...xs.upper.2 : Std.Rco β) acc fun b hb acc =>
        f (a, b) (by
          rw [mem_rco_prod_iff]
          exact ⟨ha, hb⟩) acc

theorem fold_rco_prod_eq_outer_inner {α : Type u} {β : Type v} {γ : Type w}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)]
    [FoldEntries (Std.Rco α) α inferInstance] [FoldEntries (Std.Rco β) β inferInstance]
    [Fold (Std.Rco α)] [Fold (Std.Rco β)]
    [LawfulFold (Std.Rco α) α inferInstance] [LawfulFold (Std.Rco β) β inferInstance]
    (lo hi : α × β) (init : γ)
    (f : (x : α × β) → x ∈ (lo...hi : Std.Rco (α × β)) → γ → γ) :
    Fold.fold (lo...hi : Std.Rco (α × β)) init f
    =
    Fold.fold (lo.1...hi.1 : Std.Rco α) init fun a ha acc =>
      Fold.fold (lo.2...hi.2 : Std.Rco β) acc fun b hb acc =>
        f (a, b) (by
          rw [mem_rco_prod_iff]
          exact ⟨ha, hb⟩) acc := rfl

theorem fold_rco_outer_inner_eq_prod {α : Type u} {β : Type v} {γ : Type w}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)]
    [FoldEntries (Std.Rco α) α inferInstance] [FoldEntries (Std.Rco β) β inferInstance]
    [Fold (Std.Rco α)] [Fold (Std.Rco β)]
    [LawfulFold (Std.Rco α) α inferInstance] [LawfulFold (Std.Rco β) β inferInstance]
    (lo hi : α) (lo' hi' : β) (init : γ)
    (f : (a : α) → (b : β) → (a ∈ lo...hi) → (b ∈ lo'...hi') → γ → γ) :
    (Fold.fold (lo...hi) init fun a ha acc =>
      Fold.fold (lo'...hi') acc fun b hb acc =>
        f a b ha hb acc)
    =
    Fold.fold ((lo,lo')...(hi,hi')) init
      (fun (a,b) h acc => f a b (Fold.mem_rco_prod_iff.1 h).1 (Fold.mem_rco_prod_iff.1 h).2 acc) := rfl
    --



instance (priority := low) instLawfulFoldRcoProd {α : Type u} {β : Type v}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)]
    [FoldEntries (Std.Rco α) α inferInstance] [FoldEntries (Std.Rco β) β inferInstance]
    [Fold (Std.Rco α)] [Fold (Std.Rco β)]
    [LawfulFold (Std.Rco α) α inferInstance] [LawfulFold (Std.Rco β) β inferInstance] :
    LawfulFold (Std.Rco (α × β)) (α × β) inferInstance where
  mem_entries {xs} {a} h := by
    change ⟨a, h⟩ ∈ prodEntries (xs.lower.1...xs.upper.1 : Std.Rco α)
      (xs.lower.2...xs.upper.2 : Std.Rco β)
    exact mem_prodEntries (xs := xs.lower.1...xs.upper.1) (ys := xs.lower.2...xs.upper.2) ⟨a, h⟩
  entries_nodup xs := by
    change (prodEntries (xs.lower.1...xs.upper.1 : Std.Rco α)
      (xs.lower.2...xs.upper.2 : Std.Rco β)).Nodup
    exact prodEntries_nodup (xs.lower.1...xs.upper.1 : Std.Rco α)
      (xs.lower.2...xs.upper.2 : Std.Rco β)
  fold_eq_foldl xs init f := by
    rw [fold_rco_prod_eq_outer_inner]
    rw [LawfulFold.fold_eq_foldl]
    simp_rw [LawfulFold.fold_eq_foldl]
    change List.foldl
      (fun acc a => List.foldl (fun acc b => f (a.1, b.1) (by
        rw [mem_rco_prod_iff]
        exact ⟨a.2, b.2⟩) acc) acc (LawfulFold.entries (ρ := Std.Rco β) (α := β) (xs.lower.2...xs.upper.2 : Std.Rco β)))
      init (LawfulFold.entries (ρ := Std.Rco α) (α := α) (xs.lower.1...xs.upper.1 : Std.Rco α)) =
        (prodEntries (xs.lower.1...xs.upper.1 : Std.Rco α)
          (xs.lower.2...xs.upper.2 : Std.Rco β)).foldl (fun acc a => f a.1 a.2 acc) init
    simp [prodEntries, List.foldl_flatMap, List.foldl_map, prodEntry]

end Fold

end NumLean
