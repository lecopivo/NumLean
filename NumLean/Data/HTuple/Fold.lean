import NumLean.Data.HTuple.RangeIterator
import NumLean.Data.Prod.Fold
import NumLean.Interfaces.Fold

public section

namespace NumLean

/-- Recursive no-break HTuple range traversal for `Fold`.

For product profiles the left coordinate is the outer loop and the right coordinate is the
inner loop, so the right-most coordinate changes fastest. -/
@[always_inline, inline, specialize] def foldHTuple {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α]
    [FoldEntries (Std.Rco α) α inferInstance] [Fold (Std.Rco α)] :
    {p : HTuple.Profile} → (r : Std.Rco (HTuple α p)) → (init : β) →
      ((idx : HTuple α p) → idx ∈ r → β → β) → β
  | .leaf, ⟨.leaf lo, .leaf hi⟩, init, f =>
      Fold.fold (lo...hi) init fun idx hidx acc =>
        f (.leaf idx) (HTuple.Range.mem_iff_Valid.2 hidx) acc
  | .prod p q, ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩, init, f =>
      let r₀ : Std.Rco (HTuple α p) := lo₀...hi₀
      let r₁ : Std.Rco (HTuple α q) := lo₁...hi₁
      foldHTuple (r := r₀) init fun idx₀ hidx₀ acc =>
        foldHTuple (r := r₁) acc fun idx₁ hidx₁ acc =>
          f (.prod idx₀ idx₁)
            (by
              apply HTuple.Range.mem_iff_Valid.2
              change HTuple.Range.Valid lo₀ hi₀ idx₀ ∧ HTuple.Range.Valid lo₁ hi₁ idx₁
              exact ⟨HTuple.Range.mem_iff_Valid.1 hidx₀, HTuple.Range.mem_iff_Valid.1 hidx₁⟩) acc

/-- Recursive reference enumeration for HTuple range traversal. -/
def foldHTupleEntries {α : Type u} [LE α] [LT α] [DecidableLT α]
    [FoldEntries (Std.Rco α) α inferInstance] :
    {p : HTuple.Profile} → (r : Std.Rco (HTuple α p)) →
      List {idx : HTuple α p // idx ∈ r}
  | .leaf, ⟨.leaf lo, .leaf hi⟩ =>
      (NumLean.entries (lo...hi : Std.Rco α)).map fun idx =>
        ⟨.leaf idx.1, HTuple.Range.mem_iff_Valid.2 idx.2⟩
  | .prod p q, ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩ =>
      let r₀ : Std.Rco (HTuple α p) := lo₀...hi₀
      let r₁ : Std.Rco (HTuple α q) := lo₁...hi₁
      (foldHTupleEntries r₀).flatMap fun idx₀ =>
        (foldHTupleEntries r₁).map fun idx₁ =>
          ⟨.prod idx₀.1 idx₁.1,
            by
              apply HTuple.Range.mem_iff_Valid.2
              change HTuple.Range.Valid lo₀ hi₀ idx₀.1 ∧ HTuple.Range.Valid lo₁ hi₁ idx₁.1
              exact ⟨HTuple.Range.mem_iff_Valid.1 idx₀.2, HTuple.Range.mem_iff_Valid.1 idx₁.2⟩⟩

instance {α : Type u} [LE α] [LT α] [DecidableLT α]
    {p : HTuple.Profile} [FoldEntries (Std.Rco α) α inferInstance] :
    FoldEntries (Std.Rco (HTuple α p)) (HTuple α p) HTuple.Range.instMembershipRcoHTuple where
  entries := foldHTupleEntries

instance {α : Type u} [LE α] [LT α] [DecidableLT α]
    {p : HTuple.Profile} [FoldEntries (Std.Rco α) α inferInstance] [Fold (Std.Rco α)]
    :
    Fold (Std.Rco (HTuple α p)) where
  fold xs init f :=
    foldHTuple (r := xs) init f

private theorem mem_foldHTupleEntries {α : Type u} [LE α] [LT α] [DecidableLT α]
    [FoldEntries (Std.Rco α) α inferInstance] [Fold (Std.Rco α)]
    [LawfulFold (Std.Rco α) α inferInstance] :
    {p : HTuple.Profile} → (r : Std.Rco (HTuple α p)) →
      (idx : {idx : HTuple α p // idx ∈ r}) → idx ∈ foldHTupleEntries r
  | .leaf, ⟨.leaf lo, .leaf hi⟩, ⟨.leaf idx, hidx⟩ => by
      rw [foldHTupleEntries, List.mem_map]
      refine ⟨⟨idx, HTuple.Range.mem_iff_Valid.1 hidx⟩,
        LawfulFold.mem_entries (HTuple.Range.mem_iff_Valid.1 hidx), ?_⟩
      rfl
  | .prod p q, ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩, ⟨.prod idx₀ idx₁, hidx⟩ => by
      have hvalid := HTuple.Range.mem_iff_Valid.1 hidx
      change HTuple.Range.Valid lo₀ hi₀ idx₀ ∧ HTuple.Range.Valid lo₁ hi₁ idx₁ at hvalid
      rw [foldHTupleEntries, List.mem_flatMap]
      refine ⟨⟨idx₀, HTuple.Range.mem_iff_Valid.2 hvalid.1⟩,
        mem_foldHTupleEntries _ _, ?_⟩
      rw [List.mem_map]
      refine ⟨⟨idx₁, HTuple.Range.mem_iff_Valid.2 hvalid.2⟩,
        mem_foldHTupleEntries _ _, ?_⟩
      rfl

private theorem foldHTupleEntries_nodup {α : Type u} [LE α] [LT α] [DecidableLT α]
    [FoldEntries (Std.Rco α) α inferInstance] [Fold (Std.Rco α)]
    [LawfulFold (Std.Rco α) α inferInstance] :
    {p : HTuple.Profile} → (r : Std.Rco (HTuple α p)) → (foldHTupleEntries r).Nodup
  | .leaf, ⟨.leaf lo, .leaf hi⟩ => by
      rw [foldHTupleEntries]
      apply List.Nodup.map
      · intro a b h
        apply Subtype.ext
        have hval := congrArg Subtype.val h
        injection hval
      · exact LawfulFold.entries_nodup (lo...hi : Std.Rco α)
  | .prod p q, ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩ => by
      rw [foldHTupleEntries, List.nodup_flatMap]
      constructor
      · intro idx₀ hidx₀
        apply List.Nodup.map
        · intro idx₁ idx₂ h
          apply Subtype.ext
          have hval := congrArg Subtype.val h
          injection hval
        · exact foldHTupleEntries_nodup (lo₁...hi₁ : Std.Rco (HTuple α q))
      · exact (foldHTupleEntries_nodup (lo₀...hi₀ : Std.Rco (HTuple α p))).imp fun hne idx hp₁ hp₂ => by
          rw [List.mem_map] at hp₁ hp₂
          rcases hp₁ with ⟨idx₁, hidx₁, rfl⟩
          rcases hp₂ with ⟨idx₂, hidx₂, hp₂_eq⟩
          apply hne
          apply Subtype.ext
          let fstOf : HTuple α (.prod p q) → HTuple α p
            | .prod fst _ => fst
          exact (congrArg (fun idx : {idx : HTuple α (.prod p q) //
            idx ∈ ((lo₀.prod lo₁)...(hi₀.prod hi₁) : Std.Rco (HTuple α (.prod p q)))} =>
              fstOf idx.1) hp₂_eq).symm

theorem foldHTuple_eq_foldl {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α]
    [FoldEntries (Std.Rco α) α inferInstance] [Fold (Std.Rco α)]
    [LawfulFold (Std.Rco α) α inferInstance] :
    {p : HTuple.Profile} → (r : Std.Rco (HTuple α p)) → (init : β) →
      (f : (idx : HTuple α p) → idx ∈ r → β → β) →
        foldHTuple (r := r) init f =
          (foldHTupleEntries r).foldl (fun acc idx => f idx.1 idx.2 acc) init
  | .leaf, ⟨.leaf lo, .leaf hi⟩, init, f => by
      change Fold.fold (lo...hi) init
        (fun idx hidx acc => f (.leaf idx) (HTuple.Range.mem_iff_Valid.2 hidx) acc) = _
      rw [LawfulFold.fold_eq_foldl (xs := lo...hi) (init := init)
        (f := fun idx hidx acc => f (.leaf idx) (HTuple.Range.mem_iff_Valid.2 hidx) acc)]
      simp [foldHTupleEntries, List.foldl_map]
  | .prod p q, ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩, init, f => by
      change foldHTuple (r := (lo₀...hi₀ : Std.Rco (HTuple α p))) init
        (fun idx₀ hidx₀ acc =>
          foldHTuple (r := (lo₁...hi₁ : Std.Rco (HTuple α q))) acc fun idx₁ hidx₁ acc =>
            f (.prod idx₀ idx₁)
              (by
                apply HTuple.Range.mem_iff_Valid.2
                change HTuple.Range.Valid lo₀ hi₀ idx₀ ∧ HTuple.Range.Valid lo₁ hi₁ idx₁
                exact ⟨HTuple.Range.mem_iff_Valid.1 hidx₀, HTuple.Range.mem_iff_Valid.1 hidx₁⟩) acc) = _
      rw [foldHTuple_eq_foldl (r := (lo₀...hi₀ : Std.Rco (HTuple α p))) (init := init)
        (f := fun idx₀ hidx₀ acc =>
          foldHTuple (r := (lo₁...hi₁ : Std.Rco (HTuple α q))) acc fun idx₁ hidx₁ acc =>
            f (.prod idx₀ idx₁)
              (by
                apply HTuple.Range.mem_iff_Valid.2
                change HTuple.Range.Valid lo₀ hi₀ idx₀ ∧ HTuple.Range.Valid lo₁ hi₁ idx₁
                exact ⟨HTuple.Range.mem_iff_Valid.1 hidx₀, HTuple.Range.mem_iff_Valid.1 hidx₁⟩) acc)]
      simp [foldHTupleEntries, foldHTuple_eq_foldl, List.foldl_flatMap, List.foldl_map]

/-- Row-major entries for a product HTuple range are outer entries flat-mapped over inner entries. -/
theorem entries_htuple_prod {α : Type u} [LE α] [LT α] [DecidableLT α]
    {p q : HTuple.Profile}
    [FoldEntries (Std.Rco α) α inferInstance] [Fold (Std.Rco α)]
    [LawfulFold (Std.Rco α) α inferInstance]
    (lo₀ hi₀ : HTuple α p) (lo₁ hi₁ : HTuple α q) :
    foldHTupleEntries ((lo₀.prod lo₁)...(hi₀.prod hi₁) : Std.Rco (HTuple α (.prod p q))) =
      (foldHTupleEntries (lo₀...hi₀ : Std.Rco (HTuple α p))).flatMap fun idx₀ =>
        (foldHTupleEntries (lo₁...hi₁ : Std.Rco (HTuple α q))).map fun idx₁ =>
          ⟨.prod idx₀.1 idx₁.1,
            by
              apply HTuple.Range.mem_iff_Valid.2
              change HTuple.Range.Valid lo₀ hi₀ idx₀.1 ∧ HTuple.Range.Valid lo₁ hi₁ idx₁.1
              exact ⟨HTuple.Range.mem_iff_Valid.1 idx₀.2,
                HTuple.Range.mem_iff_Valid.1 idx₁.2⟩⟩ := rfl

/-- Row-major fold over a product HTuple range is an outer fold followed by an inner fold. -/
theorem fold_htuple_prod_eq_outer_inner {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α]
    {p q : HTuple.Profile}
    [FoldEntries (Std.Rco α) α inferInstance] [Fold (Std.Rco α)]
    [LawfulFold (Std.Rco α) α inferInstance]
    (lo₀ hi₀ : HTuple α p) (lo₁ hi₁ : HTuple α q) (init : β)
    (f : (idx : HTuple α (.prod p q)) →
      idx ∈ ((lo₀.prod lo₁)...(hi₀.prod hi₁) : Std.Rco (HTuple α (.prod p q))) → β → β) :
    Fold.fold ((lo₀.prod lo₁)...(hi₀.prod hi₁) : Std.Rco (HTuple α (.prod p q))) init f =
      Fold.fold (lo₀...hi₀ : Std.Rco (HTuple α p)) init fun idx₀ hidx₀ acc =>
        Fold.fold (lo₁...hi₁ : Std.Rco (HTuple α q)) acc fun idx₁ hidx₁ acc =>
          f (.prod idx₀ idx₁)
            (by
              apply HTuple.Range.mem_iff_Valid.2
              change HTuple.Range.Valid lo₀ hi₀ idx₀ ∧ HTuple.Range.Valid lo₁ hi₁ idx₁
              exact ⟨HTuple.Range.mem_iff_Valid.1 hidx₀,
                HTuple.Range.mem_iff_Valid.1 hidx₁⟩) acc := rfl

theorem fold_htuple_outer_inner_eq_prod {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α]
    {p q : HTuple.Profile}
    [FoldEntries (Std.Rco α) α inferInstance] [Fold (Std.Rco α)]
    [LawfulFold (Std.Rco α) α inferInstance]
    (lo₀ hi₀ : HTuple α p) (lo₁ hi₁ : HTuple α q) (init : β)
    (f : (idx : HTuple α (.prod p q)) →
      idx ∈ ((lo₀.prod lo₁)...(hi₀.prod hi₁) : Std.Rco (HTuple α (.prod p q))) → β → β) :
    (Fold.fold (lo₀...hi₀ : Std.Rco (HTuple α p)) init fun idx₀ hidx₀ acc =>
      Fold.fold (lo₁...hi₁ : Std.Rco (HTuple α q)) acc fun idx₁ hidx₁ acc =>
        f (.prod idx₀ idx₁)
          (by
            apply HTuple.Range.mem_iff_Valid.2
            change HTuple.Range.Valid lo₀ hi₀ idx₀ ∧ HTuple.Range.Valid lo₁ hi₁ idx₁
            exact ⟨HTuple.Range.mem_iff_Valid.1 hidx₀,
              HTuple.Range.mem_iff_Valid.1 hidx₁⟩) acc)
    =
    Fold.fold ((lo₀.prod lo₁)...(hi₀.prod hi₁) : Std.Rco (HTuple α (.prod p q))) init f := by
  rw [fold_htuple_prod_eq_outer_inner]

instance {α : Type u} [LE α] [LT α] [DecidableLT α]
    {p : HTuple.Profile} [FoldEntries (Std.Rco α) α inferInstance] [Fold (Std.Rco α)]
    [LawfulFold (Std.Rco α) α inferInstance] :
    LawfulFold (Std.Rco (HTuple α p)) (HTuple α p)
      HTuple.Range.instMembershipRcoHTuple where
  mem_entries {xs} {idx} hidx := by
    exact mem_foldHTupleEntries xs ⟨idx, hidx⟩
  entries_nodup xs := by
    exact foldHTupleEntries_nodup xs
  fold_eq_foldl xs init f := by
    exact foldHTuple_eq_foldl xs init f

/-- Ordered range isomorphism between product ranges of HTuples and HTuple product ranges. -/
noncomputable def htupleProdRangeIso {α : Type u} [LE α] [LT α] [DecidableLT α]
    {p q : HTuple.Profile}
    [FoldEntries (Std.Rco α) α inferInstance] [Fold (Std.Rco α)]
    [LawfulFold (Std.Rco α) α inferInstance]
    (lo₀ hi₀ : HTuple α p) (lo₁ hi₁ : HTuple α q) :
    Fold.RangeIso
      ((lo₀, lo₁)...(hi₀, hi₁))
      ((lo₀.prod lo₁)...(hi₀.prod hi₁)) where
  toFun := fun idx =>
    ⟨.prod idx.1.1 idx.1.2, by
      rw [HTuple.Range.mem_iff_Valid]
      change HTuple.Range.Valid lo₀ hi₀ idx.1.1 ∧ HTuple.Range.Valid lo₁ hi₁ idx.1.2
      exact ⟨HTuple.Range.mem_iff_Valid.1 idx.2.1,
        HTuple.Range.mem_iff_Valid.1 idx.2.2⟩⟩
  invFun := fun idx =>
    match idx with
    | ⟨.prod idx₀ idx₁, hidx⟩ =>
        ⟨(idx₀, idx₁), by
          rw [Fold.mem_rco_prod_iff]
          rw [HTuple.Range.mem_iff_Valid] at hidx
          change HTuple.Range.Valid lo₀ hi₀ idx₀ ∧ HTuple.Range.Valid lo₁ hi₁ idx₁ at hidx
          exact ⟨HTuple.Range.mem_iff_Valid.2 hidx.1,
            HTuple.Range.mem_iff_Valid.2 hidx.2⟩⟩
  left_inv := by
    intro idx
    apply Subtype.ext
    rfl
  right_inv := by
    intro idx
    cases idx with
    | mk val hval =>
    cases val with
    | prod idx₀ idx₁ =>
    apply Subtype.ext
    rfl
  entries_perm := by
    apply List.Perm.of_eq
    change foldHTupleEntries ((lo₀.prod lo₁)...(hi₀.prod hi₁) : Std.Rco (HTuple α (.prod p q))) =
      (List.flatMap
        (fun a => List.map
          (fun b => Fold.prodEntry (lo₀...hi₀ : Std.Rco (HTuple α p))
            (lo₁...hi₁ : Std.Rco (HTuple α q)) a b)
          (foldHTupleEntries (lo₁...hi₁ : Std.Rco (HTuple α q))))
        (foldHTupleEntries (lo₀...hi₀ : Std.Rco (HTuple α p)))).map _
    rw [entries_htuple_prod]
    rw [List.map_flatMap]
    simp only [List.map_map]
    apply List.flatMap_congr
    intro a _
    apply List.map_congr_left
    intro b _
    apply Subtype.ext
    rfl
  entries_eq := by
    change foldHTupleEntries ((lo₀.prod lo₁)...(hi₀.prod hi₁) : Std.Rco (HTuple α (.prod p q))) =
      (List.flatMap
        (fun a => List.map
          (fun b => Fold.prodEntry (lo₀...hi₀ : Std.Rco (HTuple α p))
            (lo₁...hi₁ : Std.Rco (HTuple α q)) a b)
          (foldHTupleEntries (lo₁...hi₁ : Std.Rco (HTuple α q))))
        (foldHTupleEntries (lo₀...hi₀ : Std.Rco (HTuple α p)))).map _
    rw [entries_htuple_prod]
    rw [List.map_flatMap]
    simp only [List.map_map]
    apply List.flatMap_congr
    intro a _
    apply List.map_congr_left
    intro b _
    apply Subtype.ext
    rfl

end NumLean
