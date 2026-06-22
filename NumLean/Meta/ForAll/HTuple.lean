import NumLean.Data.HTuple.RangeIterator
import NumLean.Meta.ForAll.Basic

public section

namespace NumLean
namespace Meta.ForAll

/-- No-break HTuple range traversal specialized by tuple profile.

The leaf case delegates to the scalar `ForAllIn'` backend, so native scalar ranges such as `Nat` and
`UInt64` use the same no-break loops as scalar `for_all`. -/
class ForAllInProfile (p : HTuple.Profile) (α : Type u) (β : Type v)
    [LE α] [LT α] [DecidableLT α] where
  forAllInProfile (r : Std.Rco (HTuple α p)) (init : β)
    (f : (idx : HTuple α p) → idx ∈ r → β → β) : β

attribute [always_inline, inline, specialize] ForAllInProfile.forAllInProfile

/-- Reference semantics for profile-specialized HTuple no-break traversal. -/
class LawfulForAllInProfile (p : HTuple.Profile) (α : Type u) (β : Type v)
    [LE α] [LT α] [DecidableLT α] [ForAllInProfile p α β] where
  entries : (r : Std.Rco (HTuple α p)) → List {idx : HTuple α p // idx ∈ r}
  mem_entries : ∀ {r : Std.Rco (HTuple α p)} {idx : HTuple α p},
    (hidx : idx ∈ r) → ⟨idx, hidx⟩ ∈ entries r
  forAllInProfile_eq_foldl : ∀ (r : Std.Rco (HTuple α p)) (init : β)
    (f : (idx : HTuple α p) → idx ∈ r → β → β),
      ForAllInProfile.forAllInProfile r init f =
        (entries r).foldl (fun acc idx => f idx.1 idx.2 acc) init

@[always_inline, inline] instance {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α]
    [ForAllIn' (Std.Rco α) α β inferInstance] :
    ForAllInProfile .leaf α β where
  forAllInProfile r init f :=
    match r with
    | ⟨.leaf lo, .leaf hi⟩ =>
        ForAllIn'.forAllIn' (lo...hi) init fun idx hidx acc =>
          f (.leaf idx) (HTuple.Range.mem_iff_Valid.2 hidx) acc

@[always_inline, inline] instance {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α]
    [ForAllIn' (Std.Rco α) α β inferInstance]
    [LawfulForAllIn' (Std.Rco α) α β inferInstance] :
    LawfulForAllInProfile .leaf α β where
  entries r :=
    match r with
    | ⟨.leaf lo, .leaf hi⟩ =>
        (LawfulForAllIn'.entries (ρ := Std.Rco α) (α := α) (β := β) (lo...hi)).map fun idx =>
          ⟨.leaf idx.1, HTuple.Range.mem_iff_Valid.2 idx.2⟩
  mem_entries := by
    intro r idx hidx
    cases r with
    | mk lower upper =>
    cases lower with | leaf lo =>
    cases upper with | leaf hi =>
    cases idx with | leaf idx =>
      rw [List.mem_map]
      refine ⟨⟨idx, HTuple.Range.mem_iff_Valid.mp hidx⟩, ?_, rfl⟩
      exact LawfulForAllIn'.mem_entries (ρ := Std.Rco α) (α := α) (β := β)
        (HTuple.Range.mem_iff_Valid.mp hidx)
  forAllInProfile_eq_foldl r init f := by
    cases r with
    | mk lower upper =>
      cases lower with
      | leaf lo =>
      cases upper with
      | leaf hi =>
      change ForAllIn'.forAllIn' (lo...hi) init
        (fun idx hidx acc => f (.leaf idx) (HTuple.Range.mem_iff_Valid.2 hidx) acc) = _
      rw [LawfulForAllIn'.forAllIn'_eq_foldl (xs := lo...hi) (init := init)
        (f := fun idx hidx acc => f (.leaf idx) (HTuple.Range.mem_iff_Valid.2 hidx) acc)]
      simp [List.foldl_map]

@[always_inline, inline] instance {p q : HTuple.Profile} {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α]
    [ForAllInProfile p α β] [ForAllInProfile q α β] :
    ForAllInProfile (.prod p q) α β where
  forAllInProfile r init f :=
    match r with
    | ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩ =>
        let r₀ : Std.Rco (HTuple α p) := lo₀...hi₀
        let r₁ : Std.Rco (HTuple α q) := lo₁...hi₁
        ForAllInProfile.forAllInProfile r₀ init fun idx₀ hidx₀ acc =>
          ForAllInProfile.forAllInProfile r₁ acc fun idx₁ hidx₁ acc =>
            f (.prod idx₀ idx₁)
              (by
                apply HTuple.Range.mem_iff_Valid.2
                change HTuple.Range.Valid lo₀ hi₀ idx₀ ∧ HTuple.Range.Valid lo₁ hi₁ idx₁
                exact ⟨HTuple.Range.mem_iff_Valid.1 hidx₀, HTuple.Range.mem_iff_Valid.1 hidx₁⟩) acc

@[always_inline, inline] instance {p q : HTuple.Profile} {α : Type u} {β : Type v}
    [LE α] [LT α] [DecidableLT α]
    [ForAllInProfile p α β] [ForAllInProfile q α β]
    [LawfulForAllInProfile p α β] [LawfulForAllInProfile q α β] :
    LawfulForAllInProfile (.prod p q) α β where
  entries r :=
    match r with
    | ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩ =>
        let r₀ : Std.Rco (HTuple α p) := lo₀...hi₀
        let r₁ : Std.Rco (HTuple α q) := lo₁...hi₁
        (LawfulForAllInProfile.entries (p := p) (α := α) (β := β) r₀).flatMap fun idx₀ =>
          (LawfulForAllInProfile.entries (p := q) (α := α) (β := β) r₁).map fun idx₁ =>
            ⟨.prod idx₀.1 idx₁.1,
              by
                apply HTuple.Range.mem_iff_Valid.2
                change HTuple.Range.Valid lo₀ hi₀ idx₀.1 ∧ HTuple.Range.Valid lo₁ hi₁ idx₁.1
                exact ⟨HTuple.Range.mem_iff_Valid.1 idx₀.2, HTuple.Range.mem_iff_Valid.1 idx₁.2⟩⟩
  mem_entries := by
    intro r idx hidx
    cases r with
    | mk lower upper =>
    cases lower with | prod lo₀ lo₁ =>
    cases upper with | prod hi₀ hi₁ =>
    cases idx with | prod idx₀ idx₁ =>
      have hvalid := HTuple.Range.mem_iff_Valid.mp hidx
      let hidx₀ : idx₀ ∈ (lo₀...hi₀) := HTuple.Range.mem_iff_Valid.2 hvalid.1
      let hidx₁ : idx₁ ∈ (lo₁...hi₁) := HTuple.Range.mem_iff_Valid.2 hvalid.2
      simp only [List.mem_flatMap, List.mem_map]
      refine ⟨⟨idx₀, hidx₀⟩, LawfulForAllInProfile.mem_entries (p := p) (α := α) (β := β) hidx₀, ?_⟩
      refine ⟨⟨idx₁, hidx₁⟩, LawfulForAllInProfile.mem_entries (p := q) (α := α) (β := β) hidx₁, ?_⟩
      rfl
  forAllInProfile_eq_foldl r init f := by
    cases r with
    | mk lower upper =>
      cases lower with
      | prod lo₀ lo₁ =>
      cases upper with
      | prod hi₀ hi₁ =>
      change ForAllInProfile.forAllInProfile (lo₀...hi₀) init
        (fun idx₀ hidx₀ acc =>
          ForAllInProfile.forAllInProfile (lo₁...hi₁) acc fun idx₁ hidx₁ acc =>
            f (.prod idx₀ idx₁)
              (by
                apply HTuple.Range.mem_iff_Valid.2
                change HTuple.Range.Valid lo₀ hi₀ idx₀ ∧ HTuple.Range.Valid lo₁ hi₁ idx₁
                exact ⟨HTuple.Range.mem_iff_Valid.1 hidx₀, HTuple.Range.mem_iff_Valid.1 hidx₁⟩) acc) = _
      rw [LawfulForAllInProfile.forAllInProfile_eq_foldl
        (p := p) (α := α) (β := β) (r := lo₀...hi₀) (init := init)
        (f := fun idx₀ hidx₀ acc =>
          ForAllInProfile.forAllInProfile (lo₁...hi₁) acc fun idx₁ hidx₁ acc =>
            f (.prod idx₀ idx₁)
              (by
                apply HTuple.Range.mem_iff_Valid.2
                change HTuple.Range.Valid lo₀ hi₀ idx₀ ∧ HTuple.Range.Valid lo₁ hi₁ idx₁
                exact ⟨HTuple.Range.mem_iff_Valid.1 hidx₀, HTuple.Range.mem_iff_Valid.1 hidx₁⟩) acc)]
      simp [LawfulForAllInProfile.forAllInProfile_eq_foldl, List.foldl_flatMap, List.foldl_map]

@[always_inline, inline] instance {α : Type u} {β : Type v} [LE α] [LT α] [DecidableLT α]
    {p : HTuple.Profile} [ForAllInProfile p α β] :
    ForAllIn' (Std.Rco (HTuple α p)) (HTuple α p) β HTuple.Range.instMembershipRcoHTuple where
  forAllIn' xs init f :=
    ForAllInProfile.forAllInProfile xs init f

@[always_inline, inline] instance {α : Type u} {β : Type v} [LE α] [LT α] [DecidableLT α]
    {p : HTuple.Profile} [ForAllInProfile p α β] [LawfulForAllInProfile p α β] :
    LawfulForAllIn' (Std.Rco (HTuple α p)) (HTuple α p) β HTuple.Range.instMembershipRcoHTuple where
  entries := fun xs => LawfulForAllInProfile.entries (p := p) (α := α) (β := β) xs
  mem_entries h := LawfulForAllInProfile.mem_entries (p := p) (α := α) (β := β) h
  forAllIn'_eq_foldl xs init f :=
    LawfulForAllInProfile.forAllInProfile_eq_foldl xs init f

end Meta.ForAll
end NumLean
