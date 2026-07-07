module

public import NumLean.Interfaces.Fold.RcoNative
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Batteries.Data.Fin.Fold
public import Batteries.Data.List.Lemmas

@[expose] public section

public section

namespace NumLean

namespace Fold

private theorem List.foldl_add_eq_add_sum [AddCommMonoid A] (xs : List α) (f : α → A) (init : A) :
    xs.foldl (fun acc x => acc + f x) init = init + (xs.map f).sum := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, add_assoc]

private theorem List.foldl_mul_eq_mul_prod [CommMonoid A] (xs : List α) (f : α → A) (init : A) :
    xs.foldl (fun acc x => acc * f x) init = init * (xs.map f).prod := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, mul_assoc]

/-- A folded range viewed as a finite range.

The executable fold still ranges over `xs`; this structure exposes a stable finite-index API for
proofs and user-facing theorems.  The subtype-heavy entry representation remains internal through
`entries_eq`. -/
structure FinRangeView {ρ : Type u} {α : Type v} {d : Membership α ρ}
    [FoldEntries ρ α d] [Fold ρ] [LawfulFold ρ α d] (xs : ρ) where
  size : Nat
  fromFin : Fin size → α
  mem_fromFin : ∀ i, fromFin i ∈ xs
  toFin : (a : α) → a ∈ xs → Fin size
  toFin_fromFin : ∀ i, toFin (fromFin i) (mem_fromFin i) = i
  fromFin_toFin : ∀ a h, fromFin (toFin a h) = a
  entries_eq :
    NumLean.entries xs =
      (List.finRange size).map fun i => ⟨fromFin i, mem_fromFin i⟩

namespace FinRangeView

variable {ρ : Type u} {α : Type v} {d : Membership α ρ}
    [FoldEntries ρ α d] [Fold ρ] [LawfulFold ρ α d] {xs : ρ}

@[simp]
theorem toFin_fromFin_apply (view : FinRangeView xs) (i : Fin view.size) :
    view.toFin (view.fromFin i) (view.mem_fromFin i) = i :=
  view.toFin_fromFin i

@[simp]
theorem fromFin_toFin_apply (view : FinRangeView xs) (a : α) (h : a ∈ xs) :
    view.fromFin (view.toFin a h) = a :=
  view.fromFin_toFin a h

theorem entries_eq_finRange (view : FinRangeView xs) :
    NumLean.entries xs =
      (List.finRange view.size).map fun i => ⟨view.fromFin i, view.mem_fromFin i⟩ :=
  view.entries_eq

def rangeIsoFin (view : FinRangeView xs) : {a : α // a ∈ xs} ≃ Fin view.size where
  toFun a := view.toFin a.1 a.2
  invFun i := ⟨view.fromFin i, view.mem_fromFin i⟩
  left_inv a := by
    apply Subtype.ext
    exact view.fromFin_toFin a.1 a.2
  right_inv i := view.toFin_fromFin i

theorem fold_eq_fin_foldl {β : Type w} (view : FinRangeView xs) (init : β)
    (f : (a : α) → a ∈ xs → β → β) :
    Fold.fold xs init f =
      Fin.foldl view.size
        (fun acc i => f (view.fromFin i) (view.mem_fromFin i) acc)
        init := by
  rw [LawfulFold.fold_eq_foldl (xs := xs) (init := init) (f := f)]
  rw [view.entries_eq]
  rw [Fin.foldl_eq_foldl_finRange]
  simp [List.foldl_map]

theorem sum_entries_eq_fin_sum [DecidableEq {a : α // a ∈ xs}] [AddCommMonoid A]
    (view : FinRangeView xs)
    (f : {a : α // a ∈ xs} → A) :
    ∑ a ∈ (NumLean.entries xs).toFinset, f a =
      ∑ i : Fin view.size, f ⟨view.fromFin i, view.mem_fromFin i⟩ := by
  rw [view.entries_eq]
  have hnodup :
      ((List.finRange view.size).map fun i =>
        (⟨view.fromFin i, view.mem_fromFin i⟩ : {a : α // a ∈ xs})).Nodup := by
    rw [← view.entries_eq]
    exact LawfulFold.entries_nodup (xs := xs)
  rw [List.sum_toFinset _ hnodup]
  rw [Fin.sum_univ_def]
  simp [List.map_map, Function.comp_def]

theorem prod_entries_eq_fin_prod [DecidableEq {a : α // a ∈ xs}] [CommMonoid A]
    (view : FinRangeView xs)
    (f : {a : α // a ∈ xs} → A) :
    ∏ a ∈ (NumLean.entries xs).toFinset, f a =
      ∏ i : Fin view.size, f ⟨view.fromFin i, view.mem_fromFin i⟩ := by
  rw [view.entries_eq]
  have hnodup :
      ((List.finRange view.size).map fun i =>
        (⟨view.fromFin i, view.mem_fromFin i⟩ : {a : α // a ∈ xs})).Nodup := by
    rw [← view.entries_eq]
    exact LawfulFold.entries_nodup (xs := xs)
  rw [List.prod_toFinset _ hnodup]
  rw [Fin.prod_univ_def]
  simp [List.map_map, Function.comp_def]

theorem fold_eq_fin_sum [AddCommMonoid A] (view : FinRangeView xs) (init : A)
    (f : (a : α) → a ∈ xs → A) :
    Fold.fold xs init (fun a h acc => acc + f a h) =
      init + ∑ i : Fin view.size, f (view.fromFin i) (view.mem_fromFin i) := by
  rw [view.fold_eq_fin_foldl]
  rw [Fin.foldl_eq_foldl_finRange]
  rw [List.foldl_add_eq_add_sum]
  rw [Fin.sum_univ_def]

theorem fold_eq_fin_prod [CommMonoid A] (view : FinRangeView xs) (init : A)
    (f : (a : α) → a ∈ xs → A) :
    Fold.fold xs init (fun a h acc => acc * f a h) =
      init * ∏ i : Fin view.size, f (view.fromFin i) (view.mem_fromFin i) := by
  rw [view.fold_eq_fin_foldl]
  rw [Fin.foldl_eq_foldl_finRange]
  rw [List.foldl_mul_eq_mul_prod]
  rw [Fin.prod_univ_def]

/-- Every lawful fold has a canonical finite view by indexing into its concrete `entries` list.

This is a fallback view: it is always order-correct, but `fromFin` is list-index based.  Prefer a
domain-specific view when a simple closed form such as `lo + i` or row-major unflattening is
available. -/
def ofEntries [DecidableEq {a : α // a ∈ xs}] : FinRangeView xs where
  size := (NumLean.entries xs).length
  fromFin i := (NumLean.entries xs).get i
  mem_fromFin i := (NumLean.entries xs).get i |>.2
  toFin a h := ⟨(NumLean.entries xs).idxOf ⟨a, h⟩, by
    rw [List.idxOf_lt_length_iff]
    exact LawfulFold.mem_entries (xs := xs) h⟩
  toFin_fromFin i := by
    apply Fin.ext
    exact List.get_idxOf (LawfulFold.entries_nodup (xs := xs)) i
  fromFin_toFin a h := by
    exact congrArg Subtype.val
      (List.idxOf_get (List.idxOf_lt_length_iff.2 (LawfulFold.mem_entries (xs := xs) h)))
  entries_eq := by
    let entries := NumLean.entries xs
    change entries = (List.finRange entries.length).map fun i => entries.get i
    simp [List.get_eq_getElem]

end FinRangeView

/-- Finite view of the zero-origin Nat range `0...n`. -/
def finViewZeroNat (n : Nat) : FinRangeView (0...n : Std.Rco Nat) where
  size := n
  fromFin i := i
  mem_fromFin i := by
    rw [Std.Rco.mem_iff]
    exact ⟨Nat.zero_le _, i.isLt⟩
  toFin a h := ⟨a, by
    rw [Std.Rco.mem_iff] at h
    exact h.2⟩
  toFin_fromFin i := by
    apply Fin.ext
    rfl
  fromFin_toFin a h := rfl
  entries_eq := by
    apply List.subtype_ext_of_map_val_eq
    change (rcoNativeEntries (0...n : Std.Rco Nat)).map Subtype.val =
      (List.map (fun i : Fin n => (⟨↑i, by
        rw [Std.Rco.mem_iff]
        exact ⟨Nat.zero_le ↑i, i.isLt⟩⟩ : {x : Nat // x ∈ (0...n : Std.Rco Nat)}))
        (List.finRange n)).map Subtype.val
    rw [rcoNativeEntries_zero_nat_map_val]
    simp [List.map_map, Function.comp_def]

theorem fold_zeroNat_eq_fin_foldl {β : Type u} (n : Nat) (init : β)
    (f : (i : Nat) → i ∈ (0...n : Std.Rco Nat) → β → β) :
    Fold.fold (0...n : Std.Rco Nat) init f =
      Fin.foldl (finViewZeroNat n).size
        (fun acc i => f ((finViewZeroNat n).fromFin i) ((finViewZeroNat n).mem_fromFin i) acc)
        init :=
  (finViewZeroNat n).fold_eq_fin_foldl init f

private theorem map_finRange_add_eq_range' (lo n : Nat) :
    (List.finRange n).map (fun i : Fin n => lo + i.1) = List.range' lo n := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [List.getElem_range']

/-- Finite view of the Nat range `lo...hi`. -/
def finViewNat (lo hi : Nat) : FinRangeView (lo...hi : Std.Rco Nat) where
  size := hi - lo
  fromFin i := lo + i
  mem_fromFin i := by
    rw [Std.Rco.mem_iff]
    change lo ≤ lo + i.1 ∧ lo + i.1 < hi
    constructor
    · exact Nat.le_add_right lo i
    · have hlt : i.1 < hi - lo := i.2
      omega
  toFin a h := ⟨a - lo, by
    rw [Std.Rco.mem_iff] at h
    change lo ≤ a ∧ a < hi at h
    omega⟩
  toFin_fromFin i := by
    apply Fin.ext
    simp
  fromFin_toFin a h := by
    rw [Std.Rco.mem_iff] at h
    change lo ≤ a ∧ a < hi at h
    change lo + (a - lo) = a
    omega
  entries_eq := by
    apply List.subtype_ext_of_map_val_eq
    change (rcoNativeEntries (lo...hi : Std.Rco Nat)).map Subtype.val =
      (List.map (fun i : Fin (hi - lo) => (⟨lo + ↑i, by
        rw [Std.Rco.mem_iff]
        change lo ≤ lo + i.1 ∧ lo + i.1 < hi
        constructor
        · exact Nat.le_add_right lo i
        · have hlt : i.1 < hi - lo := i.2
          omega⟩ : {x : Nat // x ∈ (lo...hi : Std.Rco Nat)}))
        (List.finRange (hi - lo))).map Subtype.val
    rw [rcoNativeEntries_nat_map_val]
    simpa [List.map_map, Function.comp_def] using
      (map_finRange_add_eq_range' lo (hi - lo)).symm

theorem fold_nat_eq_fin_foldl {β : Type u} (lo hi : Nat) (init : β)
    (f : (i : Nat) → i ∈ (lo...hi : Std.Rco Nat) → β → β) :
    Fold.fold (lo...hi : Std.Rco Nat) init f =
      Fin.foldl (finViewNat lo hi).size
        (fun acc i => f ((finViewNat lo hi).fromFin i) ((finViewNat lo hi).mem_fromFin i) acc)
        init :=
  (finViewNat lo hi).fold_eq_fin_foldl init f

/-- Entry-indexed finite view of an Int range.

This is already enough to rewrite an Int range fold to `Fin.foldl`.  A later refinement should expose
the closed-form size `(hi - lo).toNat` and `fromFin i = lo + i`. -/
def finViewInt (lo hi : Int) : FinRangeView (lo...hi : Std.Rco Int) :=
  FinRangeView.ofEntries

theorem fold_int_eq_fin_foldl {β : Type u} (lo hi : Int) (init : β)
    (f : (i : Int) → i ∈ (lo...hi : Std.Rco Int) → β → β) :
    Fold.fold (lo...hi : Std.Rco Int) init f =
      Fin.foldl (finViewInt lo hi).size
        (fun acc i => f ((finViewInt lo hi).fromFin i) ((finViewInt lo hi).mem_fromFin i) acc)
        init :=
  (finViewInt lo hi).fold_eq_fin_foldl init f

/-- Fallback conversion of any lawful fold to `Fin.foldl` by indexing its concrete `entries` list.

Prefer a range-specific theorem when available, since those usually expose simpler `fromFin` maps. -/
theorem fold_eq_fin_foldl_of_entries {ρ : Type u} {α : Type v}
    {d : Membership α ρ} [FoldEntries ρ α d] [Fold ρ] [LawfulFold ρ α d]
    {xs : ρ} [DecidableEq {a : α // a ∈ xs}] {β : Type w} (init : β)
    (f : (a : α) → a ∈ xs → β → β) :
    Fold.fold xs init f =
      Fin.foldl (FinRangeView.ofEntries (xs := xs)).size
        (fun acc i => f ((FinRangeView.ofEntries (xs := xs)).fromFin i)
          ((FinRangeView.ofEntries (xs := xs)).mem_fromFin i) acc)
        init :=
  (FinRangeView.ofEntries (xs := xs)).fold_eq_fin_foldl init f

end Fold

end NumLean
