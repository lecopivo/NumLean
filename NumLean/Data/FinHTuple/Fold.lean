module

public import NumLean.Data.FinHTuple.Basic
public import NumLean.Data.FinHTuple.FinHTupleMap
public import NumLean.Interfaces.Fold
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Intervals

@[expose] public section

namespace NumLean

universe u

namespace FinHTuple

private theorem List.map_range_rowMajor_block (i m : Nat) :
    (List.range m).map (fun j => j + m * i) = List.Ico (m * i) (m * (i + 1)) := by
  rw [← List.Ico.zero_bot m]
  calc
    (List.Ico 0 m).map (fun j => j + m * i) = (List.Ico 0 m).map (fun j => m * i + j) := by
      apply List.map_congr_left
      intro j _
      omega
    _ = List.Ico (0 + m * i) (m + m * i) := by
      exact List.Ico.map_add 0 m (m * i)
    _ = List.Ico (m * i) (m * (i + 1)) := by
      rw [Nat.zero_add, Nat.mul_succ, Nat.add_comm]

private theorem List.range_flatMap_rowMajor (n m : Nat) :
    (List.range n).flatMap (fun i => (List.range m).map (fun j => j + m * i)) =
      List.range (m * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      simp [List.map_range_rowMajor_block]
      rw [← List.Ico.zero_bot (m * n), ← List.Ico.zero_bot (m * (n + 1))]
      exact List.Ico.append_consecutive (Nat.zero_le (m * n))
        (Nat.mul_le_mul_left m (Nat.le_succ n))

private theorem List.range_flatMap_rowMajor_outer (n m : Nat) :
    (List.range n).flatMap (fun i => (List.range m).map (fun j => j + m * i)) =
      List.range (n * m) := by
  rw [List.range_flatMap_rowMajor, Nat.mul_comm]

private theorem List.map_flatMap' {α : Type u} {β : Type v} {γ : Type w}
    (xs : List α) (f : α → List β) (g : β → γ) :
    (xs.flatMap f).map g = xs.flatMap (fun x => (f x).map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem List.map_append' {α : Type u} {β : Type v}
    (xs ys : List α) (f : α → β) :
    (xs ++ ys).map f = xs.map f ++ ys.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Row-major equivalence between the zero-origin tuple range `0...ns` and the scalar range
`0...ns.numel`. -/
def zeroRangeEquivFin {p : HTuple.Profile} (ns : HTuple Nat p) :
    {idx : HTuple Nat p // idx ∈ ((0 : HTuple Nat p)...ns)} ≃
      {i : Nat // i ∈ (0...ns.numel : Std.Rco Nat)} :=
  (zeroRangeEquivFlatFin ns).trans (finEquivZeroRange ns.numel)

/-- Unordered range equivalence between a zero-origin tuple range and its row-major scalar range. -/
def zeroRangeRangeEquivFin {p : HTuple.Profile} (ns : HTuple Nat p) :
    Fold.RangeEquiv
      ((0 : HTuple Nat p)...ns)
      (0...ns.numel : Std.Rco Nat) :=
  Fold.RangeEquiv.ofSubtypeEquivAll (zeroRangeEquivFin ns)

open Classical in
theorem sum_zeroRange_eq_fin {p : HTuple.Profile} {M : Type u} [AddCommMonoid M]
    (ns : HTuple Nat p)
    (f : {idx : HTuple Nat p // idx ∈ ((0 : HTuple Nat p)...ns)} → M) :
    (∑ idx ∈ (NumLean.entries ((0 : HTuple Nat p)...ns)).toFinset, f idx) =
      ∑ i : Fin ns.numel,
        let idx := (equivFin ns).symm i
        f ⟨idx, val_mem_zero_shape idx⟩ := by
  classical
  let r : Std.Rco (HTuple Nat p) := (0 : HTuple Nat p)...ns
  let e := zeroRangeEquivFlatFin ns
  let s : Finset {idx : HTuple Nat p // idx ∈ r} := (NumLean.entries r).toFinset
  change (∑ idx ∈ s, f idx) =
    ∑ i ∈ (Finset.univ : Finset (Fin ns.numel)),
      let idx := (equivFin ns).symm i
      f ⟨idx, val_mem_zero_shape idx⟩
  refine Finset.sum_bij'
    (fun idx _ => e idx)
    (fun i _ => e.symm i)
    ?_ ?_ ?_ ?_ ?_
  · intro idx hidx
    simp
  · intro i _
    simpa [s] using
      ((inferInstance : LawfulFold.{0, 0, 0} (Std.Rco (HTuple Nat p)) (HTuple Nat p)
        HTuple.Range.instMembershipRcoHTuple).mem_entries (xs := r) (e.symm i).2)
  · intro idx hidx
    simp [e]
  · intro i _
    simp [e]
  · intro idx hidx
    cases idx with
    | mk idx hmem =>
        have hfin : (equivFin ns).symm (e ⟨idx, hmem⟩) = equivZeroRange ns ⟨idx, hmem⟩ := by
          simp [e, zeroRangeEquivFlatFin]
        simp [hfin, equivZeroRange]


end FinHTuple

namespace Fold

/-- Entry-indexed finite view of a zero-origin HTuple range.

This gives an immediate ordered bridge from `Fold.fold (0...shape)` to `Fin.foldl`.  The view is
entry-indexed; a later refinement should expose the closed-form row-major map
`(FinHTuple.equivFin shape).symm`. -/
def finViewZeroHTuple {p : HTuple.Profile} (shape : HTuple Nat p)
    [DecidableEq {idx : HTuple Nat p // idx ∈ ((0 : HTuple Nat p)...shape)}] :
    Fold.FinRangeView ((0 : HTuple Nat p)...shape) :=
  Fold.FinRangeView.ofEntries

theorem fold_zeroHTuple_eq_fin_foldl {p : HTuple.Profile} (shape : HTuple Nat p)
    [DecidableEq {idx : HTuple Nat p // idx ∈ ((0 : HTuple Nat p)...shape)}]
    {β : Type u} (init : β)
    (f : (idx : HTuple Nat p) → idx ∈ ((0 : HTuple Nat p)...shape) → β → β) :
    Fold.fold ((0 : HTuple Nat p)...shape) init f =
      Fin.foldl (finViewZeroHTuple shape).size
        (fun acc i => f ((finViewZeroHTuple shape).fromFin i)
          ((finViewZeroHTuple shape).mem_fromFin i) acc)
        init :=
  (finViewZeroHTuple shape).fold_eq_fin_foldl init f

open Classical Function in
theorem fold_layout_ext {r : HTuple.Profile} {shape : HTuple Nat r}
    {α : Type u} {n : Nat} (map : FinHTupleMap shape h(n)) (init : Vector α n)
    (hmap : map.Injective)
    (f : (i : HTuple ℕ r) → (i <ₑ shape) → α → α)
    (j : Nat) (hj : j < n) :
    getElem (Fold.fold (0...shape) (init := init) (fun i hi xs =>
      xs.set (map i : Nat)
        (f i (by grind) (getElem xs (map i) (by simpa using map.inBounds i (by grind))))
        (by simpa using map.inBounds i (by grind)))) j hj
    =
    if hj : j ∈ map.rangeNat then
      let ⟨i, hi⟩ := map.rangeNatInv j hj
      f i hi init[j]
    else
      init[j] := by
  let imap : (i : HTuple Nat r) → i ∈ ((0 : HTuple Nat r)...shape) → Nat := fun i _ => (map i : Nat)
  let f' : (i : HTuple Nat r) → i ∈ ((0 : HTuple Nat r)...shape) → α → α := fun i hi x => f i (by grind) x
  have himap : ∀ i hi, imap i hi < n := by
    intro i hi
    exact FinHTupleMap.mem_rangeNat_lt (f := map) (by exact ⟨⟨i, by grind⟩, rfl⟩)
  have himap' : Injective (fun i : {i' // i' ∈ ((0 : HTuple Nat r)...shape)} => imap i.1 i.2) := by
    intro a b hab
    apply Subtype.ext
    have hfin : (⟨a.1, by grind⟩ : FinHTuple shape) = ⟨b.1, by grind⟩ := by
      apply hmap
      apply FinHTuple.ext
      apply HTuple.toScalar_injective
      simpa [imap] using hab
    exact congrArg FinHTuple.val hfin
  have hfold := Fold.fold_ext
    (range := ((0 : HTuple Nat r)...shape))
    (imap := imap) (f := f') (init := init)
    (himap := himap) (himap' := himap')
  change getElem (Fold.fold (0...shape) (init := init) (fun i hi xs =>
      xs.set (imap i hi) (f' i hi (getElem xs (imap i hi) (himap i hi))) (by grind))) j hj = _
  rw [hfold]
  rw [Vector.getElem_mapFinIdx]
  by_cases h : j ∈ map.rangeNat
  · have hset : j ∈ Set.range (fun i : {i' // i' ∈ ((0 : HTuple Nat r)...shape)} => imap i.1 i.2) := by
      rw [map.mem_rangeNat_iff_mem_range_indexFun] at h
      simpa [imap, FinHTupleMap.indexFun] using h
    haveI : Nonempty {i' // i' ∈ ((0 : HTuple Nat r)...shape)} := by
      rcases hset with ⟨i, _⟩
      exact ⟨i⟩
    have hinv : invFun (fun i : {i' // i' ∈ ((0 : HTuple Nat r)...shape)} => imap i.1 i.2) j =
        ⟨(map.rangeNatInv j h).val, FinHTuple.val_mem_zero_shape _⟩ := by
      simpa [imap, FinHTupleMap.indexFun] using map.invFun_indexFun_eq_rangeNatInv j h hmap
    simp only [hset, h, dif_pos, hinv, f']
  · have hset : ¬ j ∈ Set.range (fun i : {i' // i' ∈ ((0 : HTuple Nat r)...shape)} => imap i.1 i.2) := by
      intro hset
      apply h
      rw [map.mem_rangeNat_iff_mem_range_indexFun]
      simpa [imap, FinHTupleMap.indexFun] using hset
    simp [hset, h]

end Fold

end NumLean
