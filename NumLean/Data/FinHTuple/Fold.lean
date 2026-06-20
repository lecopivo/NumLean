import NumLean.Data.FinHTuple.Basic
import NumLean.Interfaces.Fold
import Mathlib.Data.List.Intervals

namespace NumLean

namespace FinHTuple

namespace List

private theorem subtype_ext_of_map_val_eq {α : Type u} {p : α → Prop}
    {xs ys : List {x : α // p x}}
    (h : xs.map Subtype.val = ys.map Subtype.val) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons] at h
          injection h with hxy htail
          have hxy' : x = y := Subtype.ext hxy
          subst hxy'
          simp [ih htail]

end List

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


end FinHTuple

end NumLean
