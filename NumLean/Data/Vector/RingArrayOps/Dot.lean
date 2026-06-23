import NumLean.Data.Vector.RingArrayOps.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option backward.do.legacy false

open scoped BigOperators

namespace NumLean

namespace Vector

private theorem List.foldl_add_eq_add_sum [AddCommMonoid K] (xs : List α) (f : α → K) (acc : K) :
    xs.foldl (fun acc a => acc + f a) acc = acc + (xs.map f).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, add_assoc]

private theorem List.foldl_add_eq_sum [AddCommMonoid K] (xs : List α) (f : α → K) :
    xs.foldl (fun acc a => acc + f a) 0 = (xs.map f).sum := by
  simpa using List.foldl_add_eq_add_sum xs f (0 : K)

private theorem foldEntries_sum_eq_fin_sum [AddCommMonoid K] {n : Nat}
    (f : {i : Nat // i ∈ (0...n : Std.Rco Nat)} → K) :
    (NumLean.entries (0...n : Std.Rco Nat)).foldl (fun acc i => acc + f i) 0 =
      ∑ i : Fin n, f (finEquivZeroRange n i) := by
  classical
  letI : Fintype {i : Nat // i ∈ (0...n : Std.Rco Nat)} :=
    Fintype.ofEquiv (Fin n) (finEquivZeroRange n)
  rw [List.foldl_add_eq_sum]
  change (List.map f (rcoNativeEntries (0...n : Std.Rco Nat))).sum =
    ∑ i : Fin n, f (finEquivZeroRange n i)
  rw [← List.sum_toFinset f (LawfulRcoNativeStep.entries_nodup (0...n : Std.Rco Nat))]
  rw [show (rcoNativeEntries (0...n : Std.Rco Nat)).toFinset = Finset.univ by
        ext idx
        simp [LawfulRcoNativeStep.mem_entries idx.2]]
  exact (Fintype.sum_equiv (finEquivZeroRange n)
    (fun i : Fin n => f (finEquivZeroRange n i)) f (by intro i; rfl)).symm

theorem dotRef_eq_range_sum [AddCommMonoid K] [Mul K] {xn yn : Nat} (n : Nat)
    (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) :
    dotRef n xs xoff xinc ys yoff yinc hx hy =
      ∑ i : Fin n,
        xs[xoff + i.1 * xinc]'(by exact TBounds.stride_lt hx.1 hx.2 i.2) *
          ys[yoff + i.1 * yinc]'(by exact TBounds.stride_lt hy.1 hy.2 i.2) := by
  unfold dotRef
  simp only [LawfulFold.fold_eq_foldl (ρ := Std.Rco Nat) (α := Nat)
    (d := (inferInstance : Membership Nat (Std.Rco Nat)))
    (xs := (0...n : Std.Rco Nat))]
  simp only [bind, Id.run, pure]
  rw [foldEntries_sum_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem dotRef_full_eq_finset_sum [AddCommMonoid K] [Mul K] {n : Nat}
    (xs ys : Vector K n) :
    dotRef n xs 0 1 ys 0 1 (by simp) (by simp) = ∑ i : Fin n, xs[i] * ys[i] := by
  simpa using dotRef_eq_range_sum n xs 0 1 ys 0 1 (by simp) (by simp)

end Vector

end NumLean
