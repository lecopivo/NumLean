import NumLean.Data.Vector.RingArrayOps.Basic

set_option backward.do.legacy false

open scoped BigOperators

namespace NumLean

namespace Vector

theorem sumRef_eq_range_sum [AddCommMonoid K] {xn : Nat} (n : Nat)
    (xs : Vector K xn) (xoff xinc : Nat) (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) :
    sumRef n xs xoff xinc hx =
      ∑ i : Fin n, xs[xoff + i.1 * xinc]'(by exact TBounds.stride_lt hx.1 hx.2 i.2) := by
  sorry

theorem sumRef_full_eq_finset_sum [AddCommMonoid K] {n : Nat} (xs : Vector K n) :
    sumRef n xs 0 1 (by simp) = ∑ i : Fin n, xs[i] := by
  sorry

end Vector

end NumLean
