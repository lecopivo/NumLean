import NumLean.Data.Vector.RingArrayOps.Basic

set_option backward.do.legacy false

open scoped BigOperators

namespace NumLean

namespace Vector

theorem dotRef_eq_range_sum [AddCommMonoid K] [Mul K] {xn yn : Nat} (n : Nat)
    (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) :
    dotRef n xs xoff xinc ys yoff yinc hx hy =
      ∑ i : Fin n,
        xs[xoff + i.1 * xinc]'(by exact TBounds.stride_lt hx.1 hx.2 i.2) *
          ys[yoff + i.1 * yinc]'(by exact TBounds.stride_lt hy.1 hy.2 i.2) := by
  sorry

theorem dotRef_full_eq_finset_sum [AddCommMonoid K] [Mul K] {n : Nat}
    (xs ys : Vector K n) :
    dotRef n xs 0 1 ys 0 1 (by simp) (by simp) = ∑ i : Fin n, xs[i] * ys[i] := by
  sorry

end Vector

end NumLean
