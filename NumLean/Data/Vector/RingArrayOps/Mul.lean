import NumLean.Data.Vector.RingArrayOps.Basic

set_option backward.do.legacy false

namespace NumLean

namespace Vector

theorem mulRef_in_range [Mul K] {xn yn : Nat} (n : Nat)
    (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0)
    (i : Nat) (hi : i ∈ (0...n : Std.Rco Nat)) :
    (mulRef n xs xoff xinc ys yoff yinc hx hy)[yoff + i * yinc]'(by tbounds) =
      ys[yoff + i * yinc]'(by tbounds) * xs[xoff + i * xinc]'(by tbounds) := by
  sorry

theorem mulRef_out_range [Mul K] {xn yn : Nat} (n : Nat)
    (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0)
    (j : Nat) (hj : j < yn) (hjout : ∀ i, i ∈ (0...n : Std.Rco Nat) → j ≠ yoff + i * yinc) :
    (mulRef n xs xoff xinc ys yoff yinc hx hy)[j] = ys[j] := by
  sorry

theorem mulRef_full_ext [Mul K] {n : Nat} (xs ys : Vector K n) (i : Fin n) :
    (mulRef n xs 0 1 ys 0 1 (by simp) (by simp))[i] = ys[i] * xs[i] := by
  sorry

theorem mulRef_full_eq_ofFn [Mul K] {n : Nat} (xs ys : Vector K n) :
    mulRef n xs 0 1 ys 0 1 (by simp) (by simp) =
      Vector.ofFn (fun i : Fin n => ys[i] * xs[i]) := by
  sorry

end Vector

end NumLean
