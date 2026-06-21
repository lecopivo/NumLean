import NumLean.Data.Vector.RingArrayOps.Basic

set_option backward.do.legacy false

namespace NumLean


namespace Vector


theorem axpyRef_in_range [Add K] [Mul K] {xn yn : Nat} (n : Nat)
    (a : K) (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0)
    (i : Nat) (hi : i ∈ (0...n : Std.Rco Nat)) :
    (axpyRef n a xs xoff xinc ys yoff yinc hx hy)[yoff + i * yinc]'(by tbounds) =
      ys[yoff + i * yinc]'(by tbounds) + a * xs[xoff + i * xinc]'(by tbounds) := by
  sorry

theorem axpyRef_out_range [Add K] [Mul K] {xn yn : Nat} (n : Nat)
    (a : K) (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0)
    (j : Nat) (hj : j < yn) (hjout : ∀ i, i ∈ (0...n : Std.Rco Nat) → j ≠ yoff + i * yinc) :
    (axpyRef n a xs xoff xinc ys yoff yinc hx hy)[j] = ys[j] := by
  sorry

theorem axpyRef_full_ext [Add K] [Mul K] {n : Nat}
    (a : K) (xs ys : Vector K n) (i : Fin n) :
    (axpyRef n a xs 0 1 ys 0 1 (by simp) (by simp))[i] = ys[i] + a * xs[i] := by
  sorry

theorem axpyRef_full_eq_ofFn [Add K] [Mul K] {n : Nat} (a : K) (xs ys : Vector K n) :
    axpyRef n a xs 0 1 ys 0 1 (by simp) (by simp) =
      Vector.ofFn (fun i : Fin n => ys[i] + a * xs[i]) := by
  sorry

end Vector

end NumLean
