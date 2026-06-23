import NumLean.Data.Vector.RingArrayOps.Basic
import NumLean.Interfaces.VectorType.Basic
import Mathlib.Algebra.Ring.Defs

namespace NumLean

/-- Fast BLAS-style operations for arrays of elements of a ring `K`. -/
class RingArrayOps (Ks : Nat → Type u) {K : Type w} [VectorType Ks K] where
  axpy {xn yn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : Ks yn

  scal {xn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) : Ks xn

  mul' {xn yn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : Ks yn

  dot {xn yn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : K

  sum {xn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) : K

open RingArrayOps VectorType Vector in
class LawfulRingArrayOps (Ks : Nat → Type) {K : Type} [VectorType Ks K]
    [RingArrayOps Ks] [Ring K] where
  axpy_spec {xn yn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) :
    axpy n a xs xoff xinc ys yoff yinc hx hy =
      fromVector (axpyRef (K := K) n a (toVector xs) xoff xinc (toVector ys) yoff yinc hx hy)

  scal_spec {xn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) :
    scal n a xs xoff xinc hx =
      fromVector (scalRef (K := K) n a (toVector xs) xoff xinc hx)

  mul_spec {xn yn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn)
    (yoff yinc : Nat) (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) :
    mul' (Ks := Ks) (K := K) n xs xoff xinc ys yoff yinc hx hy =
      fromVector (mulRef (K := K) n (toVector xs) xoff xinc (toVector ys) yoff yinc hx hy)

  dot_spec {xn yn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn)
    (yoff yinc : Nat) (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) :
    dot n xs xoff xinc ys yoff yinc hx hy =
      dotRef (K := K) n (toVector xs) xoff xinc (toVector ys) yoff yinc hx hy

  sum_spec {xn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) :
    sum n xs xoff xinc hx = sumRef (K := K) n (toVector xs) xoff xinc hx

end NumLean
