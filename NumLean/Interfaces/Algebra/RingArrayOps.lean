import NumLean.Data.Vector.RingArrayOps.Basic
import NumLean.Interfaces.VectorType.Basic
import Mathlib.Algebra.Ring.Defs

namespace NumLean

/-- Fast operations for arrays of elements of a ring `K`. -/
class RingArrayOps (Ks : Nat → Type u) {K : Type w} [VectorType Ks K] where

  /-- Computes BLAS operation `axpy`:

  ```
  for i in 0...n do
    ys[yoff + i * yinc] += a * xs[xoff + i * xinc]
  ```

  This function is used to define addition and subtraction on arrays and subarrays:
    - `xs + ys = axpy n 1 ys 0 1 xs 0 1`
    - `xs - ys = axpy n - ys 0 1 xs 0 1`

  Addition is defined with reversed operands because `axpy` mutates its second argument. Thus
  `xs + ys + zs` is bracketed as `(xs + ys) + zs`, and the second addition mutates the temporary
  result `(xs + ys)`.

  We forbid `yinc = 0` such that implementation can execute the loop in parallel without any synchronization or atomics.
  -/
  axpy {xn yn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : Ks yn

  /-- Computes BLAS operation `scal`:

  ```
  for i in 0...n do
    xs[xoff + i * xinc] += a
  ```

  This function is use to define negation and scalar multiplication:
    - `- xs = scal n (-1) xs 0 1`
    - `a • xs = scal n a xs 0 1`

  We forbid `xinc = 0` such that implementation can execute the loop in parallel without any synchronization or atomics.
  -/
  scal {xn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) : Ks xn


  /-- Computes elementwise multiplication of a strided slice:

  ```
  for i in 0...n do
    ys[yoff + i * yinc] *= xs[xoff + i * xinc]
  ```

  This function is used to define multiplication on arrays and subarrays:
    - `xs * ys = mul n ys 0 1 xs 0 1`

  Note that this mutates the second argument for the same associativity reason as `axpy`.

  We forbid `yinc = 0` such that implementation can execute the loop in parallel without any synchronization or atomics.
  -/
  mul {xn yn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : Ks yn

  /-- Computes the dot product of two strided slices:

  ```
  let mut r := 0
  for i in 0...n do
    r += xs[xoff + i * xinc] * ys[yoff + i * yinc]
  ```
  -/
  dot {xn yn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : K

  /-- Computes the sum of a strided slice:

  ```
  let mut r := 0
  for i in 0...n do
    r += xs[xoff + i * xinc]
  ```
  -/
  sum {xn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) : K


open RingArrayOps VectorType Vector in
class LawfulRingArrayOps (Ks : Nat → Type) {K : Type} [VectorType Ks K]
    [RingArrayOps Ks] [Ring K] where

  axpy_spec {xn yn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) :
    axpy n a xs xoff xinc ys yoff yinc hx hy
    =
    fromVector (axpyRef (K := K) n a (toVector xs) xoff xinc (toVector ys) yoff yinc hx hy)

  scal_spec {xn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) :
    scal n a xs xoff xinc hx =
      fromVector (scalRef (K := K) n a (toVector xs) xoff xinc hx)

  mul_spec {xn yn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn)
    (yoff yinc : Nat) (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) :
    mul (Ks := Ks) (K := K) n xs xoff xinc ys yoff yinc hx hy =
      fromVector (mulRef (K := K) n (toVector xs) xoff xinc (toVector ys) yoff yinc hx hy)

  dot_spec {xn yn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn)
    (yoff yinc : Nat) (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) :
    dot n xs xoff xinc ys yoff yinc hx hy =
      dotRef (K := K) n (toVector xs) xoff xinc (toVector ys) yoff yinc hx hy

  sum_spec {xn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) :
    sum n xs xoff xinc hx = sumRef (K := K) n (toVector xs) xoff xinc hx
