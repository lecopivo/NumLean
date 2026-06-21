import NumLean.Data.Vector.Basic
import NumLean.Interfaces.VectorType.Basic
import NumLean.Tactic.TBounds
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


def axpySpec [Add K] [Mul K] {xn yn : Nat} (n : Nat)
    (a : K) (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : Vector K yn := Id.run do
  let mut ys := ys
  for h : i in 0...n do
    ys[yoff + i * yinc]'(by tbounds) := ys[yoff + i * yinc]'(by tbounds) +  a * xs[xoff + i * xinc]'(by tbounds)
  return ys

def scalSpec [Mul K] {xn : Nat} (n : Nat) (a : K) (xs : Vector K xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) : Vector K xn := Id.run do
  let mut xs := xs
  for h : i in 0...n do
    xs[xoff + i * xinc]'(by tbounds) := a * xs[xoff + i * xinc]'(by tbounds)
  return xs

def mulSpec [Mul K] {xn yn : Nat} (n : Nat)
    (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : Vector K yn := Id.run do
  let mut ys := ys
  for h : i in 0...n do
    ys[yoff + i * yinc]'(by tbounds) :=
      ys[yoff + i * yinc]'(by tbounds) * xs[xoff + i * xinc]'(by tbounds)
  return ys

def dotSpec [Add K] [Mul K] [Zero K] {xn yn : Nat} (n : Nat)
    (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : K := Id.run do
  let mut r := 0
  for h : i in 0...n do
    r := r + xs[xoff + i * xinc]'(by tbounds) * ys[yoff + i * yinc]'(by tbounds)
  return r

def sumSpec [Add K] [Zero K] {xn : Nat} (n : Nat) (xs : Vector K xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) : K := Id.run do
  let mut r := 0
  for h : i in 0...n do
    r := r + xs[xoff + i * xinc]'(by tbounds)
  return r

open RingArrayOps VectorType in
class LawfulRingArrayOps (Ks : Nat → Type) {K : Type} [VectorType Ks K]
    [RingArrayOps Ks] [Ring K] where

  axpy_spec {xn yn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) :
    RingArrayOps.axpy n a xs xoff xinc ys yoff yinc hx hy
    =
    fromVector (axpySpec (K:=K) n a (toVector xs) xoff xinc (toVector ys) yoff yinc hx hy)

  scal_spec {xn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) :
    RingArrayOps.scal n a xs xoff xinc hx =
      fromVector (scalSpec (K := K) n a (toVector xs) xoff xinc hx)

  mul_spec {xn yn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn)
    (yoff yinc : Nat) (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) :
    RingArrayOps.mul (Ks := Ks) (K := K) n xs xoff xinc ys yoff yinc hx hy =
      fromVector (mulSpec (K := K) n (toVector xs) xoff xinc (toVector ys) yoff yinc hx hy)

  dot_spec {xn yn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn)
    (yoff yinc : Nat) (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) :
    RingArrayOps.dot n xs xoff xinc ys yoff yinc hx hy =
      dotSpec (K := K) n (toVector xs) xoff xinc (toVector ys) yoff yinc hx hy

  sum_spec {xn : Nat} (n : Nat) (xs : Ks xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) :
    RingArrayOps.sum n xs xoff xinc hx = sumSpec (K := K) n (toVector xs) xoff xinc hx
