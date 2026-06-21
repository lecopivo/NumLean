import NumLean.Data.Vector.Basic
import NumLean.Interfaces.Algebra.RingArrayOps
import NumLean.Interfaces.Fold
import NumLean.Meta.ForAll
import NumLean.Tactic.TBounds

namespace NumLean

namespace Vector

set_option backward.do.legacy false

def axpyRef [Add K] [Mul K] {xn yn : Nat} (n : Nat)
    (a : K) (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : Vector K yn := Id.run do
  let mut ys := ys
  for h : i in 0...n do
    ys[yoff + i * yinc]'(by tbounds) :=
      ys[yoff + i * yinc]'(by tbounds) + a * xs[xoff + i * xinc]'(by tbounds)
  return ys

def scalRef [Mul K] {xn : Nat} (n : Nat) (a : K) (xs : Vector K xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) : Vector K xn := Id.run do
  let mut xs := xs
  for h : i in 0...n do
    xs[xoff + i * xinc]'(by tbounds) := a * xs[xoff + i * xinc]'(by tbounds)
  return xs

def mulRef [Mul K] {xn yn : Nat} (n : Nat)
    (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : Vector K yn := Id.run do
  let mut ys := ys
  for h : i in 0...n do
    ys[yoff + i * yinc]'(by tbounds) :=
      ys[yoff + i * yinc]'(by tbounds) * xs[xoff + i * xinc]'(by tbounds)
  return ys

def dotRef [Add K] [Mul K] [Zero K] {xn yn : Nat} (n : Nat)
    (xs : Vector K xn) (xoff xinc : Nat) (ys : Vector K yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0)
    (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) : K := Id.run do
  let mut r := 0
  for h : i in 0...n do
    r := r + xs[xoff + i * xinc]'(by tbounds) * ys[yoff + i * yinc]'(by tbounds)
  return r

def sumRef [Add K] [Zero K] {xn : Nat} (n : Nat) (xs : Vector K xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) : K := Id.run do
  let mut r := 0
  for h : i in 0...n do
    r := r + xs[xoff + i * xinc]'(by tbounds)
  return r

instance [Ring K] : RingArrayOps (Vector K) where
  axpy := axpyRef
  scal := scalRef
  mul := mulRef
  dot := dotRef
  sum := sumRef

instance [Ring K] : LawfulRingArrayOps (Vector K) where
  axpy_spec _ _ _ _ _ _ _ _ _ _ := rfl
  scal_spec _ _ _ _ _ _ := rfl
  mul_spec _ _ _ _ _ _ _ _ _ := rfl
  dot_spec _ _ _ _ _ _ _ _ _ := rfl
  sum_spec _ _ _ _ _ := rfl

end Vector

end NumLean
