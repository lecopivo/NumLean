import Mathlib.Analysis.RCLike.Basic

namespace NumLean

variable {K} [Add K] [Mul K] [Inhabited K]

def _root_.Array.axpby (n : Nat)
    (a : K) (xs : Array K) (xoff xinc : Nat)
    (b : K) (ys : Array K) (yoff yinc : Nat) : Array K := Id.run do
  let mut ys := ys
  for i in [0:n] do
    let xidx := xoff + i * xinc
    let yidx := yoff + i * yinc
    if h : xidx < xs.size ∧ yidx < ys.size then
      ys := ys.set yidx (a * xs[xidx] + b * ys[yidx])
    else
      break
  return ys

def _root_.Array.scal (n : Nat) (a : K) (xs : Array K) (xoff xinc : Nat) : Array K := Id.run do
  let mut xs := xs
  for i in [0:n] do
    let idx := xoff + i * xinc
    if h : idx < xs.size then
      xs := xs.set idx (a * xs[idx])
    else
      break
  return xs


end NumLean
