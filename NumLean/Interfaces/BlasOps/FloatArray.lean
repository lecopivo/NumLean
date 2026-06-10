import NumLean.Interfaces.ArrayType.FloatArray
import NumLean.Interfaces.BlasOps.Basic

namespace NumLean


def _root_.FloatArray.axpby (n : Nat)
    (a : Float) (xs : FloatArray) (xoff xinc : Nat)
    (b : Float) (ys : FloatArray) (yoff yinc : Nat) : FloatArray := Id.run do
  let mut ys := ys
  for i in [0:n] do
    let xidx := xoff + i * xinc
    let yidx := yoff + i * yinc
    if h : xidx < xs.size ∧ yidx < ys.size then
      ys := ys.set yidx (a * xs[xidx] + b * ys[yidx])
    else
      break
  return ys

def _root_.FloatArray.scal (n : Nat) (a : Float) (xs : FloatArray) (xoff xinc : Nat) :
    FloatArray := Id.run do
  let mut xs := xs
  for i in [0:n] do
    let idx := xoff + i * xinc
    if h : idx < xs.size then
      xs := xs.set idx (a * xs[idx])
    else
      break
  return xs

instance : BLASOps FloatArray Float where
  axpby := FloatArray.axpby
  scal := FloatArray.scal

end NumLean
