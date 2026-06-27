import NumLean.Interfaces.Algebra.RNorm
import NumLean.Interfaces.Algebra.RCLike.Lawful

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential


namespace NumLean

instance [Norm K] : RNorm K Real where
  rnorm x := ‖x‖

noncomputable instance : RCOps Real Real where
  le := (· ≤ ·)
  lt := (· < ·)
  decLe := inferInstanceAs (DecidableRel (· ≤ · : Real → Real → Prop))
  decLt := inferInstanceAs (DecidableRel (· < · : Real → Real → Prop))
  smul x y := x * y
  algebraMap x := x
  make re _ := re
  re x := x
  im _ := 0
  I := 0
  cexp := Real.exp
  csin := Real.sin
  ccos := Real.cos
  cpow x y := x ^ y

noncomputable instance : ROps Real where
  exp := Real.exp
  sin := Real.sin
  cos := Real.cos
  pow x y := x ^ y
  log := Real.log
  sqrt := Real.sqrt

noncomputable instance : RCOps Real Complex where
  le z w := z.re ≤ w.re ∧ z.im == w.im
  lt z w := z.re < w.re ∧ z.im == w.im
  decLe := inferInstance
  decLt := inferInstance
  smul r z := (r : Complex) * z
  algebraMap r := r
  make := Complex.mk
  re := Complex.re
  im := Complex.im
  I := Complex.I
  cexp := Complex.exp
  csin := Complex.sin
  ccos := Complex.cos
  cpow x y := x ^ y

end NumLean
