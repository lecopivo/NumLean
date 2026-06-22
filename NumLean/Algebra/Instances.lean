import NumLean.Algebra.Ops
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
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans
  lt_iff_le_not_ge := fun _ _ => lt_iff_le_not_ge
  le_antisymm := fun _ _ => le_antisymm
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
  le z w := z = w
  lt _ _ := False
  le_refl _ := rfl
  le_trans _ _ _ hxy hyz := Eq.trans hxy hyz
  lt_iff_le_not_ge := by simp
  le_antisymm _ _ hzw _ := hzw
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
