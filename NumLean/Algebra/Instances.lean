import NumLean.Algebra.Ops

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential


namespace NumLean

instance [inst : AddGroup G] : AddGroupOps G where
  nsmul := inst.nsmul
  zsmul := inst.zsmul

instance [DivInvMonoid G] : GroupOps G where
  npow x n := x ^ n
  zpow x n := x ^ n

instance [Field K] : FieldOps K where

instance [Norm K] : RNorm K Real where
  rnorm x := ‖x‖

noncomputable instance [RCLike K] : RCLikeOps K Real where
  make re _ := re
  re := RCLike.re
  im := RCLike.im

noncomputable instance : RCOps Real Real where
  exp := Real.exp
  sin := Real.sin
  cos := Real.cos
  pow x y := x ^ y

noncomputable instance : ROps Real where
  log := Real.log
  sqrt := Real.sqrt

noncomputable instance : RCOps Complex Real where
  exp := Complex.exp
  sin := Complex.sin
  cos := Complex.cos
  pow x y := x ^ y

end NumLean
