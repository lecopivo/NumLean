import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real


namespace NumLean

class AddGroupOps (K : Type u) extends
  Add K, Sub K, Neg K, Zero K
  where
  nsmul : Nat → K → K
  zsmul : Int → K → K

instance [inst : AddGroupOps K] : SMul ℕ K := ⟨inst.nsmul⟩
instance [inst : AddGroupOps K] : SMul ℤ K := ⟨inst.zsmul⟩

instance [inst : AddGroup K] : AddGroupOps K where
  nsmul := inst.nsmul
  zsmul := inst.zsmul

example [AddGroupOps K] : SMul ℕ K := by infer_instance

class GroupOps (K : Type u) extends
  Mul K, Div K, Inv K, One K
  where
  npow : K → ℕ → K
  zpow : K → ℤ → K


instance [inst : GroupOps K] : Pow K Nat := ⟨inst.npow⟩
instance [inst : GroupOps K] : Pow K Int := ⟨inst.zpow⟩

instance [inst : Group K] : GroupOps K where
  npow := inst.npow
  zpow := inst.zpow

class FieldOps (K : Type u) extends
  AddGroupOps K, GroupOps K

instance [inst : Field K] : FieldOps K where
  npow := inst.npow
  zpow := inst.zpow

class RNorm (K : Type u) (R : outParam (Type v)) where
  rnorm : K → R

class RCLikeOps (K : Type u) (R : outParam (Type v)) extends
  FieldOps K, RNorm K R, Star K
  where
  make : R → R → K
  re : K → R
  im : K → R

instance [RCLike K] : RCLikeOps K ℝ where
  rnorm x := ‖x‖
  make x y := algebraMap ℝ _ x + algebraMap ℝ _ y
  re := RCLike.re
  im := RCLike.im

class RCOps (K : Type u) (R : outParam (Type v)) extends
  RCLikeOps K R
  where

  exp : K → K
  sin : K → K
  cos : K → K
  pow : K → K → K

noncomputable
instance : RCOps ℝ ℝ where

  exp := Real.exp
  sin := Real.sin
  cos := Real.cos
  pow x y := x ^ y

noncomputable
instance : RCOps ℂ ℝ where
  exp := Complex.exp
  sin := Complex.sin
  cos := Complex.cos
  pow x y := x ^ y

class ROps (R : Type u) extends
  RCOps R R, LT R, LE R --- ....
  where
  log : R → R
  sqrt : R → R

noncomputable
instance : ROps ℝ where
  log := Real.log
  sqrt := Real.sqrt

end NumLean
