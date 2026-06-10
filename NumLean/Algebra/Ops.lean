import Mathlib.Algebra.Notation.Defs

namespace NumLean

class AddGroupOps (K : Type u) extends
  Add K, Sub K, Neg K, Zero K
  where
  nsmul : Nat → K → K
  zsmul : Int → K → K

instance [inst : AddGroupOps K] : SMul Nat K := ⟨inst.nsmul⟩
instance [inst : AddGroupOps K] : SMul Int K := ⟨inst.zsmul⟩

class GroupOps (K : Type u) extends
  Mul K, Div K, Inv K, One K
  where
  npow : K → Nat → K
  zpow : K → Int → K

instance [inst : GroupOps K] : NatPow K := ⟨inst.npow⟩
instance [inst : GroupOps K] : Pow K Int := ⟨inst.zpow⟩

class FieldOps (K : Type u) extends
  AddGroupOps K, GroupOps K

class RNorm (K : Type u) (R : outParam (Type v)) where
  rnorm : K → R

class RCLikeOps (K : Type u) (R : outParam (Type v)) extends
  FieldOps K, RNorm K R, Star K
  where
  make : R → R → K
  re : K → R
  im : K → R

class RCOps (K : Type u) (R : outParam (Type v)) extends
  RCLikeOps K R
  where

  exp : K → K
  sin : K → K
  cos : K → K
  pow : K → K → K

class ROps (R : Type u) extends
  RCOps R R, LT R, LE R --- ....
  where
  log : R → R
  sqrt : R → R

end NumLean
