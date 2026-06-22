import NumLean.Algebra.Ops
import NumLean.Interfaces.Algebra.RCLike.Basic

namespace NumLean

private def ratToFloat (q : ℚ) : Float :=
  q.num.toInt64.toFloat / q.den.toFloat

private def ratToFloat32 (q : ℚ) : Float32 :=
  (ratToFloat q).toFloat32

instance : NatCast Float where
  natCast n := n.toFloat

instance : IntCast Float where
  intCast n := n.toInt64.toFloat

instance : NNRatCast Float where
  nnratCast q := ratToFloat q.1

instance : RatCast Float where
  ratCast := ratToFloat

instance : Inv Float where
  inv x := 1 / x

instance : NatPow Float where
  pow x n := x ^ n.toFloat

instance : Pow Float Int where
  pow x n := x ^ n.toInt64.toFloat

instance : SMul Nat Float where
  smul n x := n.toFloat * x

instance : SMul Int Float where
  smul n x := n.toInt64.toFloat * x

instance : SMul Float Float where
  smul x y := x * y

instance : AddGroupOps Float where
  nsmul n x := n • x
  zsmul n x := n • x

instance : GroupOps Float where
  npow n x := x ^ n
  zpow n x := x ^ n

instance : FieldOps Float where
  nnqsmul q x := (q : Float) * x
  qsmul q x := (q : Float) * x

instance : Star Float where
  star x := x

instance : RNorm Float Float where
  rnorm := Float.abs

instance : RCOps Float Float where
  le x y := x = y
  lt _ _ := False
  le_refl _ := rfl
  le_trans _ _ _ hxy hyz := Eq.trans hxy hyz
  lt_iff_le_not_ge := by simp
  le_antisymm _ _ hxy _ := hxy
  smul x y := x * y
  algebraMap x := x
  make re _ := re
  re x := x
  im _ := 0
  I := 0
  cexp := Float.exp
  csin := Float.sin
  ccos := Float.cos
  cpow := Float.pow

instance : ROps Float where
  exp := Float.exp
  sin := Float.sin
  cos := Float.cos
  pow := Float.pow
  log := Float.log
  sqrt := Float.sqrt

instance : Inv Float32 where
  inv x := 1 / x

instance : NatCast Float32 where
  natCast n := n.toFloat32

instance : IntCast Float32 where
  intCast n := n.toInt32.toFloat32

instance : NNRatCast Float32 where
  nnratCast q := ratToFloat32 q.1

instance : RatCast Float32 where
  ratCast := ratToFloat32

instance : NatPow Float32 where
  pow x n := x ^ n.toFloat32

instance : Pow Float32 Int where
  pow x n := x ^ n.toInt32.toFloat32

instance : SMul Nat Float32 where
  smul n x := n.toFloat32 * x

instance : SMul Int Float32 where
  smul n x := n.toInt32.toFloat32 * x

instance : SMul Float32 Float32 where
  smul x y := x * y

instance : AddGroupOps Float32 where
  nsmul n x := n • x
  zsmul n x := n • x

instance : GroupOps Float32 where
  npow n x := x ^ n
  zpow n x := x ^ n

instance : FieldOps Float32 where
  nnqsmul q x := (q : Float32) * x
  qsmul q x := (q : Float32) * x

instance : Star Float32 where
  star x := x

instance : RNorm Float32 Float32 where
  rnorm := Float32.abs

instance : RCOps Float32 Float32 where
  le x y := x = y
  lt _ _ := False
  le_refl _ := rfl
  le_trans _ _ _ hxy hyz := Eq.trans hxy hyz
  lt_iff_le_not_ge := by simp
  le_antisymm _ _ hxy _ := hxy
  smul x y := x * y
  algebraMap x := x
  make re _ := re
  re x := x
  im _ := 0
  I := 0
  cexp := Float32.exp
  csin := Float32.sin
  ccos := Float32.cos
  cpow := Float32.pow

instance : ROps Float32 where
  exp := Float32.exp
  sin := Float32.sin
  cos := Float32.cos
  pow := Float32.pow
  log := Float32.log
  sqrt := Float32.sqrt

end NumLean
