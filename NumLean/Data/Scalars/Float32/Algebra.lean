import NumLean.Data.Scalars.Float32.Basic
import NumLean.Data.Scalars.Float64.Algebra

namespace NumLean

instance : Inv Float32 where
  inv x := 1 / x

instance : NatCast Float32 where
  natCast n := n.toFloat32

instance : IntCast Float32 where
  intCast n := n.toInt32.toFloat32

private def ratToFloat32 (q : ℚ) : Float32 :=
  q.num.toInt32.toFloat32 / q.den.toFloat32

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
  le x y := x ≤ y
  lt x y := x < y
  decLe := inferInstance
  decLt := inferInstance
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
