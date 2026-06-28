module

public import NumLean.Interfaces.Algebra.RNorm
public import NumLean.Interfaces.Algebra.RCLike.Basic

@[expose] public section

namespace NumLean

def ratToFloat (q : ℚ) : Float :=
  q.num.toInt64.toFloat / q.den.toFloat

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

end NumLean
