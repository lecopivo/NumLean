import NumLean.Algebra.Ops
import NumLean.Data.FloatP

namespace NumLean

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

instance : AddGroupOps Float where
  nsmul n x := n • x
  zsmul n x := n • x

instance : GroupOps Float where
  npow x n := x ^ n
  zpow x n := x ^ n

instance : FieldOps Float where

instance : Star Float where
  star x := x

instance : RNorm Float Float where
  rnorm := Float.abs

instance : RCLikeOps Float Float where
  make re _ := re
  re x := x
  im _ := 0

instance : RCOps Float Float where
  exp := Float.exp
  sin := Float.sin
  cos := Float.cos
  pow := Float.pow

instance : ROps Float where
  log := Float.log
  sqrt := Float.sqrt

instance : Inv Float32 where
  inv x := 1 / x

instance : NatPow Float32 where
  pow x n := x ^ n.toFloat32

instance : Pow Float32 Int where
  pow x n := x ^ n.toInt32.toFloat32

instance : SMul Nat Float32 where
  smul n x := n.toFloat32 * x

instance : SMul Int Float32 where
  smul n x := n.toInt32.toFloat32 * x

instance : AddGroupOps Float32 where
  nsmul n x := n • x
  zsmul n x := n • x

instance : GroupOps Float32 where
  npow x n := x ^ n
  zpow x n := x ^ n

instance : FieldOps Float32 where

instance : Star Float32 where
  star x := x

instance : RNorm Float32 Float32 where
  rnorm := Float32.abs

instance : RCLikeOps Float32 Float32 where
  make re _ := re
  re x := x
  im _ := 0

instance : RCOps Float32 Float32 where
  exp := Float32.exp
  sin := Float32.sin
  cos := Float32.cos
  pow := Float32.pow

instance : ROps Float32 where
  log := Float32.log
  sqrt := Float32.sqrt

end NumLean
