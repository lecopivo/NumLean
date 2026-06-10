import NumLean.Algebra.Float
import NumLean.Data.Complex

namespace NumLean

namespace Complex32

protected def abs (z : Complex32) : Float32 :=
  Float32.sqrt (z.re * z.re + z.im * z.im)

protected def log (z : Complex32) : Complex32 :=
  ⟨Float32.log z.abs, Float32.atan2 z.im z.re⟩

protected def exp (z : Complex32) : Complex32 :=
  let r := Float32.exp z.re
  ⟨r * Float32.cos z.im, r * Float32.sin z.im⟩

protected def sin (z : Complex32) : Complex32 :=
  ⟨Float32.sin z.re * Float32.cosh z.im,
    Float32.cos z.re * Float32.sinh z.im⟩

protected def cos (z : Complex32) : Complex32 :=
  ⟨Float32.cos z.re * Float32.cosh z.im,
    -(Float32.sin z.re * Float32.sinh z.im)⟩

end Complex32

instance : Add Complex32 where
  add := fun ⟨x, y⟩ ⟨x', y'⟩ => ⟨x + x', y + y'⟩

instance : Sub Complex32 where
  sub := fun ⟨x, y⟩ ⟨x', y'⟩ => ⟨x - x', y - y'⟩

instance : Neg Complex32 where
  neg := fun ⟨x, y⟩ => ⟨-x, -y⟩

instance : Zero Complex32 where
  zero := ⟨0, 0⟩

instance : One Complex32 where
  one := ⟨1, 0⟩

instance : Mul Complex32 where
  mul := fun ⟨a, b⟩ ⟨c, d⟩ => ⟨a * c - b * d, a * d + b * c⟩

instance : Inv Complex32 where
  inv := fun ⟨a, b⟩ =>
    let denom := a * a + b * b
    ⟨a / denom, -b / denom⟩

instance : Div Complex32 where
  div z w := z * w⁻¹

instance : Star Complex32 where
  star := fun ⟨a, b⟩ => ⟨a, -b⟩

private def npowRecComplex32 : Complex32 → Nat → Complex32
  | _, 0 => 1
  | z, n + 1 => npowRecComplex32 z n * z

private def zpowRecComplex32 : Complex32 → Int → Complex32
  | z, .ofNat n => npowRecComplex32 z n
  | z, .negSucc n => (npowRecComplex32 z (n + 1))⁻¹

instance : NatPow Complex32 where
  pow := npowRecComplex32

instance : Pow Complex32 Int where
  pow := zpowRecComplex32

instance : SMul Nat Complex32 where
  smul n z := ⟨n • z.re, n • z.im⟩

instance : SMul Int Complex32 where
  smul n z := ⟨n • z.re, n • z.im⟩

instance : AddGroupOps Complex32 where
  nsmul n z := n • z
  zsmul n z := n • z

instance : GroupOps Complex32 where
  npow z n := z ^ n
  zpow z n := z ^ n

instance : FieldOps Complex32 where

instance : RNorm Complex32 Float32 where
  rnorm := Complex32.abs

instance : RCLikeOps Complex32 Float32 where
  make re im := ⟨re, im⟩
  re := Complex32.re
  im := Complex32.im

instance : RCOps Complex32 Float32 where
  exp := Complex32.exp
  sin := Complex32.sin
  cos := Complex32.cos
  pow z w := Complex32.exp (w * Complex32.log z)

namespace Complex64

protected def abs (z : Complex64) : Float :=
  Float.sqrt (z.re * z.re + z.im * z.im)

protected def log (z : Complex64) : Complex64 :=
  ⟨Float.log z.abs, Float.atan2 z.im z.re⟩

protected def exp (z : Complex64) : Complex64 :=
  let r := Float.exp z.re
  ⟨r * Float.cos z.im, r * Float.sin z.im⟩

protected def sin (z : Complex64) : Complex64 :=
  ⟨Float.sin z.re * Float.cosh z.im,
    Float.cos z.re * Float.sinh z.im⟩

protected def cos (z : Complex64) : Complex64 :=
  ⟨Float.cos z.re * Float.cosh z.im,
    -(Float.sin z.re * Float.sinh z.im)⟩

end Complex64

instance : Add Complex64 where
  add := fun ⟨x, y⟩ ⟨x', y'⟩ => ⟨x + x', y + y'⟩

instance : Sub Complex64 where
  sub := fun ⟨x, y⟩ ⟨x', y'⟩ => ⟨x - x', y - y'⟩

instance : Neg Complex64 where
  neg := fun ⟨x, y⟩ => ⟨-x, -y⟩

instance : Zero Complex64 where
  zero := ⟨0, 0⟩

instance : One Complex64 where
  one := ⟨1, 0⟩

instance : Mul Complex64 where
  mul := fun ⟨a, b⟩ ⟨c, d⟩ => ⟨a * c - b * d, a * d + b * c⟩

instance : Inv Complex64 where
  inv := fun ⟨a, b⟩ =>
    let denom := a * a + b * b
    ⟨a / denom, -b / denom⟩

instance : Div Complex64 where
  div z w := z * w⁻¹

instance : Star Complex64 where
  star := fun ⟨a, b⟩ => ⟨a, -b⟩

private def npowRecComplex64 : Complex64 → Nat → Complex64
  | _, 0 => 1
  | z, n + 1 => npowRecComplex64 z n * z

private def zpowRecComplex64 : Complex64 → Int → Complex64
  | z, .ofNat n => npowRecComplex64 z n
  | z, .negSucc n => (npowRecComplex64 z (n + 1))⁻¹

instance : NatPow Complex64 where
  pow := npowRecComplex64

instance : Pow Complex64 Int where
  pow := zpowRecComplex64

instance : SMul Nat Complex64 where
  smul n z := ⟨n • z.re, n • z.im⟩

instance : SMul Int Complex64 where
  smul n z := ⟨n • z.re, n • z.im⟩

instance : AddGroupOps Complex64 where
  nsmul n z := n • z
  zsmul n z := n • z

instance : GroupOps Complex64 where
  npow z n := z ^ n
  zpow z n := z ^ n

instance : FieldOps Complex64 where

instance : RNorm Complex64 Float where
  rnorm := Complex64.abs

instance : RCLikeOps Complex64 Float where
  make re im := ⟨re, im⟩
  re := Complex64.re
  im := Complex64.im

instance : RCOps Complex64 Float where
  exp := Complex64.exp
  sin := Complex64.sin
  cos := Complex64.cos
  pow z w := Complex64.exp (w * Complex64.log z)

end NumLean
