import NumLean.Data.Scalars.Complex64.Basic
import NumLean.Data.Scalars.Float64.Algebra
import NumLean.Interfaces.Algebra.RCLike.Basic
import NumLean.Data.Complex

namespace NumLean

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

instance : NatCast Complex64 where
  natCast n := ⟨n.toFloat, 0⟩

instance : IntCast Complex64 where
  intCast n := ⟨n.toInt64.toFloat, 0⟩

instance : NNRatCast Complex64 where
  nnratCast q := ⟨(q : Float), 0⟩

instance : RatCast Complex64 where
  ratCast q := ⟨(q : Float), 0⟩

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

instance : BEq Complex64 where
  beq x y := x.re == y.re && x.im == y.im

-- todo: make log(n)
private def npowRecComplex64 : Complex64 → Nat → Complex64
  | _, 0 => 1
  | z, n + 1 => npowRecComplex64 z n * z

-- todo: make log(n)
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

instance : SMul Float Complex64 where
  smul r z := ⟨r * z.re, r * z.im⟩

instance : AddGroupOps Complex64 where
  nsmul n z := n • z
  zsmul n z := n • z

instance : GroupOps Complex64 where
  npow n z := z ^ n
  zpow n z := z ^ n

instance : FieldOps Complex64 where
  nnqsmul q z := (q : Complex64) * z
  qsmul q z := (q : Complex64) * z

instance : RNorm Complex64 Float where
  rnorm := Complex64.abs

noncomputable instance : RCOps Float Complex64 where
  le z w := z.re ≤ w.re ∧ z.im == w.im
  lt z w := z.re < w.re ∧ z.im == w.im
  decLe := inferInstance
  decLt := inferInstance
  smul r z := ⟨r * z.re, r * z.im⟩
  algebraMap r := ⟨r, 0⟩
  make re im := ⟨re, im⟩
  re := Complex64.re
  im := Complex64.im
  I := ⟨0, 1⟩
  cexp := Complex64.exp
  csin := Complex64.sin
  ccos := Complex64.cos
  cpow z w := Complex64.exp (w * Complex64.log z)

end NumLean
