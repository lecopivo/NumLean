module

public import NumLean.Data.Scalars.Complex32.Basic
public import NumLean.Data.Scalars.Float32.Algebra
public import NumLean.Interfaces.Algebra.RCLike.Basic

@[expose] public section

namespace NumLean

instance : NatCast Complex32 where
  natCast n := ⟨n.toFloat32, 0⟩

instance : IntCast Complex32 where
  intCast n := ⟨n.toInt32.toFloat32, 0⟩

instance : NNRatCast Complex32 where
  nnratCast q := ⟨(q : Float32), 0⟩

instance : RatCast Complex32 where
  ratCast q := ⟨(q : Float32), 0⟩

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

instance : BEq Complex32 where
  beq x y := x.re == y.re && x.im == y.im

-- todo: implement by in log(n) steps by halving n
def npowRec : Complex32 → Nat → Complex32
  | _, 0 => 1
  | z, n + 1 => npowRec z n * z

-- todo: implement by in log(n) steps by halving n
def zpowRec : Complex32 → Int → Complex32
  | z, .ofNat n => npowRec z n
  | z, .negSucc n => (npowRec z (n + 1))⁻¹

instance : NatPow Complex32 where
  pow := npowRec

instance : Pow Complex32 Int where
  pow := zpowRec

instance : SMul Nat Complex32 where
  smul n z := ⟨n • z.re, n • z.im⟩

instance : SMul Int Complex32 where
  smul n z := ⟨n • z.re, n • z.im⟩

instance : SMul Float32 Complex32 where
  smul r z := ⟨r * z.re, r * z.im⟩

instance : AddGroupOps Complex32 where
  nsmul n z := n • z
  zsmul n z := n • z

instance : GroupOps Complex32 where
  npow n z := z ^ n
  zpow n z := z ^ n

instance : FieldOps Complex32 where
  nnqsmul q z := (q : Complex32) * z
  qsmul q z := (q : Complex32) * z

instance : RNorm Complex32 Float32 where
  rnorm := Complex32.abs

instance : RCOps Float32 Complex32 where
  le x y := x.re ≤ y.re ∧ x.im == y.im
  lt x y := x.re < y.re ∧ x.im == y.im
  decLe := inferInstance
  decLt := inferInstance
  smul r z := ⟨r * z.re, r * z.im⟩
  algebraMap r := ⟨r, 0⟩
  make re im := ⟨re, im⟩
  re := Complex32.re
  im := Complex32.im
  I := ⟨0, 1⟩
  cexp := Complex32.exp
  csin := Complex32.sin
  ccos := Complex32.cos
  cpow z w := Complex32.exp (w * Complex32.log z)

example : RCOps Float32 Complex32 := inferInstance

end NumLean
