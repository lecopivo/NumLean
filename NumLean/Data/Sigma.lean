import Mathlib.Algebra.Star.Basic

namespace Sigma

instance instZero {X Y : Type _} [Zero X] [Zero Y] : Zero ((_ : X) × Y) where
  zero := ⟨0, 0⟩

instance instOne {X Y : Type _} [One X] [One Y] : One ((_ : X) × Y) where
  one := ⟨1, 1⟩

instance instOfNat {X Y : Type _} (n : Nat) [OfNat X n] [OfNat Y n] : OfNat ((_ : X) × Y) n where
  ofNat := ⟨OfNat.ofNat n, OfNat.ofNat n⟩

instance instNeg {X Y : Type _} [Neg X] [Neg Y] : Neg ((_ : X) × Y) where
  neg xy := ⟨-xy.1, -xy.2⟩

instance instAdd {X Y : Type _} [Add X] [Add Y] : Add ((_ : X) × Y) where
  add xy xy' := ⟨xy.1 + xy'.1, xy.2 + xy'.2⟩

instance instSub {X Y : Type _} [Sub X] [Sub Y] : Sub ((_ : X) × Y) where
  sub xy xy' := ⟨xy.1 - xy'.1, xy.2 - xy'.2⟩

instance instMul {X Y : Type _} [Mul X] [Mul Y] : Mul ((_ : X) × Y) where
  mul xy xy' := ⟨xy.1 * xy'.1, xy.2 * xy'.2⟩

instance instInv {X Y : Type _} [Inv X] [Inv Y] : Inv ((_ : X) × Y) where
  inv xy := ⟨xy.1⁻¹, xy.2⁻¹⟩

instance instDiv {X Y : Type _} [Div X] [Div Y] : Div ((_ : X) × Y) where
  div xy xy' := ⟨xy.1 / xy'.1, xy.2 / xy'.2⟩

instance instSMul {R X Y : Type _} [SMul R X] [SMul R Y] : SMul R ((_ : X) × Y) where
  smul a xy := ⟨a • xy.1, a • xy.2⟩

instance instNatPow {X Y : Type _} [NatPow X] [NatPow Y] : NatPow ((_ : X) × Y) where
  pow xy n := ⟨xy.1 ^ n, xy.2 ^ n⟩

instance instPowInt {X Y : Type _} [Pow X Int] [Pow Y Int] : Pow ((_ : X) × Y) Int where
  pow xy n := ⟨xy.1 ^ n, xy.2 ^ n⟩

instance instStar {X Y : Type _} [Star X] [Star Y] : Star ((_ : X) × Y) where
  star xy := ⟨star xy.1, star xy.2⟩

end Sigma
