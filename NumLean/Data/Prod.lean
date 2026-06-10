import Mathlib.Algebra.Star.Basic

namespace Prod

instance instOfNat {X Y : Type _} (n : Nat) [OfNat X n] [OfNat Y n] : OfNat (X × Y) n where
  ofNat := (OfNat.ofNat n, OfNat.ofNat n)

instance instNatPow {X Y : Type _} [NatPow X] [NatPow Y] : NatPow (X × Y) where
  pow xy n := (xy.1 ^ n, xy.2 ^ n)

end Prod
