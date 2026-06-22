import Mathlib.Algebra.Field.Defs
import NumLean.Interfaces.Algebra.Ring.Basic

namespace NumLean
namespace Interfaces
namespace Algebra

class FieldOps (K : Type u) extends RingOps K, GroupOps K, NNRatCast K, RatCast K where
  nnqsmul : ℚ≥0 → K → K
  qsmul : ℚ → K → K

instance [inst : FieldOps K] : SMul ℚ≥0 K := ⟨inst.nnqsmul⟩
instance [inst : FieldOps K] : SMul ℚ K := ⟨inst.qsmul⟩

class LawfulFieldOps (K : Type u) [FieldOps K] : Prop extends LawfulRingOps K where
  div_eq_mul_inv : ∀ a b : K, a / b = a * b⁻¹
  zpow_zero : ∀ a : K, GroupOps.zpow 0 a = 1
  zpow_succ : ∀ (n : Nat) (a : K), GroupOps.zpow (Int.ofNat n.succ) a =
    GroupOps.zpow (Int.ofNat n) a * a
  zpow_neg : ∀ (n : Nat) (a : K), GroupOps.zpow (Int.negSucc n) a =
    (GroupOps.zpow (Int.ofNat n.succ) a)⁻¹
  exists_pair_ne : ∃ x y : K, x ≠ y
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : K)⁻¹ = 0
  nnratCast_def : ∀ q : ℚ≥0, (NNRat.cast q : K) = Nat.cast q.num / Nat.cast q.den
  nnqsmul_def : ∀ (q : ℚ≥0) (a : K), FieldOps.nnqsmul q a = NNRat.cast q * a
  ratCast_def : ∀ q : ℚ, (Rat.cast q : K) = Int.cast q.num / Nat.cast q.den
  qsmul_def : ∀ (q : ℚ) (a : K), FieldOps.qsmul q a = Rat.cast q * a

end Algebra
end Interfaces
end NumLean
