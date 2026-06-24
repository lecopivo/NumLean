import Mathlib.Algebra.Ring.Defs
import NumLean.Interfaces.Algebra.Group.Basic

namespace NumLean
namespace Interfaces
namespace Algebra

@[hierarchy_graph algebra_ops]
class SemiringOps (K : Type u) extends AddMonoidOps K, MonoidOps K, NatCast K

@[hierarchy_graph algebra_lawful]
class LawfulSemiringOps (K : Type u) [SemiringOps K] : Prop extends
    LawfulAddMonoidOps K, LawfulMonoidOps K where
  zero_mul : ∀ a : K, 0 * a = 0
  mul_zero : ∀ a : K, a * 0 = 0
  left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : K, (a + b) * c = a * c + b * c
  natCast_zero : (Nat.cast 0 : K) = 0
  natCast_succ : ∀ n : Nat, (Nat.cast (n + 1) : K) = Nat.cast n + 1

@[hierarchy_graph algebra_ops]
class RingOps (K : Type u) extends SemiringOps K, AddGroupOps K, IntCast K

@[hierarchy_graph algebra_lawful]
class LawfulRingOps (K : Type u) [RingOps K] : Prop extends
    LawfulSemiringOps K, LawfulAddGroupOps K where
  intCast_ofNat : ∀ n : Nat, (Int.cast (Int.ofNat n) : K) = Nat.cast n
  intCast_negSucc : ∀ n : Nat, (Int.cast (Int.negSucc n) : K) = -Nat.cast (n + 1)

end Algebra
end Interfaces
end NumLean
