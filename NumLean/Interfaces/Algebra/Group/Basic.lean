module

public import Mathlib.Algebra.Group.Defs
public import NumLean.Meta.HierarchyGraph

@[expose] public section

namespace NumLean
namespace Interfaces
namespace Algebra

-- These are broad fallback routes to primitive operations. Keep them below direct NumLean ops
-- projections so existing `AddMonoidOps`/`AddGroupOps` evidence is not bypassed.
attribute [instance 100] AddZero.toZero NegZeroClass.toZero

@[hierarchy_graph algebra_ops]
class AddMonoidOps (K : Type u) extends Add K, Zero K where
  nsmul : Nat → K → K

instance [inst : AddMonoidOps K] : SMul Nat K := ⟨inst.nsmul⟩

@[hierarchy_graph algebra_lawful]
class LawfulAddMonoidOps (K : Type u) [AddMonoidOps K] : Prop where
  add_assoc : ∀ a b c : K, a + b + c = a + (b + c)
  zero_add : ∀ a : K, 0 + a = a
  add_zero : ∀ a : K, a + 0 = a
  nsmul_zero : ∀ x : K, AddMonoidOps.nsmul 0 x = 0
  nsmul_succ : ∀ (n : Nat) (x : K), AddMonoidOps.nsmul (n + 1) x =
    AddMonoidOps.nsmul n x + x
  add_comm : ∀ a b : K, a + b = b + a

@[hierarchy_graph algebra_ops]
class MonoidOps (K : Type u) extends Mul K, One K where
  npow : Nat → K → K

instance [inst : MonoidOps K] : NatPow K := ⟨fun x n => inst.npow n x⟩

@[hierarchy_graph algebra_lawful]
class LawfulMonoidOps (K : Type u) [MonoidOps K] : Prop where
  mul_assoc : ∀ a b c : K, a * b * c = a * (b * c)
  one_mul : ∀ a : K, 1 * a = a
  mul_one : ∀ a : K, a * 1 = a
  npow_zero : ∀ x : K, MonoidOps.npow 0 x = 1
  npow_succ : ∀ (n : Nat) (x : K), MonoidOps.npow (n + 1) x =
    MonoidOps.npow n x * x
  mul_comm : ∀ a b : K, a * b = b * a

@[hierarchy_graph algebra_ops]
class AddGroupOps (K : Type u) extends AddMonoidOps K, Sub K, Neg K where
  zsmul : Int → K → K

instance [inst : AddGroupOps K] : SMul Int K := ⟨inst.zsmul⟩

@[hierarchy_graph algebra_lawful]
class LawfulAddGroupOps (K : Type u) [AddGroupOps K] : Prop extends LawfulAddMonoidOps K where
  sub_eq_add_neg : ∀ a b : K, a - b = a + -b
  zsmul_zero : ∀ a : K, AddGroupOps.zsmul 0 a = 0
  zsmul_succ : ∀ (n : Nat) (a : K), AddGroupOps.zsmul (Int.ofNat n.succ) a =
    AddGroupOps.zsmul (Int.ofNat n) a + a
  zsmul_neg : ∀ (n : Nat) (a : K), AddGroupOps.zsmul (Int.negSucc n) a =
    -AddGroupOps.zsmul (Int.ofNat n.succ) a
  neg_add_cancel : ∀ a : K, -a + a = 0

@[hierarchy_graph algebra_ops]
class GroupOps (K : Type u) extends MonoidOps K, Div K, Inv K where
  zpow : Int → K → K

instance [inst : GroupOps K] : Pow K Int := ⟨fun x n => inst.zpow n x⟩

@[hierarchy_graph algebra_lawful]
class LawfulGroupOps (K : Type u) [GroupOps K] : Prop extends LawfulMonoidOps K where
  div_eq_mul_inv : ∀ a b : K, a / b = a * b⁻¹
  zpow_zero : ∀ a : K, GroupOps.zpow 0 a = 1
  zpow_succ : ∀ (n : Nat) (a : K), GroupOps.zpow (Int.ofNat n.succ) a =
    GroupOps.zpow (Int.ofNat n) a * a
  zpow_neg : ∀ (n : Nat) (a : K), GroupOps.zpow (Int.negSucc n) a =
    (GroupOps.zpow (Int.ofNat n.succ) a)⁻¹
  inv_mul_cancel : ∀ a : K, a⁻¹ * a = 1

end Algebra
end Interfaces
end NumLean
