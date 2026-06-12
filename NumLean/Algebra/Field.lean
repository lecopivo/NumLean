import Mathlib.Algebra.Field.Defs

namespace NumLean
namespace Field

class AddGroupOps (K : Type u) extends Add K, Sub K, Neg K, Zero K where
  nsmul : Nat → K → K
  zsmul : Int → K → K

instance [inst : AddGroupOps K] : SMul Nat K := ⟨inst.nsmul⟩
instance [inst : AddGroupOps K] : SMul Int K := ⟨inst.zsmul⟩

class LawfulAddGroupOps (K : Type u) [AddGroupOps K] : Prop where
  add_assoc : ∀ a b c : K, a + b + c = a + (b + c)
  zero_add : ∀ a : K, 0 + a = a
  add_zero : ∀ a : K, a + 0 = a
  nsmul_zero : ∀ x : K, AddGroupOps.nsmul 0 x = 0
  nsmul_succ : ∀ (n : Nat) (x : K), AddGroupOps.nsmul (n + 1) x = AddGroupOps.nsmul n x + x
  sub_eq_add_neg : ∀ a b : K, a - b = a + -b
  zsmul_zero : ∀ a : K, AddGroupOps.zsmul 0 a = 0
  zsmul_succ : ∀ (n : Nat) (a : K), AddGroupOps.zsmul (Int.ofNat n.succ) a = AddGroupOps.zsmul (Int.ofNat n) a + a
  zsmul_neg : ∀ (n : Nat) (a : K), AddGroupOps.zsmul (Int.negSucc n) a = -AddGroupOps.zsmul (Int.ofNat n.succ) a
  neg_add_cancel : ∀ a : K, -a + a = 0

class LawfulAddCommGroupOps (K : Type u) [AddGroupOps K] : Prop extends LawfulAddGroupOps K where
  add_comm : ∀ a b : K, a + b = b + a

class GroupOps (K : Type u) extends Mul K, Div K, Inv K, One K where
  npow : Nat → K → K
  zpow : Int → K → K

instance [inst : GroupOps K] : NatPow K := ⟨fun x n => inst.npow n x⟩
instance [inst : GroupOps K] : Pow K Int := ⟨fun x n => inst.zpow n x⟩

class LawfulGroupOps (K : Type u) [GroupOps K] : Prop where
  mul_assoc : ∀ a b c : K, a * b * c = a * (b * c)
  one_mul : ∀ a : K, 1 * a = a
  mul_one : ∀ a : K, a * 1 = a
  npow_zero : ∀ x : K, GroupOps.npow 0 x = 1
  npow_succ : ∀ (n : Nat) (x : K), GroupOps.npow (n + 1) x = GroupOps.npow n x * x
  div_eq_mul_inv : ∀ a b : K, a / b = a * b⁻¹
  zpow_zero : ∀ a : K, GroupOps.zpow 0 a = 1
  zpow_succ : ∀ (n : Nat) (a : K), GroupOps.zpow (Int.ofNat n.succ) a = GroupOps.zpow (Int.ofNat n) a * a
  zpow_neg : ∀ (n : Nat) (a : K), GroupOps.zpow (Int.negSucc n) a = (GroupOps.zpow (Int.ofNat n.succ) a)⁻¹

class FieldOps (K : Type u) extends
    AddGroupOps K, GroupOps K,
    NatCast K, IntCast K, NNRatCast K, RatCast K where
  nnqsmul : ℚ≥0 → K → K
  qsmul : ℚ → K → K

instance [inst : FieldOps K] : SMul ℚ≥0 K := ⟨inst.nnqsmul⟩
instance [inst : FieldOps K] : SMul ℚ K := ⟨inst.qsmul⟩

class LawfulFieldOps (K : Type u) [FieldOps K] : Prop extends
    LawfulAddCommGroupOps K, LawfulGroupOps K where
  zero_mul : ∀ a : K, 0 * a = 0
  mul_zero : ∀ a : K, a * 0 = 0
  left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : K, (a + b) * c = a * c + b * c
  natCast_zero : (Nat.cast 0 : K) = 0
  natCast_succ : ∀ n : Nat, (Nat.cast (n + 1) : K) = Nat.cast n + 1
  intCast_ofNat : ∀ n : Nat, (Int.cast (Int.ofNat n) : K) = Nat.cast n
  intCast_negSucc : ∀ n : Nat, (Int.cast (Int.negSucc n) : K) = -Nat.cast (n + 1)
  mul_comm : ∀ a b : K, a * b = b * a
  exists_pair_ne : ∃ x y : K, x ≠ y
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : K)⁻¹ = 0
  nnratCast_def : ∀ q : ℚ≥0, (NNRat.cast q : K) = Nat.cast q.num / Nat.cast q.den
  nnqsmul_def : ∀ (q : ℚ≥0) (a : K), FieldOps.nnqsmul q a = NNRat.cast q * a
  ratCast_def : ∀ q : ℚ, (Rat.cast q : K) = Int.cast q.num / Nat.cast q.den
  qsmul_def : ∀ (q : ℚ) (a : K), FieldOps.qsmul q a = Rat.cast q * a

@[reducible]
def mkField (K : Type u) [FieldOps K] [LawfulFieldOps K] : _root_.Field K where
  add_assoc := LawfulAddGroupOps.add_assoc
  zero_add := LawfulAddGroupOps.zero_add
  add_zero := LawfulAddGroupOps.add_zero
  nsmul := AddGroupOps.nsmul
  nsmul_zero := LawfulAddGroupOps.nsmul_zero
  nsmul_succ := LawfulAddGroupOps.nsmul_succ
  add_comm := LawfulAddCommGroupOps.add_comm
  mul_assoc := LawfulGroupOps.mul_assoc
  one_mul := LawfulGroupOps.one_mul
  mul_one := LawfulGroupOps.mul_one
  npow := GroupOps.npow
  npow_zero := LawfulGroupOps.npow_zero
  npow_succ := LawfulGroupOps.npow_succ
  zero_mul := LawfulFieldOps.zero_mul
  mul_zero := LawfulFieldOps.mul_zero
  left_distrib := LawfulFieldOps.left_distrib
  right_distrib := LawfulFieldOps.right_distrib
  natCast_zero := LawfulFieldOps.natCast_zero
  natCast_succ := LawfulFieldOps.natCast_succ
  sub_eq_add_neg := LawfulAddGroupOps.sub_eq_add_neg
  zsmul := AddGroupOps.zsmul
  zsmul_zero' := LawfulAddGroupOps.zsmul_zero
  zsmul_succ' := LawfulAddGroupOps.zsmul_succ
  zsmul_neg' := LawfulAddGroupOps.zsmul_neg
  neg_add_cancel := LawfulAddGroupOps.neg_add_cancel
  intCast_ofNat := LawfulFieldOps.intCast_ofNat
  intCast_negSucc := LawfulFieldOps.intCast_negSucc
  mul_comm := LawfulFieldOps.mul_comm
  div_eq_mul_inv := LawfulGroupOps.div_eq_mul_inv
  zpow := GroupOps.zpow
  zpow_zero' := LawfulGroupOps.zpow_zero
  zpow_succ' := LawfulGroupOps.zpow_succ
  zpow_neg' := LawfulGroupOps.zpow_neg
  exists_pair_ne := LawfulFieldOps.exists_pair_ne
  mul_inv_cancel := LawfulFieldOps.mul_inv_cancel
  inv_zero := LawfulFieldOps.inv_zero
  nnratCast_def := LawfulFieldOps.nnratCast_def
  nnqsmul := FieldOps.nnqsmul
  nnqsmul_def := LawfulFieldOps.nnqsmul_def
  ratCast_def := LawfulFieldOps.ratCast_def
  qsmul := FieldOps.qsmul
  qsmul_def := LawfulFieldOps.qsmul_def

instance instFieldOpsOfField {K : Type u} [inst : _root_.Field K] : FieldOps K where
  nsmul := inst.nsmul
  zsmul := inst.zsmul
  npow := inst.npow
  zpow := inst.zpow
  nnqsmul := inst.nnqsmul
  qsmul := inst.qsmul

instance instLawfulFieldOpsOfField {K : Type u} [inst : _root_.Field K] : LawfulFieldOps K where
  add_assoc := inst.add_assoc
  zero_add := inst.zero_add
  add_zero := inst.add_zero
  nsmul_zero := inst.nsmul_zero
  nsmul_succ := inst.nsmul_succ
  add_comm := inst.add_comm
  mul_assoc := inst.mul_assoc
  one_mul := inst.one_mul
  mul_one := inst.mul_one
  npow_zero := inst.npow_zero
  npow_succ := inst.npow_succ
  zero_mul := inst.zero_mul
  mul_zero := inst.mul_zero
  left_distrib := inst.left_distrib
  right_distrib := inst.right_distrib
  natCast_zero := inst.natCast_zero
  natCast_succ := inst.natCast_succ
  sub_eq_add_neg := inst.sub_eq_add_neg
  zsmul_zero := inst.zsmul_zero'
  zsmul_succ := inst.zsmul_succ'
  zsmul_neg := inst.zsmul_neg'
  neg_add_cancel := inst.neg_add_cancel
  intCast_ofNat := inst.intCast_ofNat
  intCast_negSucc := inst.intCast_negSucc
  mul_comm := inst.mul_comm
  div_eq_mul_inv := inst.div_eq_mul_inv
  zpow_zero := inst.zpow_zero'
  zpow_succ := inst.zpow_succ'
  zpow_neg := inst.zpow_neg'
  exists_pair_ne := inst.exists_pair_ne
  mul_inv_cancel := inst.mul_inv_cancel
  inv_zero := inst.inv_zero
  nnratCast_def := inst.nnratCast_def
  nnqsmul_def := inst.nnqsmul_def
  ratCast_def := inst.ratCast_def
  qsmul_def := inst.qsmul_def

example {K : Type u} [inst : _root_.Field K] : (mkField K : _root_.Field K) = inst :=
  rfl

end Field
end NumLean
