import NumLean.Interfaces.Algebra.Ring.Basic
import NumLean.Interfaces.Algebra.Group.Lawful

namespace NumLean
namespace Interfaces
namespace Algebra

@[hierarchy_graph algebra_ops]
instance (priority := 100) instSemiringOpsOfCommSemiring {K : Type u}
    [inst : CommSemiring K] : SemiringOps K where
  nsmul := inst.nsmul
  npow := inst.npow

@[hierarchy_graph algebra_lawful]
instance (priority := 100) instLawfulSemiringOpsOfCommSemiring {K : Type u}
    [inst : CommSemiring K] : LawfulSemiringOps K where
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
  mul_comm := inst.mul_comm
  zero_mul := inst.zero_mul
  mul_zero := inst.mul_zero
  left_distrib := inst.left_distrib
  right_distrib := inst.right_distrib
  natCast_zero := inst.natCast_zero
  natCast_succ := inst.natCast_succ

@[hierarchy_graph algebra_lawful]
instance (priority := 50) instCommSemiringOfOps {K : Type u} [inst : SemiringOps K]
    [LawfulSemiringOps K] : CommSemiring K where
  add_assoc := LawfulAddMonoidOps.add_assoc
  zero_add := LawfulAddMonoidOps.zero_add
  add_zero := LawfulAddMonoidOps.add_zero
  nsmul := inst.nsmul
  nsmul_zero := LawfulAddMonoidOps.nsmul_zero
  nsmul_succ := LawfulAddMonoidOps.nsmul_succ
  add_comm := LawfulAddMonoidOps.add_comm
  mul_assoc := LawfulMonoidOps.mul_assoc
  one_mul := LawfulMonoidOps.one_mul
  mul_one := LawfulMonoidOps.mul_one
  npow := inst.npow
  npow_zero := LawfulMonoidOps.npow_zero
  npow_succ := LawfulMonoidOps.npow_succ
  zero_mul := LawfulSemiringOps.zero_mul
  mul_zero := LawfulSemiringOps.mul_zero
  left_distrib := LawfulSemiringOps.left_distrib
  right_distrib := LawfulSemiringOps.right_distrib
  natCast_zero := LawfulSemiringOps.natCast_zero
  natCast_succ := LawfulSemiringOps.natCast_succ
  mul_comm := LawfulMonoidOps.mul_comm

example {K : Type u} [inst : CommSemiring K] :
    (instCommSemiringOfOps : CommSemiring K) = inst :=
  rfl

@[hierarchy_graph algebra_ops]
instance (priority := 100) instRingOpsOfCommRing {K : Type u} [inst : CommRing K] : RingOps K where
  nsmul := inst.nsmul
  npow := inst.npow
  zsmul := inst.zsmul

@[hierarchy_graph algebra_lawful]
instance (priority := 100) instLawfulRingOpsOfCommRing {K : Type u} [inst : CommRing K] :
    LawfulRingOps K where
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
  mul_comm := inst.mul_comm
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

@[hierarchy_graph algebra_lawful]
instance (priority := 50) instCommRingOfOps {K : Type u} [inst : RingOps K]
    [LawfulRingOps K] : CommRing K where
  add_assoc := LawfulAddMonoidOps.add_assoc
  zero_add := LawfulAddMonoidOps.zero_add
  add_zero := LawfulAddMonoidOps.add_zero
  nsmul := inst.nsmul
  nsmul_zero := LawfulAddMonoidOps.nsmul_zero
  nsmul_succ := LawfulAddMonoidOps.nsmul_succ
  add_comm := LawfulAddMonoidOps.add_comm
  mul_assoc := LawfulMonoidOps.mul_assoc
  one_mul := LawfulMonoidOps.one_mul
  mul_one := LawfulMonoidOps.mul_one
  npow := inst.npow
  npow_zero := LawfulMonoidOps.npow_zero
  npow_succ := LawfulMonoidOps.npow_succ
  zero_mul := LawfulSemiringOps.zero_mul
  mul_zero := LawfulSemiringOps.mul_zero
  left_distrib := LawfulSemiringOps.left_distrib
  right_distrib := LawfulSemiringOps.right_distrib
  natCast_zero := LawfulSemiringOps.natCast_zero
  natCast_succ := LawfulSemiringOps.natCast_succ
  sub_eq_add_neg := LawfulRingOps.sub_eq_add_neg
  zsmul := inst.zsmul
  zsmul_zero' := LawfulRingOps.zsmul_zero
  zsmul_succ' := LawfulRingOps.zsmul_succ
  zsmul_neg' := LawfulRingOps.zsmul_neg
  neg_add_cancel := LawfulRingOps.neg_add_cancel
  intCast_ofNat := LawfulRingOps.intCast_ofNat
  intCast_negSucc := LawfulRingOps.intCast_negSucc
  mul_comm := LawfulMonoidOps.mul_comm

example {K : Type u} [inst : CommRing K] :
    (instCommRingOfOps : CommRing K) = inst :=
  rfl

end Algebra
end Interfaces
end NumLean
