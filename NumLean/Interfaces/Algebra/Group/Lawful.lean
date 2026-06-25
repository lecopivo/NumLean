import NumLean.Interfaces.Algebra.Group.Basic

namespace NumLean
namespace Interfaces
namespace Algebra

@[hierarchy_graph]
instance (priority := 100) instAddMonoidOpsOfAddCommMonoid {K : Type u}
    [inst : AddCommMonoid K] : AddMonoidOps K where
  nsmul := inst.nsmul

@[hierarchy_graph]
instance (priority := 100) instLawfulAddMonoidOpsOfAddCommMonoid {K : Type u}
    [inst : AddCommMonoid K] : LawfulAddMonoidOps K where
  add_assoc := inst.add_assoc
  zero_add := inst.zero_add
  add_zero := inst.add_zero
  nsmul_zero := inst.nsmul_zero
  nsmul_succ := inst.nsmul_succ
  add_comm := inst.add_comm

@[hierarchy_graph]
instance (priority := 50) instAddCommMonoidOfOps {K : Type u} [inst : AddMonoidOps K]
    [LawfulAddMonoidOps K] : AddCommMonoid K where
  add_assoc := LawfulAddMonoidOps.add_assoc
  zero_add := LawfulAddMonoidOps.zero_add
  add_zero := LawfulAddMonoidOps.add_zero
  nsmul := inst.nsmul
  nsmul_zero := LawfulAddMonoidOps.nsmul_zero
  nsmul_succ := LawfulAddMonoidOps.nsmul_succ
  add_comm := LawfulAddMonoidOps.add_comm

example {K : Type u} [inst : AddCommMonoid K] :
    (instAddCommMonoidOfOps : AddCommMonoid K) = inst :=
  rfl

@[hierarchy_graph]
instance (priority := 100) instMonoidOpsOfCommMonoid {K : Type u} [inst : CommMonoid K] :
    MonoidOps K where
  npow := inst.npow

@[hierarchy_graph]
instance (priority := 100) instLawfulMonoidOpsOfCommMonoid {K : Type u} [inst : CommMonoid K] :
    LawfulMonoidOps K where
  mul_assoc := inst.mul_assoc
  one_mul := inst.one_mul
  mul_one := inst.mul_one
  npow_zero := inst.npow_zero
  npow_succ := inst.npow_succ
  mul_comm := inst.mul_comm

@[hierarchy_graph]
instance (priority := 50) instCommMonoidOfOps {K : Type u} [inst : MonoidOps K]
    [LawfulMonoidOps K] : CommMonoid K where
  mul_assoc := LawfulMonoidOps.mul_assoc
  one_mul := LawfulMonoidOps.one_mul
  mul_one := LawfulMonoidOps.mul_one
  npow := inst.npow
  npow_zero := LawfulMonoidOps.npow_zero
  npow_succ := LawfulMonoidOps.npow_succ
  mul_comm := LawfulMonoidOps.mul_comm

example {K : Type u} [inst : CommMonoid K] :
    (instCommMonoidOfOps : CommMonoid K) = inst :=
  rfl

@[hierarchy_graph]
instance (priority := 100) instAddGroupOpsOfAddCommGroup {K : Type u}
    [inst : AddCommGroup K] : AddGroupOps K where
  nsmul := inst.nsmul
  zsmul := inst.zsmul

@[hierarchy_graph]
instance (priority := 100) instLawfulAddGroupOpsOfAddCommGroup {K : Type u}
    [inst : AddCommGroup K] : LawfulAddGroupOps K where
  add_assoc := inst.add_assoc
  zero_add := inst.zero_add
  add_zero := inst.add_zero
  nsmul_zero := inst.nsmul_zero
  nsmul_succ := inst.nsmul_succ
  add_comm := inst.add_comm
  sub_eq_add_neg := inst.sub_eq_add_neg
  zsmul_zero := inst.zsmul_zero'
  zsmul_succ := inst.zsmul_succ'
  zsmul_neg := inst.zsmul_neg'
  neg_add_cancel := inst.neg_add_cancel

@[hierarchy_graph]
instance (priority := 50) instAddCommGroupOfOps {K : Type u} [inst : AddGroupOps K]
    [LawfulAddGroupOps K] : AddCommGroup K where
  add_assoc := LawfulAddMonoidOps.add_assoc
  zero_add := LawfulAddMonoidOps.zero_add
  add_zero := LawfulAddMonoidOps.add_zero
  nsmul := inst.nsmul
  nsmul_zero := LawfulAddMonoidOps.nsmul_zero
  nsmul_succ := LawfulAddMonoidOps.nsmul_succ
  sub_eq_add_neg := LawfulAddGroupOps.sub_eq_add_neg
  zsmul := inst.zsmul
  zsmul_zero' := LawfulAddGroupOps.zsmul_zero
  zsmul_succ' := LawfulAddGroupOps.zsmul_succ
  zsmul_neg' := LawfulAddGroupOps.zsmul_neg
  neg_add_cancel := LawfulAddGroupOps.neg_add_cancel
  add_comm := LawfulAddMonoidOps.add_comm

example {K : Type u} [inst : AddCommGroup K] :
    (instAddCommGroupOfOps : AddCommGroup K) = inst :=
  rfl

@[hierarchy_graph]
instance (priority := 100) instGroupOpsOfCommGroup {K : Type u} [inst : CommGroup K] :
    GroupOps K where
  npow := inst.npow
  zpow := inst.zpow

@[hierarchy_graph]
instance (priority := 100) instLawfulGroupOpsOfCommGroup {K : Type u} [inst : CommGroup K] :
    LawfulGroupOps K where
  mul_assoc := inst.mul_assoc
  one_mul := inst.one_mul
  mul_one := inst.mul_one
  npow_zero := inst.npow_zero
  npow_succ := inst.npow_succ
  mul_comm := inst.mul_comm
  div_eq_mul_inv := inst.div_eq_mul_inv
  zpow_zero := inst.zpow_zero'
  zpow_succ := inst.zpow_succ'
  zpow_neg := inst.zpow_neg'
  inv_mul_cancel := inst.inv_mul_cancel

@[hierarchy_graph]
instance (priority := 50) instCommGroupOfOps {K : Type u} [inst : GroupOps K]
    [LawfulGroupOps K] : CommGroup K where
  mul_assoc := LawfulMonoidOps.mul_assoc
  one_mul := LawfulMonoidOps.one_mul
  mul_one := LawfulMonoidOps.mul_one
  npow := inst.npow
  npow_zero := LawfulMonoidOps.npow_zero
  npow_succ := LawfulMonoidOps.npow_succ
  div_eq_mul_inv := LawfulGroupOps.div_eq_mul_inv
  zpow := inst.zpow
  zpow_zero' := LawfulGroupOps.zpow_zero
  zpow_succ' := LawfulGroupOps.zpow_succ
  zpow_neg' := LawfulGroupOps.zpow_neg
  inv_mul_cancel := LawfulGroupOps.inv_mul_cancel
  mul_comm := LawfulMonoidOps.mul_comm

example {K : Type u} [inst : CommGroup K] :
    (instCommGroupOfOps : CommGroup K) = inst :=
  rfl

end Algebra
end Interfaces
end NumLean
