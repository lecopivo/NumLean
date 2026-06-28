module

public import NumLean.Interfaces.Algebra.NormedGroup.Basic

@[expose] public section

namespace NumLean

instance (priority := 30) instNormedAddCommGroupOfOps {R E} [NormedAddGroupOps R E]
    [LawfulDataNormedAddGroupOps E] [LawfulNormedAddGroupOps E] : NormedAddCommGroup E where
  dist_eq := LawfulNormedAddGroupOps.dist_eq

instance (priority := 30) instNormedCommGroupOfOps {R E} [NormedGroupOps R E]
    [LawfulDataNormedGroupOps E] [LawfulNormedGroupOps E] : NormedCommGroup E where
  dist_eq := LawfulNormedGroupOps.dist_eq

instance (priority := 50) instNormedAddMonoidOpsOfNormedAddCommGroup {E : Type v}
    [inst : NormedAddCommGroup E] : NormedAddMonoidOps ℝ E where
  rnorm x := ‖x‖
  nsmul := inst.nsmul

instance (priority := 50) instLawfulDataNormedAddMonoidOpsOfNormedAddCommGroup
    {E : Type v} [inst : NormedAddCommGroup E] : LawfulDataNormedAddMonoidOps E where
  requiv := Equiv.refl ℝ
  rnorm_eq_norm _ := rfl

instance (priority := 50) instLawfulNormedAddMonoidOpsOfNormedAddCommGroup {E : Type v}
    [inst : NormedAddCommGroup E] : LawfulNormedAddMonoidOps E where
  add_assoc := inst.add_assoc
  zero_add := inst.zero_add
  add_zero := inst.add_zero
  nsmul_zero := inst.nsmul_zero
  nsmul_succ := inst.nsmul_succ
  add_comm := inst.add_comm

instance (priority := 50) instNormedAddGroupOpsOfNormedAddCommGroup {E : Type v}
    [inst : NormedAddCommGroup E] : NormedAddGroupOps ℝ E where
  rnorm x := ‖x‖
  zsmul := inst.zsmul

instance (priority := 50) instLawfulDataNormedAddGroupOpsOfNormedAddCommGroup {E : Type v}
    [inst : NormedAddCommGroup E] : LawfulDataNormedAddGroupOps E where
  requiv := Equiv.refl ℝ
  rnorm_eq_norm _ := rfl

instance (priority := 50) instLawfulNormedAddGroupOpsOfNormedAddCommGroup {E : Type v}
    [inst : NormedAddCommGroup E] : LawfulNormedAddGroupOps E where
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
  dist_eq := inst.dist_eq

instance (priority := 50) instNormedMonoidOpsOfNormedCommGroup {E : Type v}
    [inst : NormedCommGroup E] : NormedMonoidOps ℝ E where
  rnorm x := ‖x‖
  npow := inst.npow

instance (priority := 50) instLawfulDataNormedMonoidOpsOfNormedCommGroup {E : Type v}
    [inst : NormedCommGroup E] : LawfulDataNormedMonoidOps E where
  requiv := Equiv.refl ℝ
  rnorm_eq_norm _ := rfl

instance (priority := 50) instLawfulNormedMonoidOpsOfNormedCommGroup {E : Type v}
    [inst : NormedCommGroup E] : LawfulNormedMonoidOps E where
  mul_assoc := inst.mul_assoc
  one_mul := inst.one_mul
  mul_one := inst.mul_one
  npow_zero := inst.npow_zero
  npow_succ := inst.npow_succ
  mul_comm := inst.mul_comm

instance (priority := 50) instNormedGroupOpsOfNormedCommGroup {E : Type v}
    [inst : NormedCommGroup E] : NormedGroupOps ℝ E where
  rnorm x := ‖x‖
  zpow := inst.zpow

instance (priority := 50) instLawfulDataNormedGroupOpsOfNormedCommGroup {E : Type v}
    [inst : NormedCommGroup E] : LawfulDataNormedGroupOps E where
  requiv := Equiv.refl ℝ
  rnorm_eq_norm _ := rfl

instance (priority := 50) instLawfulNormedGroupOpsOfNormedCommGroup {E : Type v}
    [inst : NormedCommGroup E] : LawfulNormedGroupOps E where
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
  dist_eq := inst.dist_eq

example {E : Type v} [inst : NormedAddCommGroup E] :
    (instNormedAddCommGroupOfOps (R := ℝ) : NormedAddCommGroup E) = inst :=
  rfl

example {E : Type v} [inst : NormedCommGroup E] :
    (instNormedCommGroupOfOps (R := ℝ) : NormedCommGroup E) = inst :=
  rfl

end NumLean
