import NumLean.Interfaces.Algebra.NormedField.Basic

namespace NumLean

instance (priority := 50) instNormedFieldOfOps {R K} [NormedFieldOps R K]
    [LawfulDataNormedFieldOps K] [LawfulNormedFieldOps K] : NormedField K where
  dist_eq := LawfulNormedFieldOps.dist_eq
  norm_mul := LawfulNormedFieldOps.norm_mul

instance (priority := 100) instNormedFieldOpsOfNormedField {K : Type v}
    [inst : NormedField K] : NormedFieldOps ℝ K where
  rnorm x := ‖x‖
  zsmul := inst.zsmul
  intCast := inst.intCast
  zpow := inst.zpow
  nnqsmul := inst.nnqsmul
  qsmul := inst.qsmul

instance (priority := 100) instLawfulDataNormedFieldOpsOfNormedField {K : Type v}
    [inst : NormedField K] : LawfulDataNormedFieldOps K where
  requiv := Equiv.refl ℝ
  rnorm_eq_norm _ := rfl

instance (priority := 100) instLawfulNormedFieldOpsOfNormedField {K : Type v}
    [inst : NormedField K] : LawfulNormedFieldOps K where
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
  dist_eq := inst.dist_eq
  norm_mul := inst.norm_mul

example {K : Type v} [inst : NormedField K] :
    (instNormedFieldOfOps (R := ℝ) : NormedField K) = inst :=
  rfl

end NumLean
