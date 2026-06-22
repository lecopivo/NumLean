import NumLean.Interfaces.Algebra.NormedRing.Basic

namespace NumLean

instance (priority := 50) instNormedCommRingOfOps {R K} [NormedRingOps R K]
    [LawfulDataNormedRingOps K] [LawfulNormedRingOps K] : NormedCommRing K where
  dist_eq := LawfulNormedRingOps.dist_eq
  norm_mul_le := LawfulNormedRingOps.norm_mul_le
  mul_comm := NumLean.Interfaces.Algebra.LawfulMonoidOps.mul_comm

instance (priority := 100) instNormedRingOpsOfNormedCommRing {K : Type v}
    [inst : NormedCommRing K] : NormedRingOps ℝ K where
  rnorm x := ‖x‖
  zsmul := inst.zsmul
  intCast := inst.intCast

instance (priority := 100) instLawfulDataNormedRingOpsOfNormedCommRing {K : Type v}
    [inst : NormedCommRing K] : LawfulDataNormedRingOps K where
  requiv := Equiv.refl ℝ
  rnorm_eq_norm _ := rfl

instance (priority := 100) instLawfulNormedRingOpsOfNormedCommRing {K : Type v}
    [inst : NormedCommRing K] : LawfulNormedRingOps K where
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
  dist_eq := inst.dist_eq
  norm_mul_le := inst.norm_mul_le

example {K : Type v} [inst : NormedCommRing K] :
    (instNormedCommRingOfOps (R := ℝ) : NormedCommRing K) = inst :=
  rfl

end NumLean
