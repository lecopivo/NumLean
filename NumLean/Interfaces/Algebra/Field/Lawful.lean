import NumLean.Interfaces.Algebra.Field.Basic
import NumLean.Interfaces.Algebra.Ring.Lawful

namespace NumLean
namespace Interfaces
namespace Algebra

@[hierarchy_graph]
instance (priority := 100) instFieldOpsOfField {K : Type u} [inst : _root_.Field K] :
    FieldOps K where
  nsmul := inst.nsmul
  npow := inst.npow
  zsmul := inst.zsmul
  zpow := inst.zpow
  nnqsmul := inst.nnqsmul
  qsmul := inst.qsmul

@[hierarchy_graph]
instance (priority := 100) instLawfulFieldOpsOfField {K : Type u} [inst : _root_.Field K] :
    LawfulFieldOps K where
  add_assoc := inst.add_assoc
  zero_add := inst.zero_add
  add_zero := inst.add_zero
  nsmul_zero := inst.nsmul_zero
  nsmul_succ := inst.nsmul_succ
  mul_assoc := inst.mul_assoc
  one_mul := inst.one_mul
  mul_one := inst.mul_one
  npow_zero := inst.npow_zero
  npow_succ := inst.npow_succ
  add_comm := inst.add_comm
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

@[hierarchy_graph]
instance (priority := 50) instFieldOfOps {K : Type u} [inst : FieldOps K] [LawfulFieldOps K] :
    _root_.Field K where
  mul_comm := LawfulMonoidOps.mul_comm
  div_eq_mul_inv := LawfulFieldOps.div_eq_mul_inv
  zpow := inst.zpow
  zpow_zero' := LawfulFieldOps.zpow_zero
  zpow_succ' := LawfulFieldOps.zpow_succ
  zpow_neg' := LawfulFieldOps.zpow_neg
  exists_pair_ne := LawfulFieldOps.exists_pair_ne
  mul_inv_cancel := LawfulFieldOps.mul_inv_cancel
  inv_zero := LawfulFieldOps.inv_zero
  nnratCast_def := LawfulFieldOps.nnratCast_def
  nnqsmul := inst.nnqsmul
  nnqsmul_def := LawfulFieldOps.nnqsmul_def
  ratCast_def := LawfulFieldOps.ratCast_def
  qsmul := inst.qsmul
  qsmul_def := LawfulFieldOps.qsmul_def

example {K : Type u} [inst : _root_.Field K] :
    (instFieldOfOps : _root_.Field K) = inst :=
  rfl

end Algebra
end Interfaces
end NumLean
