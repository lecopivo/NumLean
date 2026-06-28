module

public import NumLean.Interfaces.Algebra.NormedAlgebra.Basic

@[expose] public section

namespace NumLean

@[hierarchy_graph]
instance (priority := 30) instAlgebraOfOps {RR RA R A}
    [NormedFieldOps RR R] [NormedRingOps RA A] [NormedAlgebraOps R A]
    [LawfulDataNormedFieldOps R] [LawfulNormedFieldOps R]
    [LawfulDataNormedRingOps A] [LawfulNormedRingOps A] [LawfulNormedAlgebraOps R A] :
    Algebra R A where
  algebraMap :=
    { toFun := NormedAlgebraOps.algebraMap (R := R) (A := A)
      map_one' := LawfulNormedAlgebraOps.algebraMap_one
      map_mul' := LawfulNormedAlgebraOps.algebraMap_mul
      map_zero' := LawfulNormedAlgebraOps.algebraMap_zero
      map_add' := LawfulNormedAlgebraOps.algebraMap_add }
  commutes' := LawfulNormedAlgebraOps.smul_commutes
  smul_def' := LawfulNormedAlgebraOps.smul_def

@[hierarchy_graph]
instance (priority := 30) instNormedAlgebraOfOps {RR RA R A}
    [NormedFieldOps RR R] [NormedRingOps RA A] [NormedAlgebraOps R A]
    [LawfulDataNormedFieldOps R] [LawfulNormedFieldOps R]
    [LawfulDataNormedRingOps A] [LawfulNormedRingOps A] [LawfulNormedAlgebraOps R A] :
    NormedAlgebra R A where
  norm_smul_le := LawfulNormedAlgebraOps.norm_smul_le

@[hierarchy_graph]
instance (priority := 50) instNormedAlgebraOpsOfNormedAlgebra {K : Type u} {A : Type v}
    [NormedField K] [SeminormedRing A] [inst : NormedAlgebra K A] : NormedAlgebraOps K A where
  smul := inst.smul
  algebraMap := algebraMap K A

@[hierarchy_graph]
instance (priority := 50) instLawfulNormedAlgebraOpsOfNormedAlgebra {K : Type u} {A : Type v}
    [instK : NormedField K] [instA : NormedCommRing A] [inst : NormedAlgebra K A] :
    LawfulNormedAlgebraOps K A where
  smul_zero := smul_zero
  zero_smul := zero_smul _
  one_smul := one_smul _
  mul_smul := mul_smul
  smul_add := smul_add
  add_smul := add_smul
  algebraMap_zero := by
    simpa only [instNormedAlgebraOpsOfNormedAlgebra] using map_zero (algebraMap K A)
  algebraMap_one := by
    simpa only [instNormedAlgebraOpsOfNormedAlgebra] using map_one (algebraMap K A)
  algebraMap_add := by
    intro r s
    simpa only [instNormedAlgebraOpsOfNormedAlgebra] using map_add (algebraMap K A) r s
  algebraMap_mul := by
    intro r s
    simpa only [instNormedAlgebraOpsOfNormedAlgebra] using map_mul (algebraMap K A) r s
  smul_def := by
    intro r x
    simpa only [instNormedAlgebraOpsOfNormedAlgebra] using inst.smul_def' r x
  smul_commutes := by
    intro r x
    simpa only [instNormedAlgebraOpsOfNormedAlgebra] using inst.commutes' r x
  norm_smul_le := inst.norm_smul_le

example {K : Type u} {A : Type v} [instK : NormedField K] [instA : NormedCommRing A]
    [inst : NormedAlgebra K A] :
    (instAlgebraOfOps (RR := ℝ) (RA := ℝ) : Algebra K A) = inst.toAlgebra :=
  rfl

example {K : Type u} {A : Type v} [instK : NormedField K] [instA : NormedCommRing A]
    [inst : NormedAlgebra K A] :
    (instNormedAlgebraOfOps (RR := ℝ) (RA := ℝ) : NormedAlgebra K A) = inst :=
  rfl

end NumLean
