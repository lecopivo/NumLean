import Mathlib.Analysis.Normed.Module.Basic
import NumLean.Interfaces.Algebra.NormedField

namespace NumLean

@[hierarchy_graph algebra_ops]
class NormedAlgebraOps (R : Type u) (A : Type v) extends SMul R A where
  algebraMap : R → A

@[hierarchy_graph algebra_lawful]
class LawfulNormedAlgebraOps {RR : outParam (Type u)} {RA : outParam (Type v)}
    (R : Type w) (A : Type x) [NormedFieldOps RR R] [NormedRingOps RA A]
    [NormedAlgebraOps R A] [LawfulDataNormedFieldOps R] [LawfulDataNormedRingOps A] : Prop where
  smul_zero : ∀ r : R, r • (0 : A) = 0
  zero_smul : ∀ x : A, (0 : R) • x = 0
  one_smul : ∀ x : A, (1 : R) • x = x
  mul_smul : ∀ r s : R, ∀ x : A, (r * s) • x = r • s • x
  smul_add : ∀ r : R, ∀ x y : A, r • (x + y) = r • x + r • y
  add_smul : ∀ r s : R, ∀ x : A, (r + s) • x = r • x + s • x
  algebraMap_zero : NormedAlgebraOps.algebraMap (R := R) (A := A) 0 = 0
  algebraMap_one : NormedAlgebraOps.algebraMap (R := R) (A := A) 1 = 1
  algebraMap_add : ∀ r s : R, NormedAlgebraOps.algebraMap (R := R) (A := A) (r + s) =
    NormedAlgebraOps.algebraMap r + NormedAlgebraOps.algebraMap s
  algebraMap_mul : ∀ r s : R, NormedAlgebraOps.algebraMap (R := R) (A := A) (r * s) =
    NormedAlgebraOps.algebraMap r * NormedAlgebraOps.algebraMap s
  smul_def : ∀ r : R, ∀ x : A, r • x = NormedAlgebraOps.algebraMap (R := R) (A := A) r * x
  smul_commutes : ∀ r : R, ∀ x : A,
    NormedAlgebraOps.algebraMap (R := R) (A := A) r * x =
      x * NormedAlgebraOps.algebraMap (R := R) (A := A) r
  norm_smul_le : ∀ r : R, ∀ x : A, ‖r • x‖ ≤ ‖r‖ * ‖x‖

end NumLean
