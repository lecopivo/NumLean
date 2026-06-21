import NumLean.Data.FlatVector.Ops
import NumLean.Algebra.Instances

namespace NumLean.FlatVector

variable {X : Type u} {I : Type v}
  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatVector X Ks nX] [IndexType I nI] [BLASOps Ks K]

-- [BLASOps Ks K]

-- example [Ring K] : AddGroupOps K := by infer_instance
-- example [Ring K] : GroupOps K := by infer_instance

-- [NatCast K] [IntCast K] [FieldOps K] [BLASOps Ks K]
instance [Semiring K] [AddCommMonoid X] [Module K X]
    [FlatRepr.LawfulAdd X K] [FlatRepr.LawfulZero X K] [FlatRepr.LawfulSMul K X K] :
    AddCommMonoid (FlatVector X I) where
  add_assoc := by intros; ext; simp [add_assoc]
  add_comm := by intros; ext; simp [add_comm]
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
  nsmul n x := (n : K) • x
  nsmul_zero := by intros; ext; simp
  nsmul_succ := by intros; ext; simp [add_smul]

-- example ... assumptions with a clear split between data and props ... : AddCommMonoid (FlatVector X I) := by infer_instance

instance [CommRing K] [AddCommGroup X] [Module K X]
    [FlatRepr.LawfulAdd X K] [FlatRepr.LawfulZero X K] [FlatRepr.LawfulSMul K X K]
    [FlatRepr.LawfulSub X K] :
    AddCommGroup (FlatVector X I) where
  sub_eq_add_neg := by intros; ext; simp [sub_eq_add_neg]
  neg_add_cancel := by intros; ext; simp
  zsmul n x := (n : K) • x
  zsmul_neg' := by intros; ext; simp [add_smul]
  zsmul_zero' := by intros; ext; simp
  zsmul_succ' := by intros; ext; simp [add_smul]

-- example ... assumptions with a clear split between data and props ... : AddCommGroup (FlatVector X I) := by infer_instance

instance [Semiring K] [AddCommMonoid X] [Module K X]
    [FlatRepr.LawfulAdd X K] [FlatRepr.LawfulZero X K] [FlatRepr.LawfulSMul K X K] :
    Module K (FlatVector X I) where
  mul_smul := by intros; ext; simp [mul_smul]
  one_smul := by intros; ext; simp
  smul_zero := by intros; ext; simp
  smul_add := by intros; ext; simp
  add_smul := by intros; ext; simp [add_smul]
  zero_smul := by intros; ext; simp

-- example ... assumptions with a clear split between data and props ... : Module K (FlatVector X I) := by infer_instance

noncomputable
instance [CommRing K] [NormedAddCommGroup X] [Module K X]
    [FlatRepr.LawfulAdd X K] [FlatRepr.LawfulZero X K] [FlatRepr.LawfulSMul K X K]
    [FlatRepr.LawfulSub X K] :
    NormedAddCommGroup (FlatVector X I) where
  norm xs := Real.sqrt (∑ i : I, ‖xs[i]‖^2)
  dist_self := by intros; simp
  dist_comm := by
    intros;
    simp only [← sub_eq_neg_add, getElem_sub]
    have h : ∀ x y : X, x - y = - (y - x) := sorry
    simp only [norm_sub_rev]
  dist_triangle := by
    intros
    sorry
  eq_of_dist_eq_zero := by
    intros
    sorry

section Normed

variable [CommRing K] [NormedAddCommGroup X] [Module K X]
    [FlatRepr.LawfulAdd X K] [FlatRepr.LawfulZero X K] [FlatRepr.LawfulSMul K X K]
    [FlatRepr.LawfulSub X K]

theorem norm_eq_sqrt_sum (xs : FlatVector X I) : ‖xs‖ = Real.sqrt (∑ i : I, ‖xs[i]‖^2) := by rfl

end Normed

instance [NormedField K] [NormedAddCommGroup X] [NormedSpace K X]
    [FlatRepr.LawfulAdd X K] [FlatRepr.LawfulZero X K] [FlatRepr.LawfulSMul K X K]
    [FlatRepr.LawfulSub X K] :
    NormedSpace K (FlatVector X I) where
  norm_smul_le := by
    intros
    rw [norm_eq_sqrt_sum]
    simp [norm_smul, mul_pow, ← Finset.mul_sum]
    rw [← norm_eq_sqrt_sum]

-- We aim to have this
-- example {X : Type u} {I : Type v}
--   [VectorType Ks K] [HasDefaultFlatVector X Ks nX] [IndexType I nI] [BLASOps Ks K]
--   [ROps K] [AddGroupOps X] [SMul K X] -- data
--         -- lawfulnesss -- these all should be prop!!! probably we need one data that maps K to real!
--         -- K behaves like ℝ, or better is a Field that is a module over ℝ
--         -- X behaves like ℝ and K module
--   : NormedSpace (FlatVector X I) := by infer_instance

-- we should also show that there is with naive implementation!
-- `(FloatVector X I) ≃L[K] Fin (nI * nX) → K`
