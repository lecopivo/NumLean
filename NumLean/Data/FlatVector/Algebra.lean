import NumLean.Data.FlatVector.Ops
import NumLean.Algebra.Instances
import Mathlib.Analysis.Normed.Lp.PiLp

namespace NumLean.FlatVector

variable {X : Type u} {I : Type v}
  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatVector X Ks nX] [IndexType I nI]
  [RingArrayOps Ks]

-- [BLASOps Ks K]

-- example [Ring K] : AddGroupOps K := by infer_instance
-- example [Ring K] : GroupOps K := by infer_instance

-- [NatCast K] [IntCast K] [FieldOps K] [BLASOps Ks K]
instance [Ring K] [AddCommMonoid X] [Module K X]
    [LawfulRingArrayOps Ks]
    [FlatRepr.LawfulAdd (nX := nX) X K]
    [FlatRepr.LawfulZero (nX := nX) X K]
    [FlatRepr.LawfulSMul (nX := nX) K X K] :
    AddCommMonoid (FlatVector X I) where
  add_assoc := by intros; ext; simp [add_assoc]
  add_comm := by intros; ext; simp [add_comm]
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
  nsmul n x := (n : K) • x
  nsmul_zero := by intros; ext; simp
  nsmul_succ := by intros; ext; simp [add_smul]

-- example ... assumptions with a clear split between data and props ... : AddCommMonoid (FlatVector X I) := by infer_instance

instance instAddCommGroup [CommRing K] [AddCommGroup X] [Module K X]
    [LawfulRingArrayOps Ks]
    [FlatRepr.LawfulAdd (nX := nX) X K]
    [FlatRepr.LawfulZero (nX := nX) X K]
    [FlatRepr.LawfulSMul (nX := nX) K X K]
    [FlatRepr.LawfulSub (nX := nX) X K] :
    AddCommGroup (FlatVector X I) where
  sub_eq_add_neg := by intros; ext; simp [sub_eq_add_neg]
  neg_add_cancel := by intros; ext; simp
  zsmul n x := (n : K) • x
  zsmul_neg' := by intros; ext; simp [add_smul]
  zsmul_zero' := by intros; ext; simp
  zsmul_succ' := by intros; ext; simp [add_smul]

-- example ... assumptions with a clear split between data and props ... : AddCommGroup (FlatVector X I) := by infer_instance

instance [Ring K] [AddCommMonoid X] [Module K X]
    [LawfulRingArrayOps Ks]
    [FlatRepr.LawfulAdd (nX := nX) X K]
    [FlatRepr.LawfulZero (nX := nX) X K]
    [FlatRepr.LawfulSMul (nX := nX) K X K] :
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
    [LawfulRingArrayOps Ks]
    [FlatRepr.LawfulAdd (nX := nX) X K]
    [FlatRepr.LawfulZero (nX := nX) X K]
    [FlatRepr.LawfulSMul (nX := nX) K X K]
    [FlatRepr.LawfulSub (nX := nX) X K] :
    NormedAddCommGroup (FlatVector X I) where
  norm xs := Real.sqrt (∑ i : I, ‖xs[i]‖^2)
  dist_self := by intros; simp
  dist_comm := by
    intros;
    simp only [← sub_eq_neg_add, getElem_sub]
    simp only [norm_sub_rev]
  dist_triangle := by
    intro x y z
    simp only [← sub_eq_neg_add, getElem_sub]
    let toLp : FlatVector X I → PiLp 2 (fun _ : I ↦ X) :=
      fun xs ↦ WithLp.toLp 2 fun i ↦ xs[i]
    simpa [toLp, PiLp.dist_eq_sum, PiLp.norm_eq_sum, Real.sqrt_eq_rpow, dist_eq_norm', one_div] using
      dist_triangle (toLp x) (toLp y) (toLp z)
  eq_of_dist_eq_zero := by
    intro x y hxy
    ext i
    simp only [← sub_eq_neg_add, getElem_sub] at hxy
    have hsum : ∑ j : I, ‖y[j] - x[j]‖ ^ 2 = 0 := by
      exact (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).mp hxy
    have hi : ‖y[i] - x[i]‖ ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).mp hsum i (Finset.mem_univ i)
    have hnorm : ‖y[i] - x[i]‖ = 0 := by
      exact sq_eq_zero_iff.mp hi
    exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

section Normed

variable [CommRing K] [NormedAddCommGroup X] [Module K X]
    [LawfulRingArrayOps Ks]
    [FlatRepr.LawfulAdd (nX := nX) X K]
    [FlatRepr.LawfulZero (nX := nX) X K]
    [FlatRepr.LawfulSMul (nX := nX) K X K]
    [FlatRepr.LawfulSub (nX := nX) X K]

theorem norm_eq_sqrt_sum (xs : FlatVector X I) : ‖xs‖ = Real.sqrt (∑ i : I, ‖xs[i]‖^2) := by rfl

end Normed

instance [NormedField K] [NormedAddCommGroup X] [NormedSpace K X]
    [LawfulRingArrayOps Ks]
    [FlatRepr.LawfulAdd (nX := nX) X K]
    [FlatRepr.LawfulZero (nX := nX) X K]
    [FlatRepr.LawfulSMul (nX := nX) K X K]
    [FlatRepr.LawfulSub (nX := nX) X K] :
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

theorem dist_getElem_le_dist [CommRing K] [NormedAddCommGroup X] [Module K X]
    [LawfulRingArrayOps Ks]
    [FlatRepr.LawfulAdd (nX := nX) X K]
    [FlatRepr.LawfulZero (nX := nX) X K]
    [FlatRepr.LawfulSMul (nX := nX) K X K]
    [FlatRepr.LawfulSub (nX := nX) X K]
    (i : I) (xs ys : FlatVector X I) : dist xs[i] ys[i] ≤ dist xs ys := by
  classical
  rw [dist_eq_norm', dist_eq_norm', norm_eq_sqrt_sum]
  simp only [getElem_sub]
  exact Real.le_sqrt_of_sq_le <|
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖ys[j] - xs[j]‖) (Finset.mem_univ i)

theorem continuous_getElem [CommRing K] [NormedAddCommGroup X] [Module K X]
    [LawfulRingArrayOps Ks]
    [FlatRepr.LawfulAdd (nX := nX) X K]
    [FlatRepr.LawfulZero (nX := nX) X K]
    [FlatRepr.LawfulSMul (nX := nX) K X K]
    [FlatRepr.LawfulSub (nX := nX) X K]
    (i : I) : Continuous fun xs : FlatVector X I ↦ xs[i] := by
  rw [Metric.continuous_iff]
  intro xs ε hε
  refine ⟨ε, hε, ?_⟩
  intro ys hys
  exact lt_of_le_of_lt (dist_getElem_le_dist (i := i) ys xs) hys
