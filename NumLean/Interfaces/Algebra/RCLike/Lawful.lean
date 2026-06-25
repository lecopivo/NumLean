import NumLean.Interfaces.Algebra.RCLike.Basic

namespace NumLean

private noncomputable def complexToRCLike {K : Type v} [RCLike K] (z : ℂ) : K :=
  (algebraMap ℝ K) z.re + (algebraMap ℝ K) z.im * RCLike.I

private noncomputable def rclikeToComplex {K : Type v} [RCLike K] (z : K) : ℂ where
  re := RCLike.re z
  im := RCLike.im z

@[hierarchy_graph]
noncomputable instance (priority := 100) instRCOpsOfRCLike {K : Type v} [inst : RCLike K] :
    RCOps ℝ K where
  le := RCLike.toPartialOrder.le
  lt := RCLike.toPartialOrder.lt
  le_refl := RCLike.toPartialOrder.le_refl
  le_trans := RCLike.toPartialOrder.le_trans
  lt_iff_le_not_ge := RCLike.toPartialOrder.lt_iff_le_not_ge
  le_antisymm := RCLike.toPartialOrder.le_antisymm
  smul := inst.smul
  algebraMap := algebraMap ℝ K
  rnorm x := ‖x‖
  zsmul := inst.zsmul
  intCast := inst.intCast
  zpow := inst.zpow
  nnqsmul := inst.nnqsmul
  qsmul := inst.qsmul
  make re im := (algebraMap ℝ K) re + (algebraMap ℝ K) im * RCLike.I
  re z := RCLike.re z
  im z := RCLike.im z
  I := RCLike.I
  cexp z := complexToRCLike (Complex.exp (rclikeToComplex z))
  csin z := complexToRCLike (Complex.sin (rclikeToComplex z))
  ccos z := complexToRCLike (Complex.cos (rclikeToComplex z))
  cpow z w := complexToRCLike (Complex.cpow (rclikeToComplex z) (rclikeToComplex w))

@[hierarchy_graph]
noncomputable instance (priority := 100) instLawfulDataRCOpsOfRCLike {K : Type v}
    [inst : RCLike K] : LawfulDataRCOps (R := ℝ) K where
  requiv := Equiv.refl ℝ
  rnorm_eq_norm _ := rfl
  completeSpace := inferInstance
  decEq := inferInstance
  reHom z := RCLike.re z
  imHom z := RCLike.im z

@[hierarchy_graph]
noncomputable instance (priority := 100) instLawfulRCOpsOfRCLike {K : Type v}
    [inst : RCLike K] : LawfulRCOps K where
  reHom_apply _ := rfl
  imHom_apply _ := rfl
  re_zero := RCLike.re.map_zero
  re_add := RCLike.re.map_add
  im_zero := RCLike.im.map_zero
  im_add := RCLike.im.map_add
  lt_norm_lt := inst.lt_norm_lt
  I_re := inst.I_re_ax
  I_mul_I := inst.I_mul_I_ax
  re_add_im := inst.re_add_im_ax
  re_add_im_algebraMap := inst.re_add_im_ax
  ofReal_re := by
    intro r
    change RCLike.re ((algebraMap ℝ K) r + (algebraMap ℝ K) 0 * RCLike.I) = r
    simp [inst.ofReal_re_ax]
  ofReal_im := by
    intro r
    change RCLike.im ((algebraMap ℝ K) r + (algebraMap ℝ K) 0 * RCLike.I) = 0
    simp [inst.ofReal_im_ax]
  ofReal_re_algebraMap := inst.ofReal_re_ax
  ofReal_im_algebraMap := inst.ofReal_im_ax
  mul_re := inst.mul_re_ax
  mul_im := inst.mul_im_ax
  star_star := star_star
  star_mul := star_mul
  star_add := StarRing.star_add
  conj_re := inst.conj_re_ax
  conj_im := inst.conj_im_ax
  conj_I := inst.conj_I_ax
  norm_sq_eq_def := inst.norm_sq_eq_def_ax
  mul_im_I := inst.mul_im_I_ax
  le_iff_re_im := inst.le_iff_re_im
  cexp_eq_ofComplex := by intro z; rfl
  csin_eq_ofComplex := by intro z; rfl
  ccos_eq_ofComplex := by intro z; rfl
  cpow_eq_ofComplex := by intro z w; rfl

@[hierarchy_graph]
noncomputable instance (priority := 100) instLawfulRCLikeOpsOfRCLike {K : Type v}
    [inst : RCLike K] : LawfulRCLikeOps K where
  re_apply _ := rfl
  im_apply _ := rfl
  re_add_im_algebraMap_real := inst.re_add_im_ax
  ofReal_re_algebraMap_real := inst.ofReal_re_ax
  ofReal_im_algebraMap_real := inst.ofReal_im_ax

@[hierarchy_graph]
instance (priority := 50) instStarRingOfRCOps {K : Type v} [RCOps ℝ K]
    [LawfulDataRCOps (R := ℝ) K] [LawfulNormedFieldOps K] [LawfulRCOps K] :
    StarRing K where
  star_involutive := LawfulRCOps.star_star
  star_mul := LawfulRCOps.star_mul
  star_add := LawfulRCOps.star_add

@[hierarchy_graph]
instance (priority := 50) instCompleteSpaceOfRCOps {K : Type v} [RCOps ℝ K]
    [LawfulDataRCOps (R := ℝ) K] : CompleteSpace K :=
  LawfulDataRCOps.completeSpace (R := ℝ) (K := K)

@[hierarchy_graph]
instance (priority := 50) instDecidableEqOfRCOps {K : Type v} [RCOps ℝ K]
    [LawfulDataRCOps (R := ℝ) K] : DecidableEq K :=
  LawfulDataRCOps.decEq (R := ℝ) (K := K)

@[hierarchy_graph]
instance (priority := 50) instDenselyNormedFieldOfRCOps {K : Type v} [RCOps ℝ K]
    [LawfulDataRCOps (R := ℝ) K] [LawfulNormedFieldOps K] [LawfulRCOps K] :
    DenselyNormedField K where
  lt_norm_lt := LawfulRCOps.lt_norm_lt

@[reducible]
noncomputable def rclikeOfRCOps (K : Type v) [RCOps ℝ K]
    [LawfulDataRCOps (R := ℝ) K] [LawfulNormedFieldOps K]
    [LawfulNormedAlgebraOps ℝ K] [LawfulRCLikeOps K] : RCLike K where
  algebraMap :=
    { toFun := NormedAlgebraOps.algebraMap (R := ℝ) (A := K)
      map_one' := LawfulNormedAlgebraOps.algebraMap_one
      map_mul' := LawfulNormedAlgebraOps.algebraMap_mul
      map_zero' := LawfulNormedAlgebraOps.algebraMap_zero
      map_add' := LawfulNormedAlgebraOps.algebraMap_add }
  commutes' := LawfulNormedAlgebraOps.smul_commutes
  smul_def' := LawfulNormedAlgebraOps.smul_def
  norm_smul_le := LawfulNormedAlgebraOps.norm_smul_le
  re :=
    { toFun := LawfulDataRCOps.reHom (R := ℝ)
      map_zero' := LawfulRCOps.re_zero
      map_add' := LawfulRCOps.re_add }
  im :=
    { toFun := LawfulDataRCOps.imHom (R := ℝ)
      map_zero' := LawfulRCOps.im_zero
      map_add' := LawfulRCOps.im_add }
  I := RCOps.I (R := ℝ) (K := K)
  I_re_ax := LawfulRCOps.I_re
  I_mul_I_ax := LawfulRCOps.I_mul_I
  re_add_im_ax := by
    intro z
    simpa only using LawfulRCLikeOps.re_add_im_algebraMap_real (K := K) z
  ofReal_re_ax := by
    intro r
    simpa only using LawfulRCLikeOps.ofReal_re_algebraMap_real (K := K) r
  ofReal_im_ax := by
    intro r
    simpa only using LawfulRCLikeOps.ofReal_im_algebraMap_real (K := K) r
  mul_re_ax := LawfulRCOps.mul_re
  mul_im_ax := LawfulRCOps.mul_im
  conj_re_ax := LawfulRCOps.conj_re
  conj_im_ax := LawfulRCOps.conj_im
  conj_I_ax := LawfulRCOps.conj_I
  norm_sq_eq_def_ax := LawfulRCOps.norm_sq_eq_def
  mul_im_I_ax := LawfulRCOps.mul_im_I
  toPartialOrder := inferInstance
  le_iff_re_im := LawfulRCOps.le_iff_re_im
  toDecidableEq := inferInstance

example {K : Type v} [inst : RCLike K] : rclikeOfRCOps K = inst :=
  rfl

noncomputable instance (priority := 100) instROpsOfRCLikeReal : ROps ℝ where
  toRCOps := instRCOpsOfRCLike (K := ℝ)
  exp := Real.exp
  sin := Real.sin
  cos := Real.cos
  pow x y := x ^ y
  log := Real.log
  sqrt := Real.sqrt

noncomputable instance (priority := 100) instLawfulDataROpsOfRCLikeReal :
    LawfulDataROps ℝ where
  toLawfulDataRCOps := instLawfulDataRCOpsOfRCLike (K := ℝ)

noncomputable instance (priority := 100) instLawfulROpsOfRCLikeReal :
    LawfulROps ℝ where
  toLawfulRCOps := instLawfulRCOpsOfRCLike (K := ℝ)
  algebraMap_eq_self _ := rfl
  norm_ofReal _ := rfl
  requiv_zero := rfl
  requiv_one := rfl
  requiv_add _ _ := rfl
  requiv_mul _ _ := rfl
  requiv_le _ _ := Iff.rfl
  re_eq _ := rfl
  im_eq_zero _ := rfl
  I_eq_zero := by
    change RCLike.I = 0
    exact RCLike.I_to_real
  make_eq_re := by
    intro x y
    change (algebraMap ℝ ℝ) x + (algebraMap ℝ ℝ) y * RCLike.I = x
    simp [RCLike.I_to_real]
  lt_iff_toReal_lt := by
    intro x y
    rfl
  exp_eq_ofReal _ := rfl
  sin_eq_ofReal _ := rfl
  cos_eq_ofReal _ := rfl
  pow_eq_ofReal _ _ := rfl
  log_eq_ofReal _ := rfl
  sqrt_eq_ofReal _ := rfl

example : rclikeOfRCOps ℝ = (inferInstance : RCLike ℝ) :=
  rfl

noncomputable example [ROps ℝ] [LawfulDataROps ℝ] [LawfulROps ℝ] : RCLike ℝ := by
  infer_instance


@[reducible]
noncomputable def inferRCLike (R : Type u) [ROps R] [LawfulDataROps R] [LawfulROps R] : RCLike R :=
  { instNormedFieldOfOps (R := R) with
    star_involutive := LawfulRCOps.star_star (R := R) (K := R)
    star_mul := LawfulRCOps.star_mul (R := R) (K := R)
    star_add := LawfulRCOps.star_add (R := R) (K := R)
    smul := fun r x => ROps.ofReal (R := R) r * x
    algebraMap :=
      { toFun := ROps.ofReal (R := R)
        map_one' := by
          apply (LawfulDataRNorm.requiv (E := R)).injective
          simpa [ROps.ofReal] using (LawfulROps.requiv_one (R := R)).symm
        map_mul' := by
          intro x y
          apply (LawfulDataRNorm.requiv (E := R)).injective
          rw [LawfulROps.requiv_mul]
          simp [ROps.ofReal]
        map_zero' := by
          apply (LawfulDataRNorm.requiv (E := R)).injective
          simpa [ROps.ofReal] using (LawfulROps.requiv_zero (R := R)).symm
        map_add' := by
          intro x y
          apply (LawfulDataRNorm.requiv (E := R)).injective
          rw [LawfulROps.requiv_add]
          simp [ROps.ofReal] }
    commutes' := by
      intro r x
      exact mul_comm _ _
    smul_def' := by
      intro r x
      rfl
    norm_smul_le := by
      intro r x
      calc
        ‖ROps.ofReal (R := R) r * x‖ ≤ ‖ROps.ofReal (R := R) r‖ * ‖x‖ :=
          norm_mul_le _ _
        _ = ‖r‖ * ‖x‖ := by rw [LawfulROps.norm_ofReal]
    complete := LawfulDataRCOps.completeSpace (R := R) (K := R) |>.complete
    lt_norm_lt := LawfulRCOps.lt_norm_lt
    re :=
      { toFun := LawfulDataRCOps.reHom (R := R)
        map_zero' := LawfulRCOps.re_zero
        map_add' := LawfulRCOps.re_add }
    im :=
      { toFun := LawfulDataRCOps.imHom (R := R)
        map_zero' := LawfulRCOps.im_zero
        map_add' := LawfulRCOps.im_add }
    I := RCOps.I (R := R) (K := R)
    I_re_ax := LawfulRCOps.I_re
    I_mul_I_ax := LawfulRCOps.I_mul_I
    re_add_im_ax := by
      intro z
      change ROps.ofReal (LawfulDataRCOps.reHom (R := R) z) +
          ROps.ofReal (LawfulDataRCOps.imHom (R := R) z) * RCOps.I (R := R) (K := R) = z
      rw [LawfulROps.re_eq, LawfulROps.im_eq_zero, LawfulROps.I_eq_zero]
      simp [ROps.toReal, ROps.ofReal]
    ofReal_re_ax := by
      intro r
      change LawfulDataRCOps.reHom (R := R) (ROps.ofReal (R := R) r) = r
      rw [LawfulROps.re_eq]
      simp [ROps.toReal, ROps.ofReal]
    ofReal_im_ax := by
      intro r
      change LawfulDataRCOps.imHom (R := R) (ROps.ofReal (R := R) r) = 0
      rw [LawfulROps.im_eq_zero]
    mul_re_ax := LawfulRCOps.mul_re
    mul_im_ax := LawfulRCOps.mul_im
    conj_re_ax := LawfulRCOps.conj_re
    conj_im_ax := LawfulRCOps.conj_im
    conj_I_ax := LawfulRCOps.conj_I
    norm_sq_eq_def_ax := LawfulRCOps.norm_sq_eq_def
    mul_im_I_ax := LawfulRCOps.mul_im_I
    toPartialOrder := inferInstance
    le_iff_re_im := LawfulRCOps.le_iff_re_im
    toDecidableEq := LawfulDataRCOps.decEq (R := R) (K := R) }

noncomputable example {R : Type u} [ROps R] [LawfulDataROps R] [LawfulROps R] : RCLike R :=
  inferRCLike R


end NumLean
