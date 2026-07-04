module

public import NumLean.Data.Tensor.Algebra.Ops
public import NumLean.Data.Tensor.Algebra.VMul
public import NumLean.Interfaces.TensorAlgebra
public import NumLean.Interfaces.Module.Lawful
public import NumLean.Interfaces.HasFlatRepr.Lawful
public import NumLean.Interfaces.UntypedIndex
public import NumLean.Interfaces.Algebra.Ring.Lawful
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace NumLean.Tensor

open Tensor


variable {X : Type u} {I : Type v}
  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX] [IndexType I nI]


@[simp]
theorem getElem_zero [Zero K] [Zero X] [HasFlatRepr.LawfulZero X Ks] (i : I) :
    (0 : Tensor X I)[i] = 0 := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j h
  conv_lhs => simp only [getComp_getElem_eq_get]; simp [Zero.zero, OfNat.ofNat]
  simp [HasFlatRepr.LawfulZero.getComp_zero]
  rfl


@[simp]
theorem getElem_one [One K] [One X] [HasFlatRepr.LawfulOne X Ks] (i : I) :
    (1 : Tensor X I)[i] = 1 := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j h
  conv_lhs => simp only [getComp_getElem_eq_get]; simp [One.one, OfNat.ofNat]
  simp [HasFlatRepr.LawfulOne.getComp_one]
  rfl


open TensorRingOps
@[simp]
theorem getElem_add [CommRing K] [AddMonoid X] [SMul K X] [HasFlatRepr.LawfulAdd X Ks]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    (xs ys : Tensor X I) (i : I) :
    (xs + ys)[i] = xs[i] + ys[i] := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j h
  simp [- get_tensorAxpy, HasFlatRepr.LawfulAdd.getComp_add, add_def]


@[simp]
theorem getElem_sub [CommRing K] [AddCommGroup X] [SMul K X] [HasFlatRepr.LawfulSub X Ks]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    (xs ys : Tensor X I) (i : I) :
    (xs - ys)[i] = xs[i] - ys[i] := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j h
  simp [- get_tensorAxpy, HasFlatRepr.LawfulSub.getComp_sub, sub_def, ←sub_eq_add_neg]


@[simp]
theorem getElem_smul [CommRing K] [SMul K X] [HasFlatRepr.LawfulSMul K X Ks]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    (k : K) (xs : Tensor X I) (i : I) :
    (k • xs)[i] = k • xs[i] := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j h
  simp [- get_tensorScal, HasFlatRepr.LawfulSMul.getComp_smul, smul_def]


@[simp]
theorem getElem_neg [CommRing K] [Neg X] [SMul K X]
    [HasFlatRepr.LawfulSMul K X Ks] [HasFlatRepr.LawfulNeg X Ks]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    (xs : Tensor X I) (i : I) :
    (- xs)[i] = - xs[i] := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j h
  simp [- get_tensorScal, HasFlatRepr.LawfulSMul.getComp_smul, HasFlatRepr.LawfulNeg.getComp_neg, neg_def]


instance instAddMonoid
    [CommRing K] [AddCommMonoid X] [Module K X] [HasFlatRepr.LawfulAddMonoidOps X Ks]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K] :
    AddCommMonoid (Tensor X I) where
  add_assoc := by intros; ext; simp [add_assoc]
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
  nsmul := Interfaces.Algebra.AddMonoidOps.nsmul
  nsmul_zero := by
    intro x
    ext i
    simp [_root_.NumLean.Interfaces.Algebra.AddMonoidOps.nsmul]
  nsmul_succ := by
    intro n x
    ext i
    simp [_root_.NumLean.Interfaces.Algebra.AddMonoidOps.nsmul]
    rw [add_smul]
    simp
  add_comm := by intros; ext; simp [add_comm]


instance instAddCommGroup
    [CommRing K] [AddCommGroup X] [Module K X] [HasFlatRepr.LawfulAddGroupOps X Ks]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K] :
    AddCommGroup (Tensor X I) where
  neg_add_cancel := by intros; ext; simp
  sub_eq_add_neg :=  by intros; ext; simp [sub_eq_add_neg]
  zsmul :=  Interfaces.Algebra.AddGroupOps.zsmul
  zsmul_zero' := by intro a; ext i; simp [Interfaces.Algebra.AddGroupOps.zsmul]
  zsmul_succ' := by intro n a; ext i; simp [Interfaces.Algebra.AddGroupOps.zsmul, Nat.cast_add, add_smul]
  zsmul_neg' := by
    intro n a; ext i; simp [Interfaces.Algebra.AddGroupOps.zsmul]
    rw [← neg_smul]; congr 1; ring


instance instModule
    [CommRing K] [AddCommMonoid X] [Module K X] [HasFlatRepr.LawfulAddMonoidOps X Ks]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K] :
    Module K (Tensor X I) where
  mul_smul := by intros; ext; simp [mul_smul]
  one_smul := by intros; ext; simp
  smul_zero := by intros; ext; simp
  smul_add := by intros; ext; simp
  add_smul := by intros; ext; simp [add_smul]
  zero_smul := by intros; ext; simp


noncomputable
instance [CommRing K] [NormedAddCommGroup X] [Module K X]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) X Ks] :
    NormedAddCommGroup (Tensor X I) where
  norm xs := Real.sqrt (∑ i : I, ‖xs[i]‖^2)
  dist_self := by intros; simp
  dist_comm := by
    intros
    simp only [← sub_eq_neg_add, getElem_sub]
    simp only [norm_sub_rev]
  dist_triangle := by
    intro x y z
    simp only [← sub_eq_neg_add, getElem_sub]
    let toLp : Tensor X I → PiLp 2 (fun _ : I ↦ X) :=
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
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    [HasFlatRepr.LawfulAddGroupOps X Ks]

theorem norm_eq_sqrt_sum (xs : Tensor X I) : ‖xs‖ = Real.sqrt (∑ i : I, ‖xs[i]‖^2) := by
  rfl

end Normed


noncomputable
instance [NormedField K] [NormedAddCommGroup X] [NormedSpace K X]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) X Ks] :
    NormedSpace K (Tensor X I) where
  norm_smul_le := by
    intros
    rw [norm_eq_sqrt_sum]
    simp [norm_smul, mul_pow, ← Finset.mul_sum]
    rw [← norm_eq_sqrt_sum]

noncomputable
instance [RCLike K] [NormedAddCommGroup X] [InnerProductSpace K X]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) X Ks]
    [HasFlatRepr.LawfulInner X Ks] :
    InnerProductSpace K (Tensor X I) where
  inner x y := ∑ i : I, inner K x[i] y[i]
  norm_sq_eq_re_inner := by
    intro x
    rw [norm_eq_sqrt_sum, Real.sq_sqrt]
    · simp [map_sum]
    · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  conj_inner_symm := by
    intro x y
    simp [map_sum, inner_conj_symm]
  add_left := by
    intro x y z
    simp [inner_add_left, Finset.sum_add_distrib]
  smul_left := by
    intro x y r
    simp [inner_smul_left, Finset.mul_sum]

theorem norm_getElem_sq_eq_sum_getComp [RCLike K] [NormedAddCommGroup X] [InnerProductSpace K X]
    [HasFlatRepr.LawfulInner X Ks] (x : Tensor X I) (i : I) :
    ‖x[i]‖ ^ 2 = ∑ j : Fin nX, ‖x.getComp i j.1 j.2‖ ^ 2 := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner K X _ _ _ (x[i])]
  rw [@HasFlatRepr.LawfulInner.inner_eq_sum X Ks K nX _ _ _ _ _ (x[i]) (x[i])]
  simp [map_sum, RCLike.conj_mul, Tensor.getComp, getComp_getElem_eq_get]

open IndexType in
noncomputable def euclideanToFun [RCLike K] (x : Tensor X I) :
    EuclideanSpace K (Fin nI × Fin nX) :=
  WithLp.toLp 2 (fun (i,j) => x.getComp (fromFin i) j.1 j.2)

open IndexType in
def euclideanInvFun [Zero X] (x : EuclideanSpace K (Fin nI × Fin nX)) : Tensor X I :=
  letI : Inhabited X := ⟨0⟩
  Tensor.ofFn (fun i => HasFlatRepr.fromVector Ks (.ofFn fun j => x ((toFin i),j)))

open IndexType in
@[simp]
theorem getComp_euclideanInvFun [Zero X] (x : EuclideanSpace K (Fin nI × Fin nX))
    (i : I) (j : Nat) (hj : j < nX) :
    (euclideanInvFun (X := X) (I := I) (Ks := Ks) x).getComp i j hj =
      x (toFin i, ⟨j, hj⟩) := by
  letI : Inhabited X := ⟨0⟩
  calc
    (euclideanInvFun (X := X) (I := I) (Ks := Ks) x).getComp i j hj =
        HasFlatRepr.getComp (Ks := Ks) ((euclideanInvFun (X := X) (I := I) (Ks := Ks) x)[i]) j hj := by
      exact (getComp_getElem_eq_get (xs := euclideanInvFun (X := X) (I := I) (Ks := Ks) x) i j hj).symm
    _ = x (toFin i, ⟨j, hj⟩) := by
      unfold euclideanInvFun
      rw [getElem_ofFn]
      simp [HasFlatRepr.getComp_spec]

open IndexType in
def toEuclidean [RCLike K] (x : Tensor X I) : EuclideanSpace X (Fin nI) :=
  WithLp.toLp 2 fun i => x[fromFin (I := I) i]

open IndexType in
def fromEuclidean [Zero X] (x : EuclideanSpace X (Fin nI)) : Tensor X I :=
  letI : Inhabited X := ⟨0⟩
  Tensor.ofFn fun i => x (toFin i)

open IndexType in
def euclideanEquiv [RCLike K] [NormedAddCommGroup X] [InnerProductSpace K X]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) X Ks]
    [HasFlatRepr.LawfulInner X Ks] :
    Tensor X I ≃ₗᵢ[K] EuclideanSpace X (Fin nI) where
  toFun := toEuclidean (X := X) (I := I) (Ks := Ks)
  invFun := fromEuclidean (X := X) (I := I) (Ks := Ks)
  left_inv := by
    intro x
    ext i
    simp [toEuclidean, fromEuclidean, IndexType.fromFin_toFin]
  right_inv := by
    intro x
    ext i
    simp [toEuclidean, fromEuclidean, IndexType.toFin_fromFin]
  map_add' := by
    intro x y
    ext i
    simp [toEuclidean]
  map_smul' := by
    intro k x
    ext i
    simp [toEuclidean]
  norm_map' := by
    intro x
    change ‖toEuclidean (X := X) (I := I) (Ks := Ks) x‖ = ‖x‖
    rw [norm_eq_sqrt_sum]
    have hnorm := PiLp.norm_eq_sum (show 0 < (2 : ENNReal).toReal by norm_num)
      (toEuclidean (X := X) (I := I) (Ks := Ks) x)
    calc
      ‖toEuclidean (X := X) (I := I) (Ks := Ks) x‖
          = (∑ i : Fin nI,
              ‖(toEuclidean (X := X) (I := I) (Ks := Ks) x).ofLp i‖ ^
                (2 : ENNReal).toReal) ^
              (1 / (2 : ENNReal).toReal) := hnorm
      _ = (∑ i : Fin nI,
            ‖(@getElem (Tensor X I) I X (fun _ _ => True) _ x (fromFin i) True.intro)‖ ^ 2) ^
              (1 / 2 : ℝ) := by
        simp [toEuclidean]
      _ = √(∑ i : I, ‖x[i]‖ ^ 2) := by
        rw [Real.sqrt_eq_rpow]
        congr 1
        exact Equiv.sum_comp (IndexType.equivFin (I := I)).symm (fun i : I => ‖x[i]‖ ^ 2)

theorem dist_getElem_le_dist [CommRing K] [NormedAddCommGroup X] [Module K X]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    [HasFlatRepr.LawfulAddGroupOps X Ks]
    (i : I) (xs ys : Tensor X I) : dist xs[i] ys[i] ≤ dist xs ys := by
  classical
  rw [dist_eq_norm', dist_eq_norm', norm_eq_sqrt_sum]
  simp only [getElem_sub]
  exact Real.le_sqrt_of_sq_le <|
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖ys[j] - xs[j]‖) (Finset.mem_univ i)

theorem continuous_getElem [CommRing K] [NormedAddCommGroup X] [Module K X]
    [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    [HasFlatRepr.LawfulAddGroupOps X Ks]
    (i : I) : Continuous fun xs : Tensor X I ↦ xs[i] := by
  rw [Metric.continuous_iff]
  intro xs ε hε
  refine ⟨ε, hε, ?_⟩
  intro ys hys
  exact lt_of_le_of_lt (dist_getElem_le_dist (i := i) ys xs) hys


end NumLean.Tensor
