import NumLean.Algebra.Instances
import NumLean.Data.FlatVector.Algebra.Group.Ops
import NumLean.Data.Vector.RingArrayOps.Axpy
import NumLean.Data.Vector.RingArrayOps.Scal
import NumLean.Interfaces.Module.Lawful
import NumLean.Interfaces.HasFlatRepr.Lawful
import NumLean.Interfaces.UntypedIndex
import Mathlib.Analysis.Normed.Lp.PiLp

namespace NumLean.FlatVector

variable {X : Type u} {I : Type v}
  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX] [IndexType I nI]

@[simp]
theorem getElem_zero [Zero K] [Zero X] [HasFlatRepr.LawfulZero X Ks] (i : I) :
    (0 : FlatVector X I)[i] = 0 := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j h
  conv_lhs => simp only [getComp_getElem_eq_get]; simp [Zero.zero, OfNat.ofNat]
  simp [HasFlatRepr.LawfulZero.getComp_zero]
  rfl

@[simp]
theorem getElem_one [One K] [One X] [HasFlatRepr.LawfulOne X Ks] (i : I) :
    (1 : FlatVector X I)[i] = 1 := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j h
  conv_lhs => simp only [getComp_getElem_eq_get]; simp [One.one, OfNat.ofNat]
  simp [HasFlatRepr.LawfulOne.getComp_one]
  rfl

@[simp]
theorem getElem_add [Ring K] [Add X] [HasFlatRepr.LawfulAdd X Ks]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    (xs ys : FlatVector X I) (i : I) :
    (xs + ys)[i] = xs[i] + ys[i] := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j h
  have hidx : (toFin i).1 * nX + j < nI * nX := by
    have hi := (toFin i).2
    tbounds
  have hget := Vector.axpy_full_get (Ks := Ks) (K := K) (a := (1 : K))
    (xs := ys.data) (ys := xs.data) ((toFin i).1 * nX + j) hidx
  rw [getComp_getElem_eq_get]
  rw [HasFlatRepr.LawfulAdd.getComp_add]
  rw [getComp_getElem_eq_get xs, getComp_getElem_eq_get ys]
  simpa [one_mul] using hget

@[simp]
theorem getElem_sub [CommRing K] [Sub X] [HasFlatRepr.LawfulSub X Ks]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    (xs ys : FlatVector X I) (i : I) :
    (xs - ys)[i] = xs[i] - ys[i] := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j h
  have hidx : (toFin i).1 * nX + j < nI * nX := by
    have hi := (toFin i).2
    tbounds
  have hget := Vector.axpy_full_get (Ks := Ks) (K := K) (a := (-1 : K))
    (xs := ys.data) (ys := xs.data) ((toFin i).1 * nX + j) hidx
  rw [getComp_getElem_eq_get]
  rw [HasFlatRepr.LawfulSub.getComp_sub]
  rw [getComp_getElem_eq_get xs, getComp_getElem_eq_get ys]
  change VectorType.get (RingArrayOps.axpy (nI * nX) (-1 : K) ys.data 0 1 xs.data 0 1
      (by simp) (by simp)) ((toFin i).1 * nX + j) _ = _
  rw [hget]
  ring

@[simp]
theorem getElem_smul [Ring K] [SMul K X] [HasFlatRepr.LawfulSMul K X Ks]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    (k : K) (xs : FlatVector X I) (i : I) :
    (k • xs)[i] = k • xs[i] := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j h
  have hidx : (toFin i).1 * nX + j < nI * nX := by
    have hi := (toFin i).2
    tbounds
  have hget := Vector.scal_full_get (Ks := Ks) (K := K) (a := k)
    (xs := xs.data) ((toFin i).1 * nX + j) hidx
  rw [getComp_getElem_eq_get]
  rw [HasFlatRepr.LawfulSMul.getComp_smul]
  rw [getComp_getElem_eq_get xs]
  simpa using hget

@[simp]
theorem getElem_neg [CommRing K] [AddCommGroup X] [Module K X]
    [HasFlatRepr.LawfulSMul K X Ks]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    (xs : FlatVector X I) (i : I) :
    (- xs)[i] = - xs[i] := by
  rw [(by rfl : -xs = (-1 : K) • xs)]
  rw [getElem_smul]
  simp

instance instLawfulAddMonoidOps [Ring K] [AddCommMonoid X] [Module K X]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    [HasFlatRepr.LawfulAddMonoidOps (nX := nX) K X Ks] :
    LawfulAddMonoidOps (FlatVector X I) where
  add_assoc := by intros; ext; simp [add_assoc]
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
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

instance instLawfulAddGroupOps [CommRing K] [AddCommGroup X] [Module K X]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) K X Ks] :
    LawfulAddGroupOps (FlatVector X I) where
  toLawfulAddMonoidOps := instLawfulAddMonoidOps
  sub_eq_add_neg := by intros; ext; simp [sub_eq_add_neg]
  zsmul_zero := by
    intro a
    ext i
    simp [_root_.NumLean.Interfaces.Algebra.AddGroupOps.zsmul]
  zsmul_succ := by
    intro n a
    ext i
    simp [_root_.NumLean.Interfaces.Algebra.AddGroupOps.zsmul, Nat.cast_add, add_smul]
  zsmul_neg := by
    intro n a
    ext i
    simp [_root_.NumLean.Interfaces.Algebra.AddGroupOps.zsmul]
    rw [← neg_smul]
    congr 1
    ring
  neg_add_cancel := by intros; ext; simp

instance [Ring K] [AddCommMonoid X] [Module K X]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    [HasFlatRepr.LawfulAddMonoidOps (nX := nX) K X Ks] :
    AddCommMonoid (FlatVector X I) where
  add_assoc := by intros; ext; simp [add_assoc]
  add_comm := by intros; ext; simp [add_comm]
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
  nsmul n x := (n : K) • x
  nsmul_zero := by intros; ext; simp
  nsmul_succ := by intros; ext; simp [add_smul]

instance instAddCommGroup [CommRing K] [AddCommGroup X] [Module K X]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) K X Ks] :
    AddCommGroup (FlatVector X I) where
  sub_eq_add_neg := by intros; ext; simp [sub_eq_add_neg]
  neg_add_cancel := by intros; ext; simp
  zsmul n x := (n : K) • x
  zsmul_neg' := by intros; ext; simp [add_smul]
  zsmul_zero' := by intros; ext; simp
  zsmul_succ' := by intros; ext; simp [add_smul]

instance instLawfulModuleOps [Ring K] [AddCommMonoid X] [Module K X]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    [HasFlatRepr.LawfulAddMonoidOps (nX := nX) K X Ks] :
    Interfaces.Module.LawfulModuleOps K (FlatVector X I) where
  one_smul := by
    intro x
    ext i
    rw [getElem_smul]
    exact one_smul K x[i]
  mul_smul := by
    intro r s x
    ext i
    rw [getElem_smul, getElem_smul, getElem_smul]
    exact mul_smul r s x[i]
  smul_zero := by
    intro r
    ext i
    rw [getElem_smul, getElem_zero]
    exact smul_zero r
  smul_add := by
    intro r x y
    ext i
    rw [getElem_smul, getElem_add]
    rw [getElem_add, getElem_smul, getElem_smul]
    exact smul_add r x[i] y[i]
  add_smul := by
    intro r s x
    ext i
    rw [getElem_smul]
    rw [getElem_add, getElem_smul, getElem_smul]
    exact add_smul r s x[i]
  zero_smul := by
    intro x
    ext i
    rw [getElem_smul, getElem_zero]
    exact zero_smul K x[i]

instance [Ring K] [AddCommMonoid X] [Module K X]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    [HasFlatRepr.LawfulAddMonoidOps (nX := nX) K X Ks] :
    Module K (FlatVector X I) where
  mul_smul := by intros; ext; simp [mul_smul]
  one_smul := by intros; ext; simp
  smul_zero := by intros; ext; simp
  smul_add := by intros; ext; simp
  add_smul := by intros; ext; simp [add_smul]
  zero_smul := by intros; ext; simp

noncomputable
instance [CommRing K] [NormedAddCommGroup X] [Module K X]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) K X Ks] :
    NormedAddCommGroup (FlatVector X I) where
  norm xs := Real.sqrt (∑ i : I, ‖xs[i]‖^2)
  dist_self := by intros; simp
  dist_comm := by
    intros
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
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) K X Ks]

theorem norm_eq_sqrt_sum (xs : FlatVector X I) : ‖xs‖ = Real.sqrt (∑ i : I, ‖xs[i]‖^2) := by
  rfl

end Normed

instance [NormedField K] [NormedAddCommGroup X] [NormedSpace K X]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) K X Ks] :
    NormedSpace K (FlatVector X I) where
  norm_smul_le := by
    intros
    rw [norm_eq_sqrt_sum]
    simp [norm_smul, mul_pow, ← Finset.mul_sum]
    rw [← norm_eq_sqrt_sum]

theorem dist_getElem_le_dist [CommRing K] [NormedAddCommGroup X] [Module K X]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) K X Ks]
    (i : I) (xs ys : FlatVector X I) : dist xs[i] ys[i] ≤ dist xs ys := by
  classical
  rw [dist_eq_norm', dist_eq_norm', norm_eq_sqrt_sum]
  simp only [getElem_sub]
  exact Real.le_sqrt_of_sq_le <|
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖ys[j] - xs[j]‖) (Finset.mem_univ i)

theorem continuous_getElem [CommRing K] [NormedAddCommGroup X] [Module K X]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) K X Ks]
    (i : I) : Continuous fun xs : FlatVector X I ↦ xs[i] := by
  rw [Metric.continuous_iff]
  intro xs ε hε
  refine ⟨ε, hε, ?_⟩
  intro ys hys
  exact lt_of_le_of_lt (dist_getElem_le_dist (i := i) ys xs) hys

end NumLean.FlatVector
