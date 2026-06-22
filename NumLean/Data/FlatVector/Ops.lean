import NumLean.Data.FlatVector.Basic
import NumLean.Data.Vector.RingArrayOps.Axpy
import NumLean.Data.Vector.RingArrayOps.Scal
import NumLean.Interfaces.Algebra.RingArrayOps
import NumLean.Interfaces.FlatRepr.Lawful
import NumLean.Interfaces.UntypedIndex
import NumLean.Algebra.Ops

namespace NumLean.FlatVector

variable {X : Type u} {I : Type v}
  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatVector X Ks nX] [IndexType I nI]

instance [Zero K] : Zero (FlatVector X I) := ⟨{ data := VectorType.replicate (nI * nX) 0 }⟩

@[simp]
theorem getElem_zero [Zero K] [Zero X] [FlatRepr.LawfulZero X K] (i : I) :
    (0 : FlatVector X I)[i] = 0 := by
  apply FlatRepr.ext K
  intro j h
  conv_lhs => simp only [getComp_getElem_eq_get]; simp [Zero.zero, OfNat.ofNat]
  simp [FlatRepr.LawfulZero.getComp_zero]
  rfl

instance [One K] : One (FlatVector X I) := ⟨{ data := VectorType.replicate (nI * nX) 1 }⟩

@[simp]
theorem getElem_one [One K] [One X] [FlatRepr.LawfulOne X K] (i : I) :
    (1 : FlatVector X I)[i] = 1 := by
  apply FlatRepr.ext K
  intro j h
  conv_lhs => simp only [getComp_getElem_eq_get]; simp [One.one, OfNat.ofNat]
  simp [FlatRepr.LawfulOne.getComp_one]
  rfl

instance [One K] [RingArrayOps Ks] : Add (FlatVector X I) := ⟨fun x y =>
  { data := RingArrayOps.axpy (nI * nX) (1 : K) y.data 0 1 x.data 0 1 (by simp) (by simp)}⟩

@[simp]
theorem getElem_add [Ring K] [Add X] [FlatRepr.LawfulAdd X K]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    (xs ys : FlatVector X I) (i : I) :
    (xs + ys)[i] = xs[i] + ys[i] := by
  apply FlatRepr.ext K
  intro j h
  have hidx : (toFin i).1 * nX + j < nI * nX := by
    have hi := (toFin i).2
    tbounds
  have hget := Vector.axpy_full_get (Ks := Ks) (K := K) (a := (1 : K))
    (xs := ys.data) (ys := xs.data) ((toFin i).1 * nX + j) hidx
  rw [getComp_getElem_eq_get]
  rw [FlatRepr.LawfulAdd.getComp_add]
  rw [getComp_getElem_eq_get xs, getComp_getElem_eq_get ys]
  simpa [one_mul] using hget


instance [Neg K] [One K] [RingArrayOps Ks] : Sub (FlatVector X I) := ⟨fun x y =>
  { data := RingArrayOps.axpy (nI * nX) (-1 : K) y.data 0 1 x.data 0 1 (by simp) (by simp)}⟩

@[simp]
theorem getElem_sub [CommRing K] [Sub X] [FlatRepr.LawfulSub X K]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    (xs ys : FlatVector X I) (i : I) :
    (xs - ys)[i] = xs[i] - ys[i] := by
  apply FlatRepr.ext K
  intro j h
  have hidx : (toFin i).1 * nX + j < nI * nX := by
    have hi := (toFin i).2
    tbounds
  have hget := Vector.axpy_full_get (Ks := Ks) (K := K) (a := (-1 : K))
    (xs := ys.data) (ys := xs.data) ((toFin i).1 * nX + j) hidx
  rw [getComp_getElem_eq_get]
  rw [FlatRepr.LawfulSub.getComp_sub]
  rw [getComp_getElem_eq_get xs, getComp_getElem_eq_get ys]
  change VectorType.get (RingArrayOps.axpy (nI * nX) (-1 : K) ys.data 0 1 xs.data 0 1
      (by simp) (by simp)) ((toFin i).1 * nX + j) _ = _
  rw [hget]
  ring


instance [RingArrayOps Ks] : SMul K (FlatVector X I) := ⟨fun s x =>
  { data := RingArrayOps.scal (nI * nX) s x.data 0 1 (by simp)}⟩

@[simp]
theorem getElem_smul [Ring K] [SMul K X] [FlatRepr.LawfulSMul K X K]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    (k : K) (xs : FlatVector X I) (i : I) :
    (k • xs)[i] = k • xs[i] := by
  apply FlatRepr.ext K
  intro j h
  have hidx : (toFin i).1 * nX + j < nI * nX := by
    have hi := (toFin i).2
    tbounds
  have hget := Vector.scal_full_get (Ks := Ks) (K := K) (a := k)
    (xs := xs.data) ((toFin i).1 * nX + j) hidx
  rw [getComp_getElem_eq_get]
  rw [FlatRepr.LawfulSMul.getComp_smul]
  rw [getComp_getElem_eq_get xs]
  simpa using hget


instance [Neg K] [One K] [RingArrayOps Ks] : Neg (FlatVector X I) := ⟨fun x => (-1 : K) • x⟩

@[simp]
theorem getElem_neg [CommRing K] [AddCommGroup X] [Module K X] [FlatRepr.LawfulSMul K X K]
    [RingArrayOps Ks] [LawfulRingArrayOps Ks]
    (xs : FlatVector X I) (i : I) :
    (- xs)[i] = - xs[i] := by
  rw[(by rfl : - xs = (-1 : K) • xs)]
  rw[getElem_smul]
  simp


-- todo: NatCast and IntCast should be part of some *Ops !!!

-- todo: define RingOps and assume [RingOps K]
instance [NatCast K] [IntCast K] [AddGroupOps K] [One K] [RingArrayOps Ks] :
    AddGroupOps (FlatVector X I) where
  nsmul n x := (n : K) • x
  zsmul n x := (n : K) • x


-- instance : RNorm (FlatVector X I) K where
--   rnorm
