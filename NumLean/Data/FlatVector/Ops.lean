import NumLean.Data.FlatVector.Basic
import NumLean.Interfaces.FlatRepr.Lawful
import NumLean.Interfaces.UntypedIndex
import NumLean.Algebra.Ops

namespace NumLean.FlatVector

variable {X : Type u} {I : Type v}
  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatVector X Ks nX] [IndexType I nI]

-- todo: move this
class BLASOps (Ks : Nat → Type u) (K : outParam (Type v)) where

  /-- Computes BLAS operation `axpy`:

  ```
  for i in 0...n do
    ys[yoff + i * yinc] += a * xs[xoff + i * xinc]
  ```

  We forbid `yinc = 0` such that implementation can execute the loop in parallel without any synchronization or atomics.
  -/
  axpy {xn yn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat) (ys : Ks yn) (yoff yinc : Nat)
    (hx : xoff + n * xinc ≤ xn) (hy : yoff + n * yinc ≤ yn ∧ yinc ≠ 0) -- valid index access and forbit accumulation! with yinc ≠ 0
    : Ks yn

  /-- Computes BLAS operation `scal`:

  ```
  for i in 0...n do
    xs[xoff + i * xinc] += a
  ```

  We forbid `xinc = 0` such that implementation can execute the loop in parallel without any synchronization or atomics.
  -/
  scal {xn : Nat} (n : Nat) (a : K) (xs : Ks xn) (xoff xinc : Nat)
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) : Ks xn


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

instance [One K] [BLASOps Ks K] : Add (FlatVector X I) := ⟨fun x y =>
  { data := BLASOps.axpy (nI * nX) (1 : K) y.data 0 1 x.data 0 1 (by simp) (by simp)}⟩

@[simp]
theorem getElem_add [Semiring K] [Add X] [FlatRepr.LawfulAdd X K] [BLASOps Ks K] -- [LawfulBLASOps Ks K]
    (xs ys : FlatVector X I) (i : I) :
    (xs + ys)[i] = xs[i] + ys[i] := by
  apply FlatRepr.ext K
  intro j h
  have h' : ∀ xs' : FlatVector X I, FlatRepr.getComp K (xs')[i] j h
            =
            VectorType.get xs'.data ((toFin i).1 * nX + j) sorry := sorry
  simp [FlatRepr.LawfulAdd.getComp_add]

  -- this is consequence of `axpy` definition of addition on `Ks n` !
  have h'' : VectorType.get (xs + ys).data ((toFin i).1 * nX + j) sorry
             =
             1 * VectorType.get ys.data ((toFin i).1 * nX + j) sorry
             +
             1 * VectorType.get xs.data ((toFin i).1 * nX + j) sorry := sorry

  simp [h'']
  ac_rfl


instance [One K] [Neg K] [BLASOps Ks K] : Sub (FlatVector X I) := ⟨fun x y =>
  { data := BLASOps.axpy (nI * nX) (-1 : K) y.data 0 1 x.data 0 1 (by simp) (by simp)}⟩

@[simp]
theorem getElem_sub [CommRing K] [Sub X] [FlatRepr.LawfulSub X K] [BLASOps Ks K]
    (xs ys : FlatVector X I) (i : I) :
    (xs - ys)[i] = xs[i] - ys[i] := by
  apply FlatRepr.ext K
  intro j h
  have h' : ∀ xs' : FlatVector X I, FlatRepr.getComp K (xs')[i] j h
            =
            VectorType.get xs'.data ((toFin i).1 * nX + j) sorry := sorry
  simp [FlatRepr.LawfulSub.getComp_sub]

  -- this is consequence of `axpy` definition of subition on `Ks n` !
  have h'' : VectorType.get (xs - ys).data ((toFin i).1 * nX + j) sorry
             =
             (-1) * VectorType.get ys.data ((toFin i).1 * nX + j) sorry
             +
             1 * VectorType.get xs.data ((toFin i).1 * nX + j) sorry := sorry

  simp [h'']
  ring


instance [BLASOps Ks K] : SMul K (FlatVector X I) := ⟨fun s x =>
  { data := BLASOps.scal (nI * nX) s x.data 0 1 (by simp)}⟩

@[simp]
theorem getElem_smul [Mul K] [SMul K X] [FlatRepr.LawfulSMul K X K] [BLASOps Ks K]
    (k : K) (xs : FlatVector X I) (i : I) :
    (k • xs)[i] = k • xs[i] := by
  apply FlatRepr.ext K
  intro j h
  have h' : ∀ xs' : FlatVector X I, FlatRepr.getComp K (xs')[i] j h
            =
            VectorType.get xs'.data ((toFin i).1 * nX + j) sorry := sorry
  simp [FlatRepr.LawfulSMul.getComp_smul]

  -- this is consequence of `axpy` definition of subition on `Ks n` !
  have h'' : VectorType.get (k • xs).data ((toFin i).1 * nX + j) sorry
             =
             k * VectorType.get xs.data ((toFin i).1 * nX + j) sorry := sorry

  simp [h'']


instance [Neg K] [One K] [BLASOps Ks K] : Neg (FlatVector X I) := ⟨fun x => (-1 : K) • x⟩

@[simp]
theorem getElem_neg [CommRing K] [AddCommGroup X] [Module K X] [FlatRepr.LawfulSMul K X K] [BLASOps Ks K]
    (xs : FlatVector X I) (i : I) :
    (- xs)[i] = - xs[i] := by
  rw[(by rfl : - xs = (-1 : K) • xs)]
  rw[getElem_smul]
  simp


-- todo: NatCast and IntCast should be part of some *Ops !!!

-- todo: define RingOps and assume [RingOps K]
instance [NatCast K] [IntCast K] [AddGroupOps K] [One K] [Mul K] [BLASOps Ks K] :
    AddGroupOps (FlatVector X I) where
  nsmul n x := (n : K) • x
  zsmul n x := (n : K) • x


-- instance : RNorm (FlatVector X I) K where
--   rnorm
