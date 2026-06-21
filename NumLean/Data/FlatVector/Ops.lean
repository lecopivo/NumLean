import NumLean.Data.FlatVector.Basic
import NumLean.Interfaces.FlatRepr.Lawful
import NumLean.Interfaces.UntypedIndex

namespace NumLean.FlatVector

variable {X : Type u} {I : Type v}
  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatVector X Ks nX] [IndexType I nI]


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


instance [Zero K] : Zero (FlatVector X I) := sorry -- ⟨{ data := HasFlatVector.replicate (nI * nX) 0 }⟩

-- todo: !!! THIS IS NOT THE simp-normal FORM !!!
-- we need some general notion of index types like: (Fin n, Nat, fun size i => i < size)
theorem getElem_zero [Zero K] [Zero X] [FlatRepr.LawfulZero X K] (i : I) :
    (0 : FlatVector X I)[i] = 0 := by
  apply FlatRepr.ext K
  intro j h
  -- this hsould be a simp theorem!
  have h' : FlatRepr.getComp K (0 : FlatVector X I)[i] j h
            =
            VectorType.get (0 : FlatVector X I).data ((toFin i).1 * nX + j) sorry := sorry
  simp [FlatRepr.LawfulZero.getComp_zero]
  simp [h'] -- make `FlatRepr.LawfulZero.getComp_zero` make this simp theorem
  sorry -- this is theorem about replicate which should be part of HasFlatVector!


instance [One K] : One (FlatVector X I) := sorry -- ⟨{ data := HasFlatVector.replicate (nI * nX) 1 }⟩

theorem getElem_one [One K] [One X] [FlatRepr.LawfulOne X K] (i : I) :
    (1 : FlatVector X I)[i] = 1 := by
  sorry


instance [One K] [BLASOps Ks K] : Add (FlatVector X I) := ⟨fun x y =>
  { data := BLASOps.axpy (nI * nX) (1 : K) y.data 0 1 x.data 0 1 (by simp) (by simp)}⟩

theorem getElem_add [Semiring K] [Add X] [FlatRepr.LawfulAdd X K] [BLASOps Ks K]
    (xs ys : FlatVector X I) (i : I) :
    (xs + ys)[i] = xs[i] + ys[i] := by
  apply FlatRepr.ext K
  intro j h
  have h' : ∀ xs' : FlatVector X I, FlatRepr.getComp K (xs')[i] j h
            =
            VectorType.get xs'.data ((toFin i).1 * nX + j) sorry := sorry
  simp [FlatRepr.LawfulAdd.getComp_add]
  simp [h']

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

theorem getElem_sub [CommRing K] [Sub X] [FlatRepr.LawfulSub X K] [BLASOps Ks K]
    (xs ys : FlatVector X I) (i : I) :
    (xs + ys)[i] = xs[i] - ys[i] := by
  apply FlatRepr.ext K
  intro j h
  have h' : ∀ xs' : FlatVector X I, FlatRepr.getComp K (xs')[i] j h
            =
            VectorType.get xs'.data ((toFin i).1 * nX + j) sorry := sorry
  simp [FlatRepr.LawfulSub.getComp_sub]
  simp [h']

  -- this is consequence of `axpy` definition of subition on `Ks n` !
  have h'' : VectorType.get (xs + ys).data ((toFin i).1 * nX + j) sorry
             =
             (-1) * VectorType.get ys.data ((toFin i).1 * nX + j) sorry
             +
             1 * VectorType.get xs.data ((toFin i).1 * nX + j) sorry := sorry

  simp [h'']
  ring


instance [BLASOps Ks K] : SMul K (FlatVector X I) := ⟨fun s x =>
  { data := BLASOps.scal (nI * nX) s x.data 0 1 (by simp)}⟩

theorem getElem_smul [Mul K] [SMul K X] [FlatRepr.LawfulSMul K X K] [BLASOps Ks K]
    (k : K) (xs : FlatVector X I) (i : I) :
    (k • xs)[i] = k • xs[i] := by
  apply FlatRepr.ext K
  intro j h
  have h' : ∀ xs' : FlatVector X I, FlatRepr.getComp K (xs')[i] j h
            =
            VectorType.get xs'.data ((toFin i).1 * nX + j) sorry := sorry
  simp [FlatRepr.LawfulSMul.getComp_smul]
  simp [h']

  -- this is consequence of `axpy` definition of subition on `Ks n` !
  have h'' : VectorType.get (k • xs).data ((toFin i).1 * nX + j) sorry
             =
             k * VectorType.get xs.data ((toFin i).1 * nX + j) sorry := sorry

  simp [h'']


instance [Neg K] [One K] [BLASOps Ks K] : Neg (FlatVector X I) := ⟨fun x => (-1 : K) • x⟩

theorem getElem_neg [CommRing K] [AddCommGroup X] [Module K X] [FlatRepr.LawfulSMul K X K] [BLASOps Ks K]
    (xs : FlatVector X I) (i : I) :
    (- xs)[i] = - xs[i] := by
  rw[(by rfl : - xs = (-1 : K) • xs)]
  rw[getElem_smul]
  simp
