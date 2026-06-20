import NumLean.Interfaces.VectorType.Basic
import NumLean.Interfaces.FlatRepr.Basic

namespace NumLean

open FlatRepr in
/-- Type `X` can be stored in a vector `Ks n` whose scalar element type is `K`. -/
class HasFlatVector (X : Type u) (Ks : Nat → Type v) (nX : outParam Nat)
    {K : outParam (Type w)} [VectorType Ks K]
    extends FlatRepr X K nX where

  /-- Read `X` from `ks` starting at scalar offset `off`. -/
  get {n : Nat} (ks : Ks n) (off : Nat) (h : off + nX ≤ n) : X
  getComp_get_eq_vector_get {n : Nat} (ks : Ks n) (off i : Nat)
    (hoff : off + nX ≤ n) (hi : i < nX) :
    getComp (get ks off hoff) i hi
    =
    VectorType.get ks (off + i) (by grind)

  -- /-- Read `X` from `ks` starting at `USize` scalar offset `off`. -/
  -- uget {n : Nat} (ks : Ks n) (off : USize) (h : off.toNat + nX ≤ n) : X

  /-- Write `x` into `ks` starting at scalar offset `off`. -/
  set {n : Nat} (ks : Ks n) (off : Nat) (x : X) (h : off + nX ≤ n) : Ks n
  vector_get_set_eq {n : Nat} (ks : Ks n) (off i : Nat) (x : X) (hoff : off + nX ≤ n)
    (hi : off ≤ i ∧ i < off + nX) :
    VectorType.get (set ks off x hoff) i (by grind)
    =
    getComp x (i - off) (by grind)
  vector_get_set_ne {n : Nat} (ks : Ks n) (off i : Nat) (x : X) (hoff : off + nX ≤ n)
    (hi : i < off ∨ off + nX ≤ i) (hi' : i < n)  :
    VectorType.get (set ks off x hoff) i (by grind)
    =
    VectorType.get ks i hi'

  -- /-- Write `x` into `ks` starting at `USize` scalar offset `off`. -/
  -- uset {n : Nat} (ks : Ks n) (off : USize) (x : X) (h : off.toNat + nX ≤ n) : Ks n

  /-- Append `x` to the end of `ks` as one contiguous `X` block. -/
  push {n : Nat} (ks : Ks n) (x : X) : Ks (n + nX)
  vector_get_push_lt {n : Nat} (ks : Ks n) (x : X) (i : Nat) (hi : i < n) :
    VectorType.get (push ks x) i (by grind) = VectorType.get ks i hi
  vector_get_push_eq {n : Nat} (ks : Ks n) (x : X) (i : Nat) (hi : i < nX) :
    VectorType.get (push ks x) (n + i) (by grind) =
      getComp x i hi

  -- for vectors, matrices, tensors this should be no-op
  toFlatVector : X → Ks nX
  get_toFlatVector_eq_getComp (x : X) (i : Nat) (h : i < nX) :
    VectorType.get (toFlatVector x) i h = getComp x i h

/-- The default flat vector type for `X`. -/
class HasDefaultFlatVector (X : Type u) (Ks : outParam (Nat → Type v)) (nX : outParam Nat)
    {K : outParam (Type w)} [VectorType Ks K]
    extends HasFlatVector X Ks nX

namespace HasFlatVector

variable {X Ks K nX} [VectorType Ks K] [HasFlatVector X Ks nX]

theorem get_set_eq {n : Nat} (ks : Ks n) (off : Nat) (x : X) (hoff : off + nX ≤ n) :
    get (set ks off x hoff) off (by grind)
    =
    x := by
  apply FlatRepr.ext K; intro i hi
  rw[getComp_get_eq_vector_get, vector_get_set_eq]
  all_goals grind

theorem get_set_ne {n : Nat} (ks : Ks n) (off off' : Nat) (x : X) (hoff : off + nX ≤ n)
    (hoff' : off' + nX ≤ off ∨ off + nX ≤ off') (hoff'' : off' + nX ≤ n) :
    get (X:=X) (set ks off x hoff) off' (by grind)
    =
    get ks off' hoff'' := by
  apply FlatRepr.ext K; intro i hi
  simp only [getComp_get_eq_vector_get]
  rw[vector_get_set_ne]
  all_goals grind

theorem get_push_eq {n : Nat} (ks : Ks n) (x : X) :
    get (X := X) (push ks x) n (by grind) = x := by
  apply FlatRepr.ext K
  intro i hi
  rw [getComp_get_eq_vector_get, vector_get_push_eq]

theorem get_push_lt {n : Nat} (ks : Ks n) (off : Nat) (x : X)
    (hoff : off + nX ≤ n) :
    get (X := X) (push ks x) off (by grind) = get (X := X) ks off hoff := by
  apply FlatRepr.ext K
  intro i hi
  rw [getComp_get_eq_vector_get, getComp_get_eq_vector_get]
  have hlt : off + i < n := by
    have := hoff
    grind
  rw [vector_get_push_lt (ks := ks) (x := x) (i := off + i) hlt]

end HasFlatVector

end NumLean
