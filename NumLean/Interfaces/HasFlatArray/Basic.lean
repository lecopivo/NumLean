import NumLean.Interfaces.ArrayOps.Basic
import NumLean.Interfaces.FlatRepr.Basic

namespace NumLean

open FlatRepr in
/-- Type `X` can be stored in an array `Ks` whose scalar element type is `K`. -/
class HasFlatArray (X : Type u) (Ks : Type v) (nX : outParam Nat)
    {K : outParam (Type w)} [ArrayOps Ks K]
    extends FlatRepr X K nX where

  /-- Read `X` from `ks` starting at scalar offset `off`. -/
  get (ks : Ks) (off : Nat) (h : off + nX ≤ ArrayOps.size ks) : X
  getComp_get_eq_array_get (ks : Ks) (off i : Nat)
    (hoff : off + nX ≤ ArrayOps.size ks) (hi : i < nX) :
    getComp (get ks off hoff) i hi
    =
    ArrayOps.get ks (off + i) (by grind)

  -- /-- Read `X` from `ks` starting at `USize` scalar offset `off`. -/
  -- uget (ks : Ks) (off : USize) (h : off.toNat + nX ≤ ArrayOps.size ks) : X

  /-- Write `x` into `ks` starting at scalar offset `off`. -/
  set (ks : Ks) (off : Nat) (x : X) (h : off + nX ≤ ArrayOps.size ks) : Ks
  size_set (ks : Ks) (off : Nat) (x : X) (h : off + nX ≤ ArrayOps.size ks) :
    ArrayOps.size (set ks off x h) = ArrayOps.size ks
  array_get_set_eq (ks : Ks) (off i : Nat) (x : X) (hoff : off + nX ≤ ArrayOps.size ks)
    (hi : off ≤ i ∧ i < off + nX) :
    ArrayOps.get (set ks off x hoff) i (by grind)
    =
    getComp x (i - off) (by grind)
  array_get_set_ne (ks : Ks) (off i : Nat) (x : X) (hoff : off + nX ≤ ArrayOps.size ks)
    (hi : i < off ∨ off + nX ≤ i) (hi' : i < ArrayOps.size ks)  :
    ArrayOps.get (set ks off x hoff) i (by grind)
    =
    ArrayOps.get ks i hi'

  -- /-- Write `x` into `ks` starting at `USize` scalar offset `off`. -/
  -- uset (ks : Ks) (off : USize) (x : X) (h : off.toNat + nX ≤ ArrayOps.size ks) : Ks

  /-- Append `x` to the end of `ks` as one contiguous `X` block. -/
  push (ks : Ks) (x : X) : Ks
  size_push (ks : Ks) (x : X) : ArrayOps.size (push ks x) = ArrayOps.size ks + nX
  array_get_push_lt (ks : Ks) (x : X) (i : Nat) (hi : i < ArrayOps.size ks) :
    ArrayOps.get (push ks x) i (by rw [size_push]; grind) = ArrayOps.get ks i hi
  array_get_push_eq (ks : Ks) (x : X) (i : Nat) (hi : i < nX) :
    ArrayOps.get (push ks x) (ArrayOps.size ks + i) (by rw [size_push]; grind) =
      getComp x i hi

  -- for vectors, matrices, tensors this should be no-op
  toArray : X → Ks
  size_toArray (x : X) : ArrayOps.size (toArray x) = nX
  get_toArray_eq_getComp (x : X) (i : Nat) (h : i < nX) :
    ArrayOps.get (toArray x) i (by rw[size_toArray]; apply h) = getComp x i h

/-- The default flat array type for `X`. -/
class HasDefaultFlatArray (X : Type u) (Ks : outParam (Type v)) (nX : outParam Nat)
    {K : outParam (Type w)} [ArrayOps Ks K]
    extends HasFlatArray X Ks nX

namespace HasFlatArray

variable {X Ks K nX} [ArrayOps Ks K] [HasFlatArray X Ks nX]

attribute [simp] size_set

theorem get_set_eq (ks : Ks) (off : Nat) (x : X) (hoff : off + nX ≤ ArrayOps.size ks) :
    get (set ks off x hoff) off (by simp; grind)
    =
    x := by
  apply FlatRepr.ext K; intro i hi
  rw[getComp_get_eq_array_get, array_get_set_eq]
  all_goals grind

theorem get_set_ne (ks : Ks) (off off' : Nat) (x : X) (hoff : off + nX ≤ ArrayOps.size ks)
    (hoff' : off' + nX ≤ off ∨ off + nX ≤ off') (hoff'' : off' + nX ≤ ArrayOps.size ks) :
    get (X:=X) (set ks off x hoff) off' (by simp; grind)
    =
    get ks off' hoff'' := by
  apply FlatRepr.ext K; intro i hi
  simp only [getComp_get_eq_array_get]
  rw[array_get_set_ne]
  all_goals grind

theorem get_push_eq (ks : Ks) (x : X) :
    get (X := X) (push ks x) (ArrayOps.size ks) (by rw [size_push]; grind) = x := by
  apply FlatRepr.ext K
  intro i hi
  rw [getComp_get_eq_array_get, array_get_push_eq]

theorem get_push_lt (ks : Ks) (off : Nat) (x : X)
    (hoff : off + nX ≤ ArrayOps.size ks) :
    get (X := X) (push ks x) off (by
      rw [size_push]
      exact Nat.le_trans hoff (Nat.le_add_right _ _)) = get (X := X) ks off hoff := by
  apply FlatRepr.ext K
  intro i hi
  rw [getComp_get_eq_array_get, getComp_get_eq_array_get]
  have hlt : off + i < ArrayOps.size ks := by
    have := hoff
    grind
  rw [array_get_push_lt (ks := ks) (x := x) (i := off + i) hlt]

end HasFlatArray

end NumLean
