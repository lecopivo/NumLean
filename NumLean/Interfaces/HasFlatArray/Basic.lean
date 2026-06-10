import NumLean.Interfaces.ArrayType.Basic
import NumLean.Interfaces.FlatRepr.Basic

namespace NumLean

open FlatRepr in
/-- Type `X` can be stored in an array `Ks` whose scalar element type is `K`. -/
class HasFlatArray (X : Type u) (Ks : Type v) (nX : outParam Nat)
    {K : outParam (Type w)} [ArrayType Ks K]
    extends FlatRepr X K nX where

  /-- Read `X` from `ks` starting at scalar offset `off`. -/
  get (ks : Ks) (off : Nat) (h : off + nX ≤ ArrayType.size ks) : X
  getComp_get_eq_array_get (ks : Ks) (off i : Nat)
    (hoff : off + nX ≤ ArrayType.size ks) (hi : i < nX) :
    getComp (get ks off hoff) i hi
    =
    ArrayType.get ks (off + i) (by grind)

  -- /-- Read `X` from `ks` starting at `USize` scalar offset `off`. -/
  -- uget (ks : Ks) (off : USize) (h : off.toNat + nX ≤ ArrayType.size ks) : X

  /-- Write `x` into `ks` starting at scalar offset `off`. -/
  set (ks : Ks) (off : Nat) (x : X) (h : off + nX ≤ ArrayType.size ks) : Ks
  size_set (ks : Ks) (off : Nat) (x : X) (h : off + nX ≤ ArrayType.size ks) :
    ArrayType.size (set ks off x h) = ArrayType.size ks
  array_get_set_eq (ks : Ks) (off i : Nat) (x : X) (hoff : off + nX ≤ ArrayType.size ks)
    (hi : off ≤ i ∧ i < off + nX) :
    ArrayType.get (set ks off x hoff) i (by grind)
    =
    getComp x (i - off) (by grind)
  array_get_set_ne (ks : Ks) (off i : Nat) (x : X) (hoff : off + nX ≤ ArrayType.size ks)
    (hi : i < off ∨ off + nX ≤ i) (hi' : i < ArrayType.size ks)  :
    ArrayType.get (set ks off x hoff) i (by grind)
    =
    ArrayType.get ks i hi'
      -- (ArrayType.fromArray <| _root_.Vector.toArray <|
      --   Fin.foldl (n:=nX) (init := _root_.Vector.mk (ArrayType.toArray ks) rfl)
      --     (fun acc i => acc.set (off + i.1) (FlatRepr.toVector K x)[i]
      --       (by simp [← ArrayType.size_spec]; omega)))

  -- /-- Write `x` into `ks` starting at `USize` scalar offset `off`. -/
  -- uset (ks : Ks) (off : USize) (x : X) (h : off.toNat + nX ≤ ArrayType.size ks) : Ks

/-- The default flat array type for `X`. -/
class HasDefaultFlatArray (X : Type u) (Ks : outParam (Type v)) (nX : outParam Nat)
    {K : outParam (Type w)} [ArrayType Ks K]
    extends HasFlatArray X Ks nX

namespace HasFlatArray

variable {X Ks K nX} [ArrayType Ks K] [HasFlatArray X Ks nX]

attribute [simp] size_set

theorem get_set_eq (ks : Ks) (off : Nat) (x : X) (hoff : off + nX ≤ ArrayType.size ks) :
    get (set ks off x hoff) off (by simp; grind)
    =
    x := by
  apply FlatRepr.ext K; intro i hi
  rw[getComp_get_eq_array_get, array_get_set_eq]
  all_goals grind

theorem get_set_ne (ks : Ks) (off off' : Nat) (x : X) (hoff : off + nX ≤ ArrayType.size ks)
    (hoff' : off' + nX ≤ off ∨ off + nX ≤ off') (hoff'' : off' + nX ≤ ArrayType.size ks) :
    get (X:=X) (set ks off x hoff) off' (by simp; grind)
    =
    get ks off' hoff'' := by
  apply FlatRepr.ext K; intro i hi
  simp only [getComp_get_eq_array_get]
  rw[array_get_set_ne]
  all_goals grind

end HasFlatArray

end NumLean
