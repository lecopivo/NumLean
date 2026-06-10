import NumLean.Interfaces.ArrayType.Basic

namespace NumLean

open Function

/-- Type `X` has a flat representation as a fixed-length vector of `K`. -/
class FlatRepr (X : Type u) (K : Type v) (n : outParam Nat) where
  /-- Specification-level conversion to a fixed-size scalar vector. -/
  toVector (K) : X → _root_.Vector K n
  /-- Specification-level conversion from a fixed-size scalar vector. -/
  fromVector (X) : _root_.Vector K n → X

  left_inv : LeftInverse fromVector toVector
  right_inv : RightInverse fromVector toVector

  /-- Scalar coordinate projection of an `X`. -/
  getComp (K) (x : X) (i : Nat) (h : i < n) : K
  getComp_spec (x : X) (i : Nat) (h : i < n) :
    getComp x i h = (toVector x)[i]

  -- /-- `USize` scalar coordinate projection of an `X`. -/
  -- ugetComp (x : X) (i : USize) (h : i.toNat < n) : K
  -- ugetComp_spec (x : X) (i : USize) (h : i.toNat < n) :
  --   ugetComp x i h = (toVector x)[i.toNat]

  setComp (x : X) (i : Nat) (xi : K) (h : i < n) : X
  setComp_spec (x : X) (i : Nat) (xi : K) (h : i < n) :
    setComp x i xi h = fromVector ((toVector x).set i xi h)

  -- usetComp (x : X) (i : USize) (xi : K) (h : i.toNat < n) : X
  -- usetComp_spec (x : X) (i : USize) (xi : K) (h : i.toNat < n) :
  --   usetComp x i xi h = fromVector ((toVector x).set i.toNat xi h)

/-- Default flat representation of type `X`. -/
class DefaultFlatRepr (X : Type u) (K : outParam (Type v)) (n : outParam Nat)
    extends FlatRepr X K n

namespace FlatRepr

variable {X : Type u} {K : Type v} {nX : Nat} [FlatRepr X K n]

@[simp]
theorem fromVector_toVector (x : X) :
    fromVector (X:=X) (toVector (K:=K) x) = x :=
  FlatRepr.left_inv x

@[simp]
theorem toVector_fromVector (x : _root_.Vector K n) :
    toVector (K:=K) (fromVector (X:=X) x) = x :=
  FlatRepr.right_inv x

@[simp]
theorem getComp_setComp_eq (x : X) (i : Nat) (xi : K) (h : i < n) :
  getComp (K:=K) (setComp x i xi h) i h = xi := by
  rw [FlatRepr.getComp_spec, FlatRepr.setComp_spec, FlatRepr.toVector_fromVector]
  exact Vector.getElem_set_self h

@[simp]
theorem getComp_setComp_neq (x : X) (i j : Nat) (xi : K) (hi : i < n) (hj : j < n) (h : i ≠ j) :
  getComp (K:=K) (setComp x i xi hi) j hj = getComp (K:=K) x j hj := by
  rw [FlatRepr.getComp_spec, FlatRepr.setComp_spec, FlatRepr.toVector_fromVector,
    FlatRepr.getComp_spec]
  rw [Vector.getElem_set hi hj]
  simp [h]

end FlatRepr

section BasicInstances

instance {X} : FlatRepr X X 1 where
  toVector x := #v[x]
  fromVector x := x[0]
  left_inv := by intro _; simp
  right_inv := by intro _; simp; ext <;> grind
  getComp x _ _ := x
  getComp_spec := by intros; simp
  -- ugetComp x _ _ := x
  -- ugetComp_spec := by intros; simp
  setComp _ _ x _ := x
  setComp_spec := by intros; simp; grind
  -- usetComp _ _ x _ := x
  -- usetComp_spec := by intros; simp; grind

end BasicInstances

end NumLean
