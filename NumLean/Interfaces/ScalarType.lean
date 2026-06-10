import NumLean.Interfaces.IndexType
import NumLean.Interfaces.ScalarArray.Basic

namespace NumLean

open Function

/-- `X` is represented by a fixed number of scalars in `Ks`. -/
class VectorType (X : Type u) (nX : outParam Nat) (Ks : outParam (Type v)) {K : outParam (Type w)}
    [ArrayType Ks K] where

  toVector : X → _root_.Vector K nX
  fromVector : _root_.Vector K nX → X
  left_inv : LeftInverse fromVector toVector
  right_inv : RightInverse fromVector toVector

  getComp (x : X) (i : Nat) (h : i < nX) : K
  getComp_spec (x : X) (i : Nat) (h : i < nX) : getComp x i h = (toVector x)[i]

  ugetComp (x : X) (i : USize) (h : i.toNat < nX) : K
  ugetComp_spec (x : X) (i : USize) (h : i.toNat < nX) : ugetComp x i h = (toVector x).uget i h

  get (ks : Ks) (off : Nat) (h : off + nX ≤ ArrayType.size ks) : X
  get_spec (ks : Ks) (off : Nat) (h : off + nX ≤ ArrayType.size ks) :
    get ks off h = fromVector (.ofFn fun i => ArrayType.get ks (off + i.1) (by grind))

  uget (ks : Ks) (off : USize) (h : off.toNat + nX ≤ ArrayType.size ks) : X
  -- uget_spec (ks : Ks) (off : USize) (h : off.toNat + nX < ArrayType.size ks) :
  --   uget ks off h
  --   =
  --   fromVector (.ofFn fun i : Fin nX => ArrayType.uget ks (off + i.1.toUSize) sorry)

  set (ks : Ks) (off : Nat) (x : X) (h : off + nX ≤ ArrayType.size ks) : Ks
  set_spec (ks : Ks) (off : Nat) (x : X) (h : off + nX ≤ ArrayType.size ks) :
    (set ks off x h)
    =
    (ArrayType.fromArray <| Vector.toArray <|
      Fin.foldl (n:=nX) (init := Vector.mk (ArrayType.toArray ks) rfl)
        (fun ks i => ks.set (off + i.1) (toVector x)[i] (by simp[← ArrayType.size_spec]; omega)))

  uset (ks : Ks) (off : USize) (x : X) (h : off.toNat + nX ≤ ArrayType.size ks) : Ks
  -- uset_spec (ks : Ks) (off : USize) (x : X) (h : off.toNat + nX < ArrayType.size ks) :
  --   (uset ks off x h)
  --   =
  --   (ArrayType.fromArray <| Vector.toArray <|
  --     Fin.foldl (n:=nX) (init := Vector.mk (ArrayType.toArray ks) rfl)
  --       (fun ks i => ks.uset (off + i.1.toUSize) (toVector x)[i] sorry))

namespace VectorType

variable {R : Type _}
    {X : Type u} {nX : outParam Nat} {Ks : outParam (Type v)} {K : outParam (Type w)}
    [ScalarArray Ks K] [VectorType X nX Ks]

@[simp]
theorem toVector_fromVector (x : Vector K nX) :
  toVector (fromVector (X:=X) x) = x := VectorType.right_inv x

@[simp]
theorem fromVector_toVector (x : X) :
  fromVector (toVector (X:=X) x) = x := VectorType.left_inv x

variable (X) in
theorem size_set {ks : Ks} {off : Nat} {x : X} (h : off + nX ≤ ArrayType.size ks) :
    ArrayType.size (set ks off x h) = ArrayType.size ks := sorry

theorem get_set_eq (ks : Ks) (off : Nat) (x : X)
  (h : off + nX ≤ ArrayType.size ks) (h' : off ≤ i ∧ i < off + nX) :
    ArrayType.get (set ks off x h) i (by rw [size_set _ h]; grind)
    =
    getComp x (i - off) (by grind) := sorry

theorem get_set_ne (ks : Ks) (off : Nat) (x : X)
  (h : off + nX ≤ ArrayType.size ks) (h' : i < off ∨ off + nX ≤ i) (h'' : i < ArrayType.size ks) :
    ArrayType.get (set ks off x h) i (by rw [size_set _ h]; grind)
    =
    ArrayType.get ks i h'' := sorry

variable (R X)

class LawfulZero [Zero X] [Zero K] : Prop where
  getComp_zero (j : Nat) (h : j < nX) : getComp (0 : X) j h = 0

class LawfulAdd [Add X] [Add K] : Prop where
  getComp_add (x y : X) (j : Nat) (h : j < nX) :
    getComp (x + y) j h = getComp x j h + getComp y j h

class LawfulNeg [Neg X] [Neg K] : Prop where
  getComp_neg (x : X) (j : Nat) (h : j < nX) :
    getComp (-x) j h = - getComp x j h

class LawfulSub [Sub X] [Sub K] : Prop where
  getComp_sub (x y : X) (j : Nat) (h : j < nX) :
    getComp (x - y) j h = getComp x j h - getComp y j h

class LawfulSMul [SMul R X] [SMul R K] : Prop where
  getComp_smul (a : R) (x : X) (j : Nat) (h : j < nX) :
    getComp (a • x) j h = a • getComp x j h

section Instances


noncomputable instance : VectorType Real 1 (Array Real) where
  toVector x := #v[x]
  fromVector x := x[0]
  left_inv := by intro _; simp
  right_inv := by intro _; simp; grind

  getComp x _ _ := x
  getComp_spec := by intros; simp

  ugetComp x _ _ := x
  ugetComp_spec := by intros; simp [Vector.uget]

  get xs off _ := xs[off]
  get_spec := by intros; simp [ArrayType.get]

  uget xs off _ := xs[off]

  set xs off x _ := xs.set off x (by simp_all [ArrayType.size])
  set_spec := by intros; simp [ArrayType.fromArray, ArrayType.toArray, Fin.foldl_succ]

  uset xs off x _ := xs.uset off x (by simp_all [ArrayType.size])

instance : LawfulZero Real where
  getComp_zero := by intros; rfl

instance : LawfulAdd Real where
  getComp_add := by intros; rfl

instance : LawfulNeg Real where
  getComp_neg := by intros; rfl

instance : LawfulSub Real where
  getComp_sub := by intros; rfl

instance : LawfulSMul Real Real where
  getComp_smul := by intros; rfl






noncomputable instance : VectorType Float 1 FloatArray where
  toVector x := #v[x]
  fromVector x := x[0]
  left_inv := by intro _; simp
  right_inv := by intro _; simp; grind

  getComp x _ _ := x
  getComp_spec := by intros; simp

  ugetComp x _ _ := x
  ugetComp_spec := by intros; simp [Vector.uget]

  get xs off h := xs.get off h
  get_spec := by intros; simp [ArrayType.get]

  uget xs off h := xs.uget off h

  set xs off x _ := xs.set off x (by simp_all [ArrayType.size])
  set_spec := by intros; simp [ArrayType.fromArray, ArrayType.toArray, Fin.foldl_succ]; rfl

  uset xs off x _ := xs.uset off x (by simp_all [ArrayType.size])

instance : LawfulZero Float where
  getComp_zero := by intros; rfl

instance : LawfulAdd Float where
  getComp_add := by intros; rfl

instance : LawfulNeg Float where
  getComp_neg := by intros; rfl

instance : LawfulSub Float where
  getComp_sub := by intros; rfl

instance : LawfulSMul Float Float where
  getComp_smul := by intros; rfl


end Instances

end VectorType

end NumLean
