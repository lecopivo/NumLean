import NumLean.Data.Scalars.Float64.Basic
import NumLean.Data.Scalars.Float64.Float64Array

import NumLean.Interfaces.SetElem
import NumLean.Interfaces.VectorType.Basic
import NumLean.Interfaces.HasFlatRepr
import NumLean.Interfaces.TensorAlgebra

namespace NumLean

abbrev Float64Array := FloatArray

structure Float64Vector (n : Nat) where
  data : Float64Array
  size_data : data.size = n

namespace Float64Vector

instance {n : Nat} : GetElem (Float64Vector n) Nat Float fun _ i => i < n where
  getElem xs i h := xs.data[i]'(by simp_all[xs.2])

instance {n : Nat} : SetElem (Float64Vector n) Nat Float fun _ i => i < n where
  setElem xs i x h := {
    data := xs.data.set i x (by simp_all[xs.2])
    size_data := by have ⟨xs,h⟩ := xs; simp[FloatArray.size, FloatArray.set]; exact h
  }
  setElem_valid := by simp

instance {n : Nat} : LawfulSetElem (Float64Vector n) Nat where
  getElem_setElem_eq := by
    intros
    simp only [FloatArray.set, FloatArray.get, getElem]
    simp
  getElem_setElem_neq := by
    intros xs _ _ _ _ _ h
    have ⟨⟨xs⟩,_⟩ := xs
    simp only [FloatArray.set, FloatArray.get, getElem]; simp
    rw [Array.getElem_set_ne _ _ h]

@[inline]
def emptyWithCapacity (c : Nat) : Float64Vector 0 :=
    ⟨.emptyWithCapacity c,
    by simp[FloatArray.emptyWithCapacity, FloatArray.size]⟩

@[inline]
def replicate (n : Nat) (x : Float64) : Float64Vector n := ⟨.replicate n x, by simp⟩

@[inline]
def push (xs : Float64Vector n) (x : Float64) : Float64Vector (n+1) :=
  ⟨xs.data.push x, by simp[FloatArray.size, FloatArray.push]; exact xs.2⟩

@[inline]
def pop (xs : Float64Vector n) : Float64Vector (n-1) :=
  ⟨xs.data.pop, by simp[xs.2]⟩

@[inline]
def swap (xs : Float64Vector n) (i j : Nat)
    (hi : i < n := by get_elem_tactic) (hj : j < n := by get_elem_tactic) :
    Float64Vector n :=
  let xi := xs[i]
  let xj := xs[j]
  setElem (setElem xs i xj) j xi

@[inline]
def append (xs : Float64Vector m) (ys : Float64Vector n) : Float64Vector (m + n) :=
  ⟨xs.data.append ys.data, by simp[xs.2, ys.2]⟩

@[inline]
def cast (xs : Float64Vector n) {m : Nat} (h : n = m) : Float64Vector m :=
  ⟨xs.data, by simp [h,xs.2]⟩

@[inline]
def simpCast (xs : Float64Vector n) {m : Nat} (h : n = m := by (conv_lhs => simp); try rfl) : Float64Vector m :=
  xs.cast h

-- def emptyWithCapacity (c : Nat) : Float64Vector 0 :=
--   ⟨Vector.emptyWithCapacity c⟩

-- def replicate (n : Nat) (x : Float) : Float64Vector n :=
--   ⟨Vector.replicate n x⟩

instance : VectorType Float64Vector Float64 where
  toVector xs := ⟨xs.data.1, xs.2⟩
  fromVector xs := ⟨⟨xs.1⟩, xs.2⟩
  left_inv := by intro _; simp
  right_inv := by intro _; simp

  emptyWithCapacity c := emptyWithCapacity c

  get xs i h := xs[i]
  get_spec := by sorry

  set xs i x h := setElem xs i x
  set_spec := sorry

  pop xs := xs.pop
  pop_spec := sorry

  replicate n x := replicate n x
  replicate_spec := sorry

  swap xs i j _ _:= xs.swap i j
  swap_spec := sorry

  push xs x := xs.push x
  push_spec := sorry

  append xs ys := xs.append ys
  append_spec := sorry

-- VectorType.toVector (dst.append (replicate (k - m) default)) =
--     Vector.cast ⋯ ((VectorType.toVector dst).append (Vector.replicate (k - m) default))

open VectorType
@[simp]
theorem toVector_cast (xs : Float64Vector n) (h : n = m) :
    toVector (xs.cast h) = (toVector xs).cast h := sorry

@[simp]
theorem toVector_append (xs : Float64Vector m) (ys : Float64Vector n) :
    toVector (xs.append ys) = (toVector xs).append (toVector ys) := sorry

@[simp]
theorem toVector_replicate (n : Nat) (x : Float64) :
    toVector (replicate n x) = .replicate n x := sorry

instance : HasFlatRepr Float64 Float64Vector 1 where
  toVector x := #v[x]
  fromVector x := x[0]
  left_inv := by intro _; simp
  right_inv := by intro _; grind
  getComp x _ _ := x
  getComp_spec := by intros; simp
  setComp x _ y _ := y
  setComp_spec := by intros; grind
  get xs i _ := xs[i]
  getComp_get_eq_vector_get := by intros; simp[VectorType.get]; grind
  set xs i x _ := setElem xs i x
  vector_get_set_eq := by intros; simp [VectorType.get]; sorry
  vector_get_set_ne := by intros; simp [VectorType.get]; sorry
  push xs x := xs.push x
  vector_get_push_lt := sorry
  vector_get_push_eq := sorry
  toFlatVector x := (emptyWithCapacity 1).push x
  get_toFlatVector_eq_getComp := sorry
  replicate n x := ⟨.replicate n x, by simp⟩
  get_replicate := sorry




end Float64Vector

end NumLean
