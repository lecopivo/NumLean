module

public import NumLean.Data.Scalars.Float64.Basic
public import NumLean.Data.Scalars.Float64.Float64Array
import all Init.Data.FloatArray.Basic

public import NumLean.Interfaces.SetElem

@[expose] public section

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
def simpCast (xs : Float64Vector n) {m : Nat} (h : n = m := by simp) : Float64Vector m :=
  xs.cast h

end Float64Vector

end NumLean
