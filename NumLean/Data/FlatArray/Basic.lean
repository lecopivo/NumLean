import NumLean.Interfaces.HasFlatArray.Basic
import NumLean.Interfaces.SetElem

namespace NumLean

structure FlatArray (X : Type u) {Ks K nX} [ArrayType Ks K] [HasDefaultFlatArray X Ks nX] where
  data : Ks
  h_size : ArrayType.size data % nX = 0

namespace FlatArray

variable {X : Type u} {Ks K nX} [ArrayType Ks K] [HasDefaultFlatArray X Ks nX]

def size (xs : FlatArray X) : Nat := ArrayType.size xs.data / nX

instance : GetElem (FlatArray X) Nat X (fun xs i => i < xs.size) where
  getElem xs i h := HasFlatArray.get xs.data (i*nX) (by simp [size] at h; sorry)

instance : SetElem (FlatArray X) Nat X (fun xs i => i < xs.size) where
  setElem xs i x h :=
    { data := HasFlatArray.set xs.data (i*nX) x sorry
      h_size := by simp [xs.h_size] }
  setElem_valid := by
    intros; simp [size]

@[simp, grind =]
theorem size_setElem (xs : FlatArray X) (i : Nat) (x : X) (h) :
    (setElem xs i x h).size
    =
    xs.size := by
  simp only [size, setElem, HasFlatArray.size_set]

@[simp]
theorem get_set_eq (xs : FlatArray X) (i : Nat) (x : X) (h) :
    (setElem xs i x h)[i]'(by grind)
    =
    x := by
  simp [setElem, getElem, HasFlatArray.get_set_eq]

@[simp]
theorem get_set_ne (xs : FlatArray X) (i j : Nat) (x : X) (hi hj) (h : i ≠ j) :
    (setElem xs i x hi)[j]'(by grind)
    =
    xs[j]'hj := by
  simp only [setElem, getElem]
  simp only [FlatArray.size] at hi hj
  rw[HasFlatArray.get_set_ne]
  by_cases i < j
  · right
    sorry
  · left
    have : j < i := by grind
    sorry

-- instance : GetElem (FlatArray X) USize X (fun xs i => i.toNat < xs.size) where
--   getElem x i h := FlatArray.uget x.data (i*nX) (by simp_all [size]; sorry)
