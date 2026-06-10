import NumLean.Interfaces.ScalarType
import NumLean.Interfaces.IndexType
import NumLean.Interfaces.SetElem

namespace NumLean

/-- A vector of `X` indexed by `I`, stored in a contiguous scalar array. -/
structure Vector (X : Type u) (I : Type v)
    {nX nI Ks K} [IndexType I nI] [ScalarArray Ks K] [VectorType X nX Ks] where
  data : Ks
  h_size : nI * nX = ArrayType.size data

macro X:term " ^[" I:term "]" : term => `(Vector $X $I)

namespace Vector

variable {X I Ks K : Type _} {nX nI : Nat}
variable [IndexType I nI] [ScalarArray Ks K] [VectorType X nX Ks]

@[inline]
def totalSize : Nat := nI * nX

@[inline]
def offset (i : I) : Nat :=
  (IndexType.toFin i).1 * nX

theorem offset_add_width_le_size
    (xs : Vector X I) (i : I) :
    offset (nX:=nX) i + nX ≤ ArrayType.size xs.data := by
  have hi : (IndexType.toFin i).1 + 1 ≤ nI := Nat.succ_le_of_lt (IndexType.toFin i).2
  calc
    offset (nX:=nX) i + nX = ((IndexType.toFin i).1 + 1) * nX := by
      simp [offset, Nat.add_mul]
    _ ≤ nI * nX := Nat.mul_le_mul_right nX hi
    _ = ArrayType.size xs.data := xs.h_size

@[inline]
def get (xs : Vector X I) (i : I) : X :=
  let off := ((toFin i).1 * nX)
  VectorType.get xs.data off
    (by rw[(by simp [Nat.add_mul] : ∀ a b : Nat, a * b + b = (a + 1) * b)]
        have hi : (toFin i).1 + 1 ≤ nI := Nat.succ_le_of_lt (toFin i).2
        rw[← xs.2]
        nlinarith)

instance : GetElem (Vector X I) I X (fun _ _ => True) where
  getElem xs i _ := get xs i

@[inline]
def set (xs : Vector X I (nX := nX) (nI := nI) (Ks := Ks) (K := K)) (i : I) (x : X) :
    Vector X I (nX := nX) (nI := nI) (Ks := Ks) (K := K) :=
  { data := VectorType.set xs.data (offset (nX := nX) i) x
      (offset_add_width_le_size xs i)
    h_size := by sorry }

instance : SetElem (Vector X I) I X (fun _ _ => True) where
  setElem xs i x _ := set xs i x
  setElem_valid := by intros; rfl

theorem getElem_eq_get (xs : Vector X I) (i : I) :
    get xs i = xs[i] := rfl

@[simp]
theorem get_set_eq (xs : Vector X I) (i : I) (x : X) :
    get (set xs i x) i = x := by
  simp only [get,set,VectorType.get_spec]
  apply VectorType.left_inv.injective
  ext i hi
  simp only [VectorType.toVector_fromVector, Vector.getElem_ofFn]
  rw[VectorType.get_set_eq, VectorType.getComp_spec]
  · congr; simp [offset]
  · simp[offset, hi]

@[simp]
theorem get_set_ne (xs : Vector X I) (i j : I) (x : X) (h : i ≠ j) :
    get (set xs i x) j = xs[j] := by
  by_cases 0 = nI
  · sorry
  · simp only [get,set,VectorType.get_spec]
    apply VectorType.left_inv.injective
    ext k hk
    simp only [VectorType.toVector_fromVector, Vector.getElem_ofFn]
    rw[VectorType.get_set_ne]
    · rw[← VectorType.getComp_spec, ← getElem_eq_get]
      unfold Vector.get
      rw[VectorType.get_spec, VectorType.getComp_spec]
      simp
    · unfold offset
      have h' : (toFin i) ≠ (toFin j) := by
        apply (IndexType.left_inv' (I:=I)).injective.ne_iff.2 (by assumption)
      generalize toFin j = j' at h'
      generalize toFin i = i' at h'
      by_cases i' < j'
      · have : i' ≤ j'.1 - 1 := by omega
        right
        calc _ ≤ (j'.1 - 1) * nX + 1 * nX := by gcongr; simp
             _ ≤ j' * nX := by rw[← Nat.add_mul]; grind
             _ ≤ _ := by grind
      · have : j' < i' := by grind
        left
        calc _ ≤ (i'.1 - 1) * nX + k := by gcongr; lia
             _ < (i'.1 - 1) * nX + 1 * nX := by gcongr; lia
             _ ≤ i'.1 * nX := by rw[← Nat.add_mul]; grind
             _ ≤ _ := by grind
    · rw[← xs.2]
      calc _ ≤ (nI - 1) * nX + k := by gcongr; lia
           _ < (nI - 1) * nX + 1 * nX := by gcongr; lia
           _ ≤ nI * nX := by rw[← Nat.add_mul]; grind



@[ext]
theorem ext {xs ys : Vector X I}
    (h : ∀ i : I, get xs i = get ys i) : xs = ys := sorry


instance [Zero K] : Zero (Vector X I) where
  zero :=
    { data := ArrayType.fromArray (Array.replicate (nI * nX) 0)
      h_size := by
        rw [ArrayType.size_spec, ArrayType.toArray_fromArray]
        simp }

instance [One K] : Add (Vector X I) where
  add xs ys :=
    { data := BLASOps.axpby (nI * nX) 1
        xs.data 0 1 1 ys.data 0 1
      h_size := sorry }

-- we only need `1*xi + 1*yi == xi + yi` for `xi yi : K`
@[simp]
theorem add_getElem [RCLike K] [LawfulScalarArray Ks] [Add X] [VectorType.LawfulAdd X]
    (x y : Vector X I) (i : I) :
  (x + y)[i] = x[i] + y[i] := sorry

instance [Neg K] [One K] : Neg (Vector X I) where
  neg xs :=
    { data := BLASOps.scal (nI * nX) (-1 : K) xs.data 0 1
      h_size := sorry }

instance [Neg K] [One K] : Sub (Vector X I) where
  sub xs ys :=
    { data := BLASOps.axpby (nI * nX) 1
        xs.data 0 1 (-1 : K) ys.data 0 1
      h_size := sorry }

instance : SMul K (Vector X I) where
  smul s xs :=
    { data := BLASOps.scal (nI * nX) s xs.data 0 1
      h_size := sorry }

instance : VectorType (Vector X I (nX := nX) (nI := nI) (Ks := Ks) (K := K)) (nI * nX) Ks where
  toVector xs := .ofFn fun i => ArrayType.get xs.data i.1 (by
    rw [← xs.h_size]
    exact i.2)
  fromVector data :=
    { data := ArrayType.fromArray data.toArray
      h_size := by sorry }
  left_inv := by sorry
  right_inv := by sorry
  getComp xs i h := ArrayType.get xs.data i (by
    rw [← xs.h_size]
    exact h)
  getComp_spec := by sorry
  ugetComp xs i h := ArrayType.uget xs.data i (by
    rw [← xs.h_size]
    exact h)
  ugetComp_spec := by sorry
  get ks off h :=
    { data := ArrayType.fromArray <| Array.extractSlice (nI * nX) (ArrayType.toArray ks) off 1
      h_size := by sorry }
  get_spec := by sorry
  uget ks off h :=
    { data := ArrayType.fromArray <| Array.extractSlice (nI * nX) (ArrayType.toArray ks) off.toNat 1
      h_size := by sorry }
  set ks off xs h :=
    sorry
  set_spec := by sorry
  uset ks off xs h :=
    sorry

end Vector

end NumLean
