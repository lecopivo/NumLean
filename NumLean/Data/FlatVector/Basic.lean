import NumLean.Interfaces.IndexType
import NumLean.Interfaces.SetElem
import NumLean.Interfaces.VectorType.Basic
import NumLean.Interfaces.HasFlatVector.Basic
import NumLean.Interfaces.TensorArrayOps.Basic
import NumLean.Data.FinHTuple
import NumLean.Tactic.TBounds

namespace NumLean

/-- A length-indexed flat vector storing one `X` value for every index in `I`.

The underlying vector stores scalar components, so its scalar length is `nI * nX`, where `nI`
is the cardinality of the index type and `nX` is the flat scalar width of each `X`. -/
structure FlatVector (X : Type u) (I : Type v)
    {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatVector X Ks nX] [IndexType I nI] where
  data : Ks (nI * nX)

namespace FlatVector

variable {X : Type u} {I : Type v}
    {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatVector X Ks nX] [IndexType I nI]

/-! ### Preliminary definitions and theorems -/

@[inline]
def offset (i : I) : Nat := (IndexType.toFin i).1 * nX

def size (_xs : FlatVector X I) : Nat := nI

theorem size_eq_card (xs : FlatVector X I) : xs.size = nI := rfl

theorem offset_add_width_le_size (_xs : FlatVector X I) (i : I) :
    offset (nX := nX) i + nX ≤ nI * nX := by
  have hi := (toFin i).2
  simp [offset]
  tbounds

/-! ### Indexing -/

@[inline]
def get (xs : FlatVector X I) (i : I) : X :=
  HasFlatVector.get xs.data (offset (nX := nX) i) (xs.offset_add_width_le_size i)

instance : GetElem (FlatVector X I) I X (fun _ _ => True) where
  getElem xs i _ := get xs i

instance : GetElem? (FlatVector X I) I X (fun _ _ => True) where
  getElem? xs i := some xs[i]

instance : LawfulGetElem (FlatVector X I) I X (fun _ _ => True) where
  getElem?_def xs i _ := by
    simp [getElem?]

theorem getElem_eq_get (xs : FlatVector X I) (i : I) :
    xs[i] = get xs i := by
  rfl

@[simp]
theorem getElem_mk (xs : Ks (nI * nX)) (i : I) :
    (FlatVector.mk (X:=X) (I:=I) xs)[i] = HasFlatVector.get xs ((toFin i).1 * nX) (by
      have hi := (toFin i).2
      tbounds) := by
  rfl

example (i j nX nI : Nat) (hi : i < nI) (hj : j < nX) : i * nX + j < nI * nX := by
  tbounds
example (i nX nI : Nat) (hi : i < nI) : i * nX + nX ≤ nI * nX := by
  tbounds

@[simp]
theorem getComp_getElem_eq_get (xs : FlatVector X I) (i : I) (j : Nat) (hj : j < nX) :
    FlatRepr.getComp K xs[i] j hj
    =
    VectorType.get xs.data ((IndexType.toFin i).1 * nX + j) (by
      have hi := (toFin i).2
      tbounds) := by
  rw[getElem_eq_get];
  simp [get, HasFlatVector.getComp_get_eq_vector_get, offset]
  --
/-! ### Setting -/

@[inline]
def set (xs : FlatVector X I) (i : I) (x : X) : FlatVector X I :=
  { data := HasFlatVector.set xs.data (offset (nX := nX) i) x (xs.offset_add_width_le_size i) }

instance : SetElem (FlatVector X I) I X (fun _ _ => True) where
  setElem xs i x _ := set xs i x
  setElem_valid := by intros; simp

theorem setElem_eq_set (xs : FlatVector X I) (i : I) (x : X) (h : True) :
    setElem xs i x h = set xs i x := by
  rfl

@[simp]
theorem getElem_set_eq (xs : FlatVector X I) (i : I) (x : X) (h : True) :
    (setElem xs i x h)[i] = x := by
  simp [setElem_eq_set, set, offset]

@[simp]
theorem getElem_set_ne (xs : FlatVector X I) (i j : I) (x : X)
    (hi : True) (hj : True) (h : i ≠ j) :
    (setElem xs i x hi)[j] = xs[j] := by
  -- todo: this proof should be seriously simplified
  have hfin : (IndexType.toFin i).1 ≠ (IndexType.toFin j).1 := by
    intro heq
    apply h
    exact (IndexType.equivFin (I := I)).injective (Fin.ext heq)
  have hsep : offset (nX := nX) j + nX ≤ offset (nX := nX) i ∨
      offset (nX := nX) i + nX ≤ offset (nX := nX) j := by
    simp[offset]
    by_cases hij : (IndexType.toFin i).1 < (IndexType.toFin j).1
    · right;
      calc
        offset (nX := nX) i + nX = ((IndexType.toFin i).1 + 1) * nX := by
          simp [offset, Nat.succ_mul]
        _ ≤ (IndexType.toFin j).1 * nX :=
          Nat.mul_le_mul_right nX (Nat.succ_le_of_lt hij)
        _ = offset (nX := nX) j := by simp [offset]
    · have hji : (IndexType.toFin j).1 < (IndexType.toFin i).1 := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt hij) (Ne.symm hfin)
      left
      calc
        offset (nX := nX) j + nX = ((IndexType.toFin j).1 + 1) * nX := by
          simp [offset, Nat.succ_mul]
        _ ≤ (IndexType.toFin i).1 * nX :=
          Nat.mul_le_mul_right nX (Nat.succ_le_of_lt hji)
        _ = offset (nX := nX) i := by simp [offset]
  simpa [setElem_eq_set, get, set, offset] using
    (HasFlatVector.get_set_ne xs.data (offset (nX := nX) i) (offset (nX := nX) j) x
      (xs.offset_add_width_le_size i) hsep (xs.offset_add_width_le_size j))

set_option linter.unnecessarySimpa false in
instance : LawfulSetElem (FlatVector X I) I where
  getElem_setElem_eq xs i v h := by
    simpa using getElem_set_eq xs i v h
  getElem_setElem_neq xs i j v hi hj hne := by
    simpa using getElem_set_ne xs i j v hi hj hne

/-! ### Extensionality -/

@[ext]
theorem ext {xs ys : FlatVector X I} (h : (i : I) → xs[i] = ys[i]) : xs = ys := by
  have ⟨xs⟩ := xs; have ⟨ys⟩ := ys
  simp only [mk.injEq]
  apply VectorType.ext
  have h := fun i j (hj : j < nX) => congrArg (FlatRepr.getComp K · j hj) (h i)
  simp at h
  sorry -- ugh this is annorying we need to split `i = i₁ * nX + i₂`


/-! ### Construction -/

def replicate (x : X) : FlatVector X I := { data := HasFlatVector.replicate nI x }

@[simp]
theorem getElem_replicate (x : X) (i : I) :
    (replicate (X := X) (I := I) x)[i] = x := by
  simp [replicate]


end FlatVector

end NumLean
