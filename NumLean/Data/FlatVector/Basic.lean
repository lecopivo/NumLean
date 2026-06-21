import NumLean.Interfaces.IndexType
import NumLean.Interfaces.SetElem
import NumLean.Interfaces.VectorType.Basic
import NumLean.Interfaces.HasFlatVector.Basic
import NumLean.Interfaces.TensorArrayOps.Basic
import NumLean.Data.FinHTuple

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
  calc
    offset (nX := nX) i + nX = ((IndexType.toFin i).1 + 1) * nX := by
      simp [offset, Nat.succ_mul]
    _ ≤ nI * nX := Nat.mul_le_mul_right nX (Nat.succ_le_of_lt (IndexType.toFin i).2)

/-! ### Indexing -/

@[inline]
def get (xs : FlatVector X I) (i : I) : X :=
  HasFlatVector.get xs.data (offset (nX := nX) i) (xs.offset_add_width_le_size i)

instance : GetElem (FlatVector X I) I X (fun _ _ => True) where
  getElem xs i _ := get xs i

theorem getElem_eq_get (xs : FlatVector X I) (i : I) (h : True) :
    xs[i] = get xs i := by
  rfl

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
  simpa [setElem_eq_set, get, set, offset] using
    (HasFlatVector.get_set_eq xs.data (offset (nX := nX) i) x (xs.offset_add_width_le_size i))

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
  sorry

/-! ### Basic queries -/

instance : GetElem? (FlatVector X I) I X (fun _ _ => True) where
  getElem? xs i := some xs[i]

instance : LawfulGetElem (FlatVector X I) I X (fun _ _ => True) where
  getElem?_def xs i _ := by
    simp [getElem?]

def back? (xs : FlatVector X I) : Option X :=
  if h : nI = 0 then none else
    some (get xs (IndexType.fromFin ⟨nI - 1, by omega⟩))

def back (xs : FlatVector X I) (h : 0 < nI) : X :=
  get xs (IndexType.fromFin ⟨nI - 1, by omega⟩)

def back! [Inhabited X] (xs : FlatVector X I) : X :=
  if h : 0 < nI then back xs h else default

/-! ### Construction -/

set_option backward.do.legacy false

variable [Inhabited K]

def ofFn (f : I → X) : FlatVector X I := Id.run do
  -- todo: this is probably not the best implementation
  --       we probably want to work unsized based ArrayType and do a sequence of `push`
  let mut r : FlatVector X I := { data := VectorType.replicate (nI * nX) default }
  for_all h : i in 0...nI do
    let i : I := fromFin ⟨i, h.2⟩
    r[i] := f i
  return r

@[simp]
theorem getElem_ofFn (f : I → X) (i : I) :
    (ofFn f)[i] = f i := by
  sorry

def replicate [Inhabited K] (x : X) : FlatVector X I := sorry

@[simp]
theorem getElem_replicate [TensorArrayOps Ks K] (x : X) (i : I) :
    (replicate (X := X) (I := I) x)[i] = x := by
  sorry

/-! ### Swapping -/

open IndexType FinHTupleMap in
@[inline]
def swapSlice [TensorArrayOps Ks K] (xs : FlatVector X I) (len i j : Nat) : FlatVector X I := sorry
  --   (h : i + len < j ∨ j + len < i) : -- non-overlaping
  --   FlatVector X I :=
  -- if h : i = j then xs else
  --   let i := toFin i
  --   let j := toFin j
  --   let imap := (FinHTupleMap.point h(nI) i).pair (FinHTupleMap.id h(nX)) |>.linearize
  --   have hi : imap.Injective := by grind
  --   let jmap := (FinHTupleMap.point h(nI) j).pair (FinHTupleMap.id h(nX)) |>.linearize
  --   have hj : jmap.Injective := by grind
  --   have hij : i ≠ j := by sorry -- todo: set up IndexType with grind!
  --   have hdisjoint : Disjoint imap.range jmap.range := by grind
  --   { data := TensorArrayOps.swapSliceSelf xs.data imap jmap hi hj hdisjoint }

-- @[simp, grind =]
-- theorem size_swap [DecidableEq I] (xs : FlatVector X I) (i j : I) :
--     (xs.swap i j).size = xs.size := by
--   by_cases h : i = j <;> simp [swap, h]
--   sorry

-- @[simp]
-- theorem getElem_swap_left [DecidableEq I] (xs : FlatVector X I) (i j : I) :
--     (xs.swap i j)[i] = xs[j] := by
--   sorry

-- @[simp]
-- theorem getElem_swap_right [DecidableEq I] (xs : FlatVector X I) (i j : I) :
--     (xs.swap i j)[j] = xs[i] := by
--   sorry

-- theorem getElem_swap_of_ne [DecidableEq I] (xs : FlatVector X I) (i j k : I) (hki : k ≠ i) (hkj : k ≠ j) :
--     (xs.swap i j)[k] = xs[k] := by
--   sorry

/-! ### Mutation variants -/

def set! (xs : FlatVector X I) (i : I) (x : X) : FlatVector X I :=
  set xs i x

def setIfInBounds (xs : FlatVector X I) (i : I) (x : X) : FlatVector X I :=
  set xs i x

@[simp]
theorem size_set! (xs : FlatVector X I) (i : I) (x : X) :
    (xs.set! i x).size = xs.size := by
  rfl

@[simp]
theorem size_setIfInBounds (xs : FlatVector X I) (i : I) (x : X) :
    (xs.setIfInBounds i x).size = xs.size := by
  rfl

end FlatVector

end NumLean
