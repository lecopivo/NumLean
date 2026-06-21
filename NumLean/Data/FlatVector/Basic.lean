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

def ofFn (f : I → X) : FlatVector X I := Id.run do
  let data : Ks 0 := VectorType.emptyWithCapacity (nI * nX)
  { data := VectorType.fromVector <| Vector.ofFn fun k : Fin (nI * nX) =>
      if hnX : nX = 0 then
        False.elim (Nat.not_lt_zero k.1 (by simpa [hnX] using k.2))
      else
        let hpos : 0 < nX := Nat.pos_of_ne_zero hnX
        let i : I := IndexType.fromFin ⟨k.1 / nX, by
          rw [Nat.div_lt_iff_lt_mul hpos]
          simpa [Nat.mul_comm] using k.2⟩
        FlatRepr.getComp (X := X) (K := K) (f i) (k.1 % nX) (Nat.mod_lt _ hpos) }

@[simp]
theorem getElem_ofFn (f : I → X) (i : I) :
    (ofFn f)[i] = f i := by
  sorry

attribute [simp] FinHTupleMap.injective_rowMajorMap

def replicate [TensorArrayOps Ks K] (x : X) : FlatVector X I :=
  let src := HasFlatVector.toFlatVector (Ks := Ks) x
  let dst := VectorType.emptyWithCapacity (As := Ks) (nI * nX)
  let srcMap := FinHTupleMap.sndMap h(nI) h(nX)
  let dstMap := FinHTupleMap.rowMajorMap h(nI, nX)
  { data := TensorArrayOps.extractSlice (nI * nX) src srcMap dst dstMap
              (FinHTupleMap.injective_rowMajorMap (h(nI, nX))) }

@[simp]
theorem getElem_replicate [TensorArrayOps Ks K] (x : X) (i : I) :
    (replicate (X := X) (I := I) x)[i] = x := by
  sorry

/-! ### Swapping -/

def _root_.NumLean.FinHTupleMap.pair
    {p q} {src : HTuple Nat p} {dst : HTuple Nat q}
    {p' q'} {src' : HTuple Nat p'} {dst' : HTuple Nat q'}
    (map : FinHTupleMap src dst) (map' : FinHTupleMap src' dst') :
    FinHTupleMap (src.prod src') (dst.prod dst') := sorry


@[grind ←]
theorem _root_.NumLean.FinHTupleMap.injective_of_pair
    {p q} {src : HTuple Nat p} {dst : HTuple Nat q}
    {p' q'} {src' : HTuple Nat p'} {dst' : HTuple Nat q'}
    (f : FinHTupleMap src dst) (g : FinHTupleMap src' dst')
    (hf : f.Injective) (hg : g.Injective) :
    (f.pair g).Injective := sorry

open IndexType in
@[inline]
def swap [TensorArrayOps Ks K] [DecidableEq I] (xs : FlatVector X I) (i j : I) : FlatVector X I :=
  if i = j then xs else
    let i := toFin i
    let j := toFin j
    let imap :=
      (FinHTupleMap.const h(nI) (dst := h(nI)) i (by grind)).pair (FinHTupleMap.id h(nX))
      |>.linearize
    let jmap :=
      (FinHTupleMap.const h(nI) (dst := h(nI)) i (by grind)).pair (FinHTupleMap.id h(nX))
      |>.linearize
    { data := TensorArrayOps.swapSliceSelf xs.data imap jmap (by grind) (by grind) sorry }


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
