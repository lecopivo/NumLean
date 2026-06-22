import NumLean.Interfaces.HasFlatArray.Basic
import NumLean.Interfaces.SetElem
import Mathlib.Tactic.GCongr
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Set.Operations

namespace NumLean

structure FlatArray (X : Type u) {Ks K nX} [ArrayOps Ks K] [HasDefaultFlatArray X Ks nX] where
  data : Ks
  h_size : ArrayOps.size data % nX = 0

namespace FlatArray

variable {X : Type u} {Ks K nX} [ArrayOps Ks K] [HasDefaultFlatArray X Ks nX]

/-! ### Preliminary definitions and theorems -/

@[inline]
def offset (i : Nat) : Nat := i * nX

def size (xs : FlatArray X) : Nat := ArrayOps.size xs.data / nX

theorem size_mul_width (xs : FlatArray X) : xs.size * nX = ArrayOps.size xs.data := by
  unfold size
  by_cases h0 : nX = 0
  · subst h0
    have hs : ArrayOps.size xs.data = 0 := by simpa using xs.h_size
    simp [hs]
  · exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero xs.h_size)

theorem offset_add_width_le_size (xs : FlatArray X) {i : Nat} (h : i < xs.size) :
    offset (nX := nX) i + nX ≤ ArrayOps.size xs.data := by
  calc
    offset (nX := nX) i + nX = (i + 1) * nX := by
      simp [offset, Nat.succ_mul]
    _ ≤ xs.size * nX := Nat.mul_le_mul_right nX (Nat.succ_le_of_lt h)
    _ = ArrayOps.size xs.data := xs.size_mul_width

/-! ### Indexing -/

@[inline]
def get (xs : FlatArray X) (i : Nat) (h : i < xs.size) : X :=
  HasFlatArray.get xs.data (offset (nX := nX) i) (xs.offset_add_width_le_size h)

instance : GetElem (FlatArray X) Nat X (fun xs i => i < xs.size) where
  getElem xs i h := get xs i h

theorem getElem_eq_get (xs : FlatArray X) (i : Nat) (h : i < xs.size) :
    xs[i] = get xs i h := by
  rfl

/-! ### Setting -/

@[inline]
def set (xs : FlatArray X) (i : Nat) (x : X) (h : i < xs.size) : FlatArray X :=
  { data := HasFlatArray.set xs.data (offset (nX := nX) i) x (xs.offset_add_width_le_size h)
    h_size := by simp [xs.h_size] }

instance : SetElem (FlatArray X) Nat X (fun xs i => i < xs.size) where
  setElem xs i x h := set xs i x h
  setElem_valid := by
    intros
    simp [set, size]

theorem setElem_eq_set (xs : FlatArray X) (i : Nat) (x : X) (h : i < xs.size) :
    setElem xs i x h = set xs i x h := by
  rfl

@[simp, grind =]
theorem size_set (xs : FlatArray X) (i : Nat) (x : X) (h : i < xs.size) :
    (set xs i x h).size = xs.size := by
  simp [set, size]

@[simp, grind =]
theorem size_setElem (xs : FlatArray X) (i : Nat) (x : X) (h : i < xs.size) :
    (setElem xs i x h).size = xs.size := by
  simp [setElem_eq_set, size_set]

@[simp]
theorem getElem_set_eq (xs : FlatArray X) (i : Nat) (x : X) (h : i < xs.size) :
    (setElem xs i x h)[i]'(by rw [size_setElem]; exact h) = x := by
  simpa [setElem_eq_set, get, set, offset] using
    (HasFlatArray.get_set_eq xs.data (offset (nX := nX) i) x (xs.offset_add_width_le_size h))

@[simp]
theorem getElem_set_ne (xs : FlatArray X) (i j : Nat) (x : X)
    (hi : i < xs.size) (hj : j < xs.size) (h : i ≠ j) :
    (setElem xs i x hi)[j]'(by rw [size_setElem]; exact hj) = xs[j]'hj := by
  have hsep : offset (nX := nX) j + nX ≤ offset (nX := nX) i ∨
      offset (nX := nX) i + nX ≤ offset (nX := nX) j := by
    by_cases hij : i < j
    · right
      calc
        offset (nX := nX) i + nX = (i + 1) * nX := by simp [offset, Nat.succ_mul]
        _ ≤ j * nX := Nat.mul_le_mul_right nX (Nat.succ_le_of_lt hij)
        _ = offset (nX := nX) j := by simp [offset]
    · have hji : j < i := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt hij) (Ne.symm h)
      left
      calc
        offset (nX := nX) j + nX = (j + 1) * nX := by simp [offset, Nat.succ_mul]
        _ ≤ i * nX := Nat.mul_le_mul_right nX (Nat.succ_le_of_lt hji)
        _ = offset (nX := nX) i := by simp [offset]
  simpa [setElem_eq_set, get, set, offset] using
    (HasFlatArray.get_set_ne xs.data (offset (nX := nX) i) (offset (nX := nX) j) x
      (xs.offset_add_width_le_size hi) hsep (xs.offset_add_width_le_size hj))

set_option linter.unnecessarySimpa false in
instance : LawfulSetElem (FlatArray X) Nat where
  getElem_setElem_eq xs i v h := by
    simpa using getElem_set_eq xs i v h
  getElem_setElem_neq xs i j v hi hj hne := by
    simpa using
      getElem_set_ne xs i j v hi
        ((setElem_valid (xs := xs) (i := i) (j := j) (v := v) (hi := hi)).2 hj) hne

/-! ### Extensionality -/

@[ext]
theorem ext {xs ys : FlatArray X}
    (h₁ : xs.size = ys.size)
    (h₂ : (i : Nat) → (hi₁ : i < xs.size) → (hi₂ : i < ys.size) → xs[i] = ys[i]) :
    xs = ys := by
  cases xs with
  | mk xs hxs =>
    cases ys with
    | mk ys hys =>
      have hsize : ArrayOps.size xs = ArrayOps.size ys := by
        have hx :
            (FlatArray.size ({ data := xs, h_size := hxs } : FlatArray X)) * nX =
              ArrayOps.size xs :=
          size_mul_width (X := X) (Ks := Ks) (K := K) (nX := nX)
            { data := xs, h_size := hxs }
        have hy :
            (FlatArray.size ({ data := ys, h_size := hys } : FlatArray X)) * nX =
              ArrayOps.size ys :=
          size_mul_width (X := X) (Ks := Ks) (K := K) (nX := nX)
            { data := ys, h_size := hys }
        rw [← hx, ← hy, h₁]
      have hdata : xs = ys := by
        apply ArrayOps.left_inv.injective
        apply Array.ext
        · simpa [ArrayOps.size_spec] using hsize
        · intro k hkx hky
          have hkx' : k < ArrayOps.size xs := by simpa [ArrayOps.size_spec] using hkx
          have hky' : k < ArrayOps.size ys := by simpa [ArrayOps.size_spec] using hky
          by_cases hnX : nX = 0
          · have hsx : ArrayOps.size xs = 0 := by simpa [hnX] using hxs
            exact False.elim (Nat.not_lt_zero _ (hsx ▸ hkx'))
          · have hpos : 0 < nX := Nat.pos_of_ne_zero hnX
            have hi₁ :
                k / nX < FlatArray.size ({ data := xs, h_size := hxs } : FlatArray X) := by
              rw [Nat.div_lt_iff_lt_mul hpos]
              simpa [size_mul_width (X := X) (Ks := Ks) (K := K) (nX := nX)
                { data := xs, h_size := hxs }] using hkx'
            have hi₂ :
                k / nX < FlatArray.size ({ data := ys, h_size := hys } : FlatArray X) := by
              rw [Nat.div_lt_iff_lt_mul hpos]
              simpa [size_mul_width (X := X) (Ks := Ks) (K := K) (nX := nX)
                { data := ys, h_size := hys }] using hky'
            have hoffx : offset (nX := nX) (k / nX) + nX ≤ ArrayOps.size xs :=
              offset_add_width_le_size (X := X) (Ks := Ks) (K := K) (nX := nX)
                { data := xs, h_size := hxs } hi₁
            have hoffy : offset (nX := nX) (k / nX) + nX ≤ ArrayOps.size ys :=
              offset_add_width_le_size (X := X) (Ks := Ks) (K := K) (nX := nX)
                { data := ys, h_size := hys } hi₂
            have hxy :
                get ({ data := xs, h_size := hxs } : FlatArray X) (k / nX) hi₁ =
                  get ({ data := ys, h_size := hys } : FlatArray X) (k / nX) hi₂ :=
              h₂ (k / nX) hi₁ hi₂
            have hcomp := congrArg
              (fun z => FlatRepr.getComp (X := X) (K := K) z (k % nX) (Nat.mod_lt _ hpos))
              hxy
            simp only [get] at hcomp
            rw [HasFlatArray.getComp_get_eq_array_get (X := X) (K := K) (ks := xs)
                  (off := offset (nX := nX) (k / nX)) (i := k % nX)
                  (hoff := hoffx) (hi := Nat.mod_lt _ hpos),
              HasFlatArray.getComp_get_eq_array_get (X := X) (K := K) (ks := ys)
                  (off := offset (nX := nX) (k / nX)) (i := k % nX)
                  (hoff := hoffy) (hi := Nat.mod_lt _ hpos)] at hcomp
            simp [offset] at hcomp
            simpa [ArrayOps.get_spec, Nat.div_add_mod' k nX] using hcomp
      cases hdata
      simp

/-! ### Empty arrays -/

@[inline]
def emptyWithCapacity (c : Nat) : FlatArray X :=
  { data := ArrayOps.emptyWithCapacity (c * nX)
    h_size := by rw[ArrayOps.size_spec, ArrayOps.emptyWithCapacity_spec]; simp }

def empty : FlatArray X := emptyWithCapacity 0

instance : EmptyCollection (FlatArray X) where
  emptyCollection := empty

instance : Inhabited (FlatArray X) where
  default := ∅

#exit
@[simp]
theorem size_emptyWithCapacity (c : Nat) :
    (emptyWithCapacity (X := X) c).size = 0 := by
  sorry

@[simp]
theorem size_empty : (∅ : FlatArray X).size = 0 := by
  sorry

/-! ### Basic queries -/

def isEmpty (xs : FlatArray X) : Bool := xs.size = 0

instance : GetElem? (FlatArray X) Nat X (fun xs i => i < xs.size) where
  getElem? xs i :=
    if h : i < xs.size then
      some xs[i]
    else
      none

instance : LawfulGetElem (FlatArray X) Nat X (fun xs i => i < xs.size) where

def back? (xs : FlatArray X) : Option X :=
  if h : xs.size - 1 < xs.size then
    some xs[xs.size - 1]
  else
    none

def back (xs : FlatArray X) (h : 0 < xs.size) : X :=
  xs[xs.size - 1]

def back! [Inhabited X] (xs : FlatArray X) : X :=
  xs[xs.size - 1]!

/-! ### Push and pop -/

@[inline]
def push (xs : FlatArray X) (x : X) : FlatArray X :=
  { data := HasFlatArray.push xs.data x
    h_size := by simp [HasFlatArray.size_push, xs.h_size] }

def pop (xs : FlatArray X) : FlatArray X :=
  { data := Nat.iterate ArrayOps.pop nX xs.data
    h_size := by sorry }

theorem size_push_of_pos (xs : FlatArray X) (x : X) (hnX : 0 < nX) :
    (xs.push x).size = xs.size + 1 := by
  sorry

@[simp]
theorem size_pop (xs : FlatArray X) : xs.pop.size = xs.size - 1 := by
  sorry

@[simp]
theorem getElem_push_eq (xs : FlatArray X) (x : X) (hnX : 0 < nX) :
    (xs.push x)[xs.size]'(by rw [size_push_of_pos xs x hnX];
                             exact Nat.lt_succ_self xs.size) = x := by
  sorry

@[simp]
theorem getElem_push_lt (xs : FlatArray X) (x : X) (i : Nat) (hi : i < xs.size)
    (hnX : 0 < nX) :
    (xs.push x)[i]'(by rw [size_push_of_pos xs x hnX]; exact Nat.lt_succ_of_lt hi) = xs[i] := by
  sorry

def ofFn (f : Fin n → X) : FlatArray X :=
  Fin.foldl n (init := emptyWithCapacity n) (fun xs i => xs.push (f i))

@[simp, grind =]
theorem size_ofFn {n} (f : Fin n → X) :
    (ofFn f).size = n := sorry

@[simp]
theorem getElem_ofFn {n} (f : Fin n → X) (i : Nat) (h : i < n) :
    (ofFn f)[i]'(by simp[h]) = f ⟨i, h ⟩ := sorry

/-! ### Replication -/

def Layout {I} (shape : Vector I n) (D : Type) : Type := Unit
def Layout.Compact {I} {shape : Vector I n} {D} (layout : Layout shape D) : Prop := True
def Layout.offset {I} {shape : Vector I n} {D} [Inhabited D] (layout : Layout shape D) : D := default

-- the layout map is maps into shape'
def IndexMap {I} (shape : Vector I n) (shape' : Vector I m) : Type := Unit

def IndexMap.range {I} {shape : Vector I n} {shape' : Vector I m} (map : IndexMap shape shape') : Set (Vector I m) := sorry

def IndexMap.Injective {I} {shape : Vector I n} {shape' : Vector I m} (map : IndexMap shape shape') : Prop := True

/-- Extract a splice of `src` and copies it into a `dst` potentially enlagening `dst` in the process.

To preven uninitialized memory we require that dstLayout is compact and that does not start beyond
the end of `dst`.
If you want to copy into `dst` but with gaps used `copySlice` -/
def TensorOps.extractSlice (shape : Vector Nat n)
    (src : Ks) (srcLayout : IndexMap shape #v[ArrayOps.size src])
    (dst : Ks) (dstLayout : Layout shape Nat)
    (h : dstLayout.Compact) (h' : dstLayout.offset ≤ ArrayOps.size dst) : Ks := sorry

/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i] -/
def TensorOps.copySlice (shape : Vector Nat n)
    (src : Ks) (srcMap : IndexMap shape #v[ArrayOps.size src])
    (dst : Ks) (dstMap : IndexMap shape #v[ArrayOps.size dst])
    (h : dstMap.Injective) : Ks := sorry

/-- this reverse along the first dimension of domain of `map` i.e. swaps src[map (i, j)] with src[map (k-i-1,j)] -/
def TensorOps.reverseSlice (k : Nat) (shape : Vector Nat n)
    (src : Ks) (map : IndexMap (#v[k] ++ shape) #v[ArrayOps.size src])
    (h : map.Injective) : Ks := sorry

/-- transpose element of `src` based on `map` i.e. swaps src[map (i,j)] with src[map (j,i)]. -/
def TensorOps.transposeSlice (shape : Vector Nat n)
    (src : Ks) (map : IndexMap (shape ++ shape) #v[ArrayOps.size src])
    (h : map.Injective) : Ks := sorry

/-- swap data between two arrays -/
def TensorOps.swapSlice (shape : Vector Nat n)
    (xs  : Ks) (map  : IndexMap shape #v[ArrayOps.size xs])
    (xs' : Ks) (map' : IndexMap shape #v[ArrayOps.size xs'])
    (h : map.Injective) (h' : map'.Injective) : Ks × Ks := sorry

def replicate (n : Nat) (x : X) : FlatArray X :=
  let xdata : Ks := HasFlatArray.push (ArrayOps.emptyWithCapacity nX) x
  let xsdata : Ks := ArrayOps.emptyWithCapacity (n * nX)
  let xsdata := TensorOps.extractSlice #v[2, nX] xdata sorry xsdata sorry sorry sorry
  { data := xsdata
    h_size := sorry }

@[simp]
theorem size_replicate (n : Nat) (x : X) :
    (replicate n x).size = n := by
  sorry

@[simp]
theorem getElem_replicate (n : Nat) (x : X) (i : Nat) (h : i < n) :
    (replicate n x)[i]'(by simp[h]) = x := by
  sorry

/-! ### Swapping -/


@[inline]
def swap (xs : FlatArray X) (i j : Nat)
    (hi : i < xs.size := by get_elem_tactic) (hj : j < xs.size := by get_elem_tactic) :
    FlatArray X :=
  if i ≠ j then
    let data := TensorOps.reverseSlice 2 #v[nX] xs.data sorry sorry
    { data := data
      h_size := sorry }
  else
    xs

def swapIfInBounds (xs : FlatArray X) (i j : Nat) : FlatArray X := sorry

@[simp, grind =]
theorem size_swap (xs : FlatArray X) (i j : Nat) (hi : i < xs.size) (hj : j < xs.size) :
    (xs.swap i j hi hj).size = xs.size := by
  sorry

@[simp]
theorem getElem_swap_left (xs : FlatArray X) (i j : Nat)
    (hi : i < xs.size) (hj : j < xs.size) :
    (xs.swap i j hi hj)[i]'(by rw [size_swap]; exact hi) = xs[j]'hj := by
  sorry

@[simp]
theorem getElem_swap_right (xs : FlatArray X) (i j : Nat)
    (hi : i < xs.size) (hj : j < xs.size) :
    (xs.swap i j hi hj)[j]'(by rw [size_swap]; exact hj) = xs[i]'hi := by
  sorry

theorem getElem_swap_of_ne (xs : FlatArray X) (i j k : Nat)
    (hi : i < xs.size) (hj : j < xs.size) (hk : k < xs.size) (hki : k ≠ i) (hkj : k ≠ j) :
    (xs.swap i j hi hj)[k]'(by rw [size_swap]; exact hk) = xs[k]'hk := by
  sorry

/-! ### Append -/


@[inline]
def append (xs ys : FlatArray X) : FlatArray X :=
  { data := ArrayOps.append xs.data ys.data
    h_size := sorry }

instance : Append (FlatArray X) where
  append := append

@[simp, grind =]
theorem size_append_of_pos {xs ys : FlatArray X} :
    (xs ++ ys).size = xs.size + ys.size := by
  sorry

theorem getElem_append_left {xs ys : FlatArray X} {i : Nat} (h : i < xs.size)
    (h' : i < (xs ++ ys).size) :
    (xs ++ ys)[i]'h' = xs[i]'h := by
  sorry

theorem getElem_append_right {xs ys : FlatArray X} {i : Nat}
    (h : xs.size ≤ i) (h' : i < xs.size + ys.size):
    (xs ++ ys)[i]'(by grind) = ys[i - xs.size] := by
  sorry

/-! ### Extraction and slicing -/

def extract (xs : FlatArray X) (start : Nat := 0) (stop : Nat := xs.size) : FlatArray X :=
  { data := ArrayOps.extractSlice ((stop - start) * nX) xs.data (start * nX) 1
    h_size := sorry }

def extractSlice (n : Nat) (xs : FlatArray X) (srcOff srcInc : Nat) : FlatArray X := sorry

def copySlice (n : Nat) (src : FlatArray X) (srcOff srcInc : Nat)
    (dst : FlatArray X) (dstOff dstInc : Nat) : FlatArray X := sorry

@[simp]
theorem size_extract (xs : FlatArray X) (start stop : Nat) :
    (xs.extract start stop).size = min stop xs.size - start := by
  sorry

/-! ### Mutation variants -/

def set! (xs : FlatArray X) (i : Nat) (x : X) : FlatArray X := sorry

def setIfInBounds (xs : FlatArray X) (i : Nat) (x : X) : FlatArray X := sorry

@[simp]
theorem size_set! (xs : FlatArray X) (i : Nat) (x : X) :
    (xs.set! i x).size = xs.size := by
  sorry

@[simp]
theorem size_setIfInBounds (xs : FlatArray X) (i : Nat) (x : X) :
    (xs.setIfInBounds i x).size = xs.size := by
  sorry


instance : ArrayOps (FlatArray X) X where
  toArray xs := .ofFn (fun i : Fin xs.size => xs[i])
  fromArray xs := .ofFn (fun i : Fin xs.size => xs[i])
  left_inv := sorry
  right_inv := sorry
  size := sorry
  size_spec := sorry
  emptyWithCapacity := sorry
  emptyWithCapacity_spec := sorry
  uget := sorry
  uget_spec := sorry
  get := sorry
  get_spec := sorry
  uset := sorry
  uset_spec := sorry
  set := sorry
  set_spec := sorry
  pop := sorry
  pop_spec := sorry
  replicate := sorry
  replicate_spec := sorry
  swap := sorry
  swap_spec := sorry
  push := sorry
  push_spec := sorry
  append := sorry
  append_spec := sorry
  copySlice := sorry
  copySlice_spec := sorry
  extractSlice := sorry
  extractSlice_spec := sorry

end FlatArray

end NumLean
