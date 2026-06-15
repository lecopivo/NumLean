import NumLean.Data.TensorIndex.FinTIndexIterator
import NumLean.Data.TensorIndex.TensorIndexType
import Init.Data.Iterators.Lemmas.Consumers.Loop

namespace NumLean

namespace TensorIndex

namespace FinTIndex

open Std Std.Iterators Std.Iterators.Types
open scoped BigOperators


def mkIndices {r} (shape : Shape r) : Array (FinTIndex shape) := Id.run do
  let mut a : Array (FinTIndex shape) := #[]
  for i in rowMajorIter shape do
    a := a.push i
  return a


/-- Mixed-radix stride of an axis position in an explicit axis order.

Position `0` is fastest-moving and has stride `1`; later positions multiply the dimensions of all
earlier positions. This is the flat offset model used by `advanceOrderedCoord`. -/
def orderedStride {r : HRank} (shape : Shape r) (order : AxisOrder r) (pos : Nat) : Nat :=
  ∏ i ∈ Finset.range pos, if h : i < r.size then shape.dim (order ⟨i, h⟩) else 1

/-- Mixed-radix flat offset of an ordered coordinate vector. -/
def orderedFlatOffset {r : HRank} (shape : Shape r) (order : AxisOrder r)
    (coord : Vector Nat r.size) : Nat :=
  ∑ i : Fin r.size, coord[i] * orderedStride shape order i.1

/-- Prefix form of `orderedFlatOffset`, useful for induction over axis positions. -/
def orderedFlatOffsetPrefix {r : HRank} (shape : Shape r) (order : AxisOrder r)
    (coord : Vector Nat r.size) (pos : Nat) : Nat :=
  ∑ i ∈ Finset.range pos,
    if h : i < r.size then coord.get ⟨i, h⟩ * orderedStride shape order i else 0

/-- Suffix form of `orderedFlatOffset`, starting at axis position `pos`. -/
def orderedFlatOffsetSuffix {r : HRank} (shape : Shape r) (order : AxisOrder r)
    (coord : Vector Nat r.size) (pos : Nat) : Nat :=
  ∑ i ∈ Finset.Ico pos r.size,
    if h : i < r.size then coord.get ⟨i, h⟩ * orderedStride shape order i else 0

@[simp]
theorem orderedStride_zero {r : HRank} (shape : Shape r) (order : AxisOrder r) :
    orderedStride shape order 0 = 1 := by
  simp [orderedStride]

theorem orderedStride_succ {r : HRank} (shape : Shape r) (order : AxisOrder r)
    {pos : Nat} (hpos : pos < r.size) :
    orderedStride shape order (pos + 1) =
      orderedStride shape order pos * shape.dim (order ⟨pos, hpos⟩) := by
  rw [orderedStride, orderedStride, Finset.prod_range_succ]
  simp [hpos]

@[simp]
theorem orderedFlatOffset_zero {r : HRank} (shape : Shape r) (order : AxisOrder r) :
    orderedFlatOffset shape order (Vector.ofFn fun _ : Fin r.size => 0) = 0 := by
  simp [orderedFlatOffset]

@[simp]
theorem orderedFlatOffsetPrefix_zero {r : HRank} (shape : Shape r) (order : AxisOrder r)
    (coord : Vector Nat r.size) :
    orderedFlatOffsetPrefix shape order coord 0 = 0 := by
  simp [orderedFlatOffsetPrefix]

theorem orderedFlatOffsetPrefix_succ {r : HRank} (shape : Shape r) (order : AxisOrder r)
    (coord : Vector Nat r.size) {pos : Nat} (hpos : pos < r.size) :
    orderedFlatOffsetPrefix shape order coord (pos + 1) =
      orderedFlatOffsetPrefix shape order coord pos +
        coord.get ⟨pos, hpos⟩ * orderedStride shape order pos := by
  rw [orderedFlatOffsetPrefix, orderedFlatOffsetPrefix, Finset.sum_range_succ]
  simp [hpos]

theorem orderedFlatOffsetSuffix_succ {r : HRank} (shape : Shape r) (order : AxisOrder r)
    (coord : Vector Nat r.size) {pos : Nat} (hpos : pos < r.size) :
    orderedFlatOffsetSuffix shape order coord pos =
      coord.get ⟨pos, hpos⟩ * orderedStride shape order pos +
        orderedFlatOffsetSuffix shape order coord (pos + 1) := by
  rw [orderedFlatOffsetSuffix, orderedFlatOffsetSuffix]
  have hico : Finset.Ico pos r.size = insert pos (Finset.Ico (pos + 1) r.size) := by
    ext i
    simp
    omega
  rw [hico]
  rw [Finset.sum_insert]
  · simp [hpos]
  · simp

theorem orderedFlatOffsetPrefix_full {r : HRank} (shape : Shape r) (order : AxisOrder r)
    (coord : Vector Nat r.size) :
    orderedFlatOffsetPrefix shape order coord r.size = orderedFlatOffset shape order coord := by
  rw [orderedFlatOffsetPrefix, orderedFlatOffset]
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro i hi
  split
  · rename_i h
    change coord.get ⟨i, h⟩ * orderedStride shape order i =
      coord.get ⟨i, h⟩ * orderedStride shape order i
    rfl
  · simp

theorem orderedFlatOffsetPrefix_add_suffix {r : HRank} (shape : Shape r) (order : AxisOrder r)
    (coord : Vector Nat r.size) {pos : Nat} (hpos : pos ≤ r.size) :
    orderedFlatOffsetPrefix shape order coord pos +
      orderedFlatOffsetSuffix shape order coord pos = orderedFlatOffset shape order coord := by
  rw [← orderedFlatOffsetPrefix_full shape order coord]
  rw [orderedFlatOffsetPrefix, orderedFlatOffsetSuffix, orderedFlatOffsetPrefix]
  exact Finset.sum_range_add_sum_Ico _ hpos

theorem orderedFlatOffsetPrefix_saturated {r : HRank} {shape : Shape r}
    {order : AxisOrder r} {coord : Vector Nat r.size}
    (hbounds : OrderedBounds shape order coord) {pos : Nat} (hpos : pos ≤ r.size)
    (hsat : ∀ j : Fin r.size, j.1 < pos → shape.dim (order j) ≤ coord[j] + 1) :
    orderedFlatOffsetPrefix shape order coord pos + 1 = orderedStride shape order pos := by
  induction pos with
  | zero => simp
  | succ pos ih =>
      have hposlt : pos < r.size := by omega
      have hposle : pos ≤ r.size := by omega
      have ih' := ih hposle (by
        intro j hj
        exact hsat j (by omega))
      let k : Fin r.size := ⟨pos, hposlt⟩
      have hcoord_succ : coord[k] + 1 = shape.dim (order k) := by
        have hk : k.1 = pos := rfl
        have hle := hsat k (by rw [hk]; omega)
        have hlt := hbounds k
        omega
      rw [orderedFlatOffsetPrefix_succ shape order coord hposlt]
      rw [orderedStride_succ shape order hposlt]
      have hget : coord.get ⟨pos, hposlt⟩ = coord[k] := rfl
      rw [hget]
      nlinarith [ih', hcoord_succ]

theorem orderedFlatOffsetPrefix_eq_zero_of_get_eq_zero {r : HRank} {shape : Shape r}
    {order : AxisOrder r} {coord : Vector Nat r.size} {pos : Nat} (hpos : pos ≤ r.size)
    (hzero : ∀ i : Fin r.size, i.1 < pos → coord[i] = 0) :
    orderedFlatOffsetPrefix shape order coord pos = 0 := by
  induction pos with
  | zero => simp
  | succ pos ih =>
      have hposlt : pos < r.size := by omega
      have hposle : pos ≤ r.size := by omega
      have ih' := ih hposle (by
        intro i hi
        exact hzero i (by omega))
      rw [orderedFlatOffsetPrefix_succ shape order coord hposlt]
      rw [ih']
      let k : Fin r.size := ⟨pos, hposlt⟩
      have hk : k.1 = pos := rfl
      have hcoord : coord[k] = 0 := hzero k (by rw [hk]; omega)
      have hget : coord.get ⟨pos, hposlt⟩ = coord[k] := rfl
      rw [hget, hcoord]
      simp

theorem orderedFlatOffsetPrefix_congr {r : HRank} {shape : Shape r} {order : AxisOrder r}
    {coord coord' : Vector Nat r.size} {pos : Nat}
    (h : ∀ i : Fin r.size, i.1 < pos → coord[i] = coord'[i]) :
    orderedFlatOffsetPrefix shape order coord pos =
      orderedFlatOffsetPrefix shape order coord' pos := by
  rw [orderedFlatOffsetPrefix, orderedFlatOffsetPrefix]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hlt : i < r.size
  · simp only [hlt, dite_true]
    let j : Fin r.size := ⟨i, hlt⟩
    have hj : j.1 < pos := by simpa using hi
    have hget : coord.get j = coord'.get j := h j hj
    change coord.get j * orderedStride shape order i =
      coord'.get j * orderedStride shape order i
    exact congrArg (fun x => x * orderedStride shape order i) hget
  · simp only [hlt, dite_false]

theorem orderedFlatOffsetSuffix_congr {r : HRank} {shape : Shape r} {order : AxisOrder r}
    {coord coord' : Vector Nat r.size} {pos : Nat}
    (h : ∀ i : Fin r.size, pos ≤ i.1 → coord[i] = coord'[i]) :
    orderedFlatOffsetSuffix shape order coord pos =
      orderedFlatOffsetSuffix shape order coord' pos := by
  rw [orderedFlatOffsetSuffix, orderedFlatOffsetSuffix]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hlt : i < r.size
  · simp only [hlt, dite_true]
    let j : Fin r.size := ⟨i, hlt⟩
    have hj : pos ≤ j.1 := by simpa using (Finset.mem_Ico.mp hi).1
    have hget : coord.get j = coord'.get j := h j hj
    change coord.get j * orderedStride shape order i =
      coord'.get j * orderedStride shape order i
    exact congrArg (fun x => x * orderedStride shape order i) hget
  · simp only [hlt, dite_false]

@[simp]
theorem orderedFlatOffset_ext {r : HRank} {shape : Shape r} {order : AxisOrder r}
    {coord coord' : Vector Nat r.size}
    (h : ∀ i : Fin r.size, coord[i] = coord'[i]) :
    orderedFlatOffset shape order coord = orderedFlatOffset shape order coord' := by
  simp [orderedFlatOffset, h]

theorem orderedFlatOffset_advanceOrderedCoord {r : HRank} {shape : Shape r}
    {order : AxisOrder r} {coord coord' : Vector Nat r.size}
    (hbounds : OrderedBounds shape order coord)
    (hnext : advanceOrderedCoord shape order coord = some coord') :
    orderedFlatOffset shape order coord' = orderedFlatOffset shape order coord + 1 := by
  rcases advanceOrderedCoord_eq_update hnext with ⟨k, _hinc, hsat, hupdate⟩
  let pos := k.1
  let stride := orderedStride shape order pos
  let suffix := orderedFlatOffsetSuffix shape order coord (pos + 1)
  have hposlt : pos < r.size := k.2
  have hposle : pos ≤ r.size := Nat.le_of_lt hposlt
  have hpossuccle : pos + 1 ≤ r.size := by omega
  have hprefix : orderedFlatOffsetPrefix shape order coord pos + 1 = stride := by
    simpa [pos, stride] using
      (orderedFlatOffsetPrefix_saturated (shape := shape) (order := order)
        (coord := coord) hbounds hposle hsat)
  have hzero' : ∀ i : Fin r.size, i.1 < pos → coord'[i] = 0 := by
    intro i hi
    have hcoord := hupdate i
    have hlt : i.1 < k.1 := by simpa [pos] using hi
    simp [hlt] at hcoord
    exact hcoord
  have hprefix'_zero : orderedFlatOffsetPrefix shape order coord' pos = 0 := by
    exact orderedFlatOffsetPrefix_eq_zero_of_get_eq_zero (shape := shape) (order := order)
      (coord := coord') hposle hzero'
  have hcoord'_k : coord'[k] = coord[k] + 1 := by
    have hcoord := hupdate k
    simp at hcoord
    exact hcoord
  have hget' : coord'.get ⟨pos, hposlt⟩ = coord'[k] := by
    subst pos
    rfl
  have hget : coord.get ⟨pos, hposlt⟩ = coord[k] := by
    subst pos
    rfl
  have hsuffix_eq : orderedFlatOffsetSuffix shape order coord' (pos + 1) = suffix := by
    dsimp [suffix]
    apply orderedFlatOffsetSuffix_congr
    intro i hi
    have hcoord := hupdate i
    have hnotlt : ¬ i.1 < k.1 := by omega
    have hnoteq : ¬ i.1 = k.1 := by omega
    simp [hnotlt, hnoteq] at hcoord
    exact hcoord
  have hfull' : orderedFlatOffset shape order coord' = (coord[k] + 1) * stride + suffix := by
    have hsplit := orderedFlatOffsetPrefix_add_suffix shape order coord' hpossuccle
    have hsucc := orderedFlatOffsetPrefix_succ shape order coord' hposlt
    rw [hprefix'_zero, hget', hcoord'_k] at hsucc
    rw [← hsplit, hsucc, hsuffix_eq]
    simp [stride]
  have hfull : orderedFlatOffset shape order coord =
      orderedFlatOffsetPrefix shape order coord pos + coord[k] * stride + suffix := by
    have hsplit := orderedFlatOffsetPrefix_add_suffix shape order coord hposle
    have hsuffix := orderedFlatOffsetSuffix_succ shape order coord hposlt
    rw [← hsplit, hsuffix, hget]
    simp [stride, suffix]
    ac_rfl
  rw [hfull', hfull]
  nlinarith [hprefix]

/-- Assumption: canonical row-major `FinTIndex.equivFin` agrees with the mixed-radix
`orderedFlatOffset` for row-major ordered coordinates.

This is the structural product theorem we are intentionally assuming for now. -/
theorem rowMajor_toFin_ofOrderedCoordFin {r : HRank} (shape : Shape r)
    (coord : Vector Nat r.size) (h : OrderedBounds shape (AxisOrder.rowMajor r) coord) :
    ((equivFin shape) (ofOrderedCoordFin shape (AxisOrder.rowMajor r) coord h)).1 =
      orderedFlatOffset shape (AxisOrder.rowMajor r) coord := by
  sorry

theorem rowMajor_initial_offset_zero {r : HRank} (shape : Shape r) (hsize : 0 < shape.size) :
    ∃ coord,
      OrderedBounds shape (AxisOrder.rowMajor r) coord ∧
      (IterState.initial shape).current? = some coord ∧
      orderedFlatOffset shape (AxisOrder.rowMajor r) coord = 0 := by
  let zero : Vector Nat r.size := Vector.ofFn fun _ => 0
  refine ⟨zero, ?_, ?_, ?_⟩
  · intro i
    simpa [zero, Shape.dim] using shape_get_pos_of_size_pos hsize ((AxisOrder.rowMajor r) i)
  · simp [IterState.initial, hsize, zero]
  · simp [orderedFlatOffset, zero]

theorem rowMajor_advance_toFin_succ {r : HRank} {shape : Shape r}
    {coord coord' : Vector Nat r.size}
    (hcoord : OrderedBounds shape (AxisOrder.rowMajor r) coord)
    (hnext : advanceOrderedCoord shape (AxisOrder.rowMajor r) coord = some coord') :
    ((equivFin shape)
        (ofOrderedCoordFin shape (AxisOrder.rowMajor r) coord'
          (advanceOrderedCoord_bounds hcoord hnext))).1 =
      ((equivFin shape) (ofOrderedCoordFin shape (AxisOrder.rowMajor r) coord hcoord)).1 + 1 := by
  rw [rowMajor_toFin_ofOrderedCoordFin]
  rw [rowMajor_toFin_ofOrderedCoordFin]
  exact orderedFlatOffset_advanceOrderedCoord hcoord hnext

theorem rowMajor_initial_toFin_zero {r : HRank} (shape : Shape r) (hsize : 0 < shape.size) :
    ∃ coord hbounds,
      (IterState.initial shape).current? = some coord ∧
      ((equivFin shape) (ofOrderedCoordFin shape (AxisOrder.rowMajor r) coord hbounds)).1 = 0 := by
  rcases rowMajor_initial_offset_zero shape hsize with ⟨coord, hbounds, hcur, hoffset⟩
  refine ⟨coord, hbounds, hcur, ?_⟩
  rw [rowMajor_toFin_ofOrderedCoordFin, hoffset]

theorem rowMajor_leaf_toFin_ofOrderedCoordFin (n : Nat) (coord : Vector Nat 1)
    (h : OrderedBounds (.leaf n) (AxisOrder.rowMajor .leaf) coord) :
    ((equivFin (.leaf n)) (ofOrderedCoordFin (.leaf n) (AxisOrder.rowMajor .leaf) coord h)).1 =
      orderedFlatOffset (.leaf n) (AxisOrder.rowMajor .leaf) coord := by
  simp [equivFin, leafEquiv, ofOrderedCoordFin, orderedFlatOffset, orderedStride]
  change ((coord[0] : Int).toNat) = coord[0]
  exact Int.toNat_natCast _

/-- Right component of a row-major ordered coordinate for a product profile.

In row-major order the right profile is fastest-moving, so it occupies the first positions. -/
def rowMajorRightCoord {p q : HRank} (coord : Vector Nat (p.size + q.size)) :
    Vector Nat q.size :=
  Vector.ofFn fun i : Fin q.size => coord.get ⟨i.1, by omega⟩

/-- Left component of a row-major ordered coordinate for a product profile.

In row-major order the left profile follows the right profile. -/
def rowMajorLeftCoord {p q : HRank} (coord : Vector Nat (p.size + q.size)) :
    Vector Nat p.size :=
  Vector.ofFn fun i : Fin p.size => coord.get ⟨q.size + i.1, by omega⟩

theorem rowMajor_prod_right {p q : HRank} (i : Fin q.size) :
    AxisOrder.rowMajor (.prod p q)
      ⟨i.1, by
        simpa [HTuple.Profile.size] using Nat.lt_of_lt_of_le i.2 (Nat.le_add_left q.size p.size)⟩ =
    HTuple.Index.right (AxisOrder.rowMajor q i) := by
  change HTuple.Index.ofFin (.prod p q)
      (Fin.rev ⟨i.1, by
        simpa [HTuple.Profile.size] using Nat.lt_of_lt_of_le i.2 (Nat.le_add_left q.size p.size)⟩) =
    HTuple.Index.right (HTuple.Index.ofFin q (Fin.rev i))
  have hnot : ¬ (p.size + q.size - (i.1 + 1) < p.size) := by omega
  simp [HTuple.Index.ofFin, Fin.rev, hnot]
  congr 1
  apply Fin.ext
  simp
  omega

theorem rowMajorRightCoord_bounds {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    {coord : Vector Nat (p.size + q.size)}
    (h : OrderedBounds (.prod shape₀ shape₁) (AxisOrder.rowMajor (.prod p q)) coord) :
    OrderedBounds shape₁ (AxisOrder.rowMajor q) (rowMajorRightCoord coord) := by
  intro i
  have hi : i.1 < (HTuple.Profile.prod p q).size := by
    simpa [HTuple.Profile.size] using Nat.lt_of_lt_of_le i.2 (Nat.le_add_left q.size p.size)
  have hprod := h ⟨i.1, hi⟩
  rw [rowMajor_prod_right i] at hprod
  simpa [rowMajorRightCoord, Shape.dim] using hprod

theorem rowMajor_prod_left {p q : HRank} (i : Fin p.size) :
    AxisOrder.rowMajor (.prod p q)
      ⟨q.size + i.1, by simpa [HTuple.Profile.size] using (by omega : q.size + i.1 < p.size + q.size)⟩ =
    HTuple.Index.left (AxisOrder.rowMajor p i) := by
  change HTuple.Index.ofFin (.prod p q)
      (Fin.rev ⟨q.size + i.1, by simpa [HTuple.Profile.size] using (by omega : q.size + i.1 < p.size + q.size)⟩) =
    HTuple.Index.left (HTuple.Index.ofFin p (Fin.rev i))
  have hleft : p.size - (i.1 + 1) < p.size := by
    have hpos : 0 < p.size := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
    omega
  have hrev : p.size + q.size - (q.size + i.1 + 1) = p.size - (i.1 + 1) := by omega
  simp [HTuple.Index.ofFin, Fin.rev, hrev, hleft]

theorem rowMajorLeftCoord_bounds {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    {coord : Vector Nat (p.size + q.size)}
    (h : OrderedBounds (.prod shape₀ shape₁) (AxisOrder.rowMajor (.prod p q)) coord) :
    OrderedBounds shape₀ (AxisOrder.rowMajor p) (rowMajorLeftCoord coord) := by
  intro i
  have hi : q.size + i.1 < (HTuple.Profile.prod p q).size := by
    simpa [HTuple.Profile.size] using (by omega : q.size + i.1 < p.size + q.size)
  have hprod := h ⟨q.size + i.1, hi⟩
  rw [rowMajor_prod_left i] at hprod
  simpa [rowMajorLeftCoord, Shape.dim] using hprod

namespace IterState

/-- The `FinTIndex` iterator emits exactly `remaining` values from any state.

This is the core stepwise iterator lemma: proofs about consumers can reduce to this measure instead
of reasoning about the coordinate carry logic directly. -/
theorem length_eq_remaining {r : HRank} {shape : Shape r}
    (state : IterState shape) :
    ({ internalState := state } : Iter (α := IterState shape) (RowMajorItem shape)).length =
      state.remaining := by
  sorry

end IterState

/-- Row-major bounded-index iteration emits exactly `shape.size` values. -/
theorem rowMajorIter_length {r : HRank} (shape : Shape r) :
    (rowMajorIter shape).length = shape.size := by
  sorry

theorem mkIndices_size_eq_length {r : HRank} (shape : Shape r) :
    (mkIndices shape).size = (rowMajorIter shape).length := by
  rw [← Iter.size_toArray_eq_length (it := rowMajorIter shape)]
  rw [Iter.toArray_eq_fold (it := rowMajorIter shape)]
  simp [mkIndices]

/-- `mkIndices` materializes all row-major bounded indices, so its size is the shape size. -/
theorem mkIndices_size {r : HRank} (shape : Shape r) :
    (mkIndices shape).size = shape.size := by
  rw [mkIndices_size_eq_length, rowMajorIter_length]

def flatUpdatePrefix {α r} (shape : Shape r) (f : FinTIndex shape → α → α) :
    (k : Nat) → k ≤ shape.size → Vector α shape.size → Vector α shape.size
  | 0, _, data => data
  | k + 1, hk, data =>
      have hk' : k ≤ shape.size := Nat.le_trans (Nat.le_succ k) hk
      have hklt : k < shape.size := Nat.lt_of_succ_le hk
      let data' := flatUpdatePrefix shape f k hk' data
      data'.set k (f (fromFin ⟨k, hklt⟩) data'[k]) hklt

def flatUpdateRange {α r} (shape : Shape r) (f : FinTIndex shape → α → α) :
    (start count : Nat) → start + count ≤ shape.size → Vector α shape.size → Vector α shape.size
  | start, 0, _, data => data
  | start, count + 1, h, data =>
      have hstart : start < shape.size := by omega
      have hnext : start + 1 + count ≤ shape.size := by omega
      let data' := data.set start (f (fromFin ⟨start, hstart⟩) data[start]) hstart
      flatUpdateRange shape f (start + 1) count hnext data'

theorem flatUpdateRange_get_before {α r} (shape : Shape r) (f : FinTIndex shape → α → α)
    {start count : Nat} (h : start + count ≤ shape.size) (data : Vector α shape.size)
    {i : Nat} (hi : i < shape.size) (hibefore : i < start) :
    (flatUpdateRange shape f start count h data)[i] = data[i] := by
  induction count generalizing start data with
  | zero => rfl
  | succ count ih =>
      simp [flatUpdateRange]
      have hstart : start < shape.size := by omega
      have hnext : start + 1 + count ≤ shape.size := by omega
      rw [ih hnext]
      · rw [Vector.getElem_set]
        have hne : start ≠ i := by omega
        simp [hne]
      · omega

theorem flatUpdateRange_get_after {α r} (shape : Shape r) (f : FinTIndex shape → α → α)
    {start count : Nat} (h : start + count ≤ shape.size) (data : Vector α shape.size)
    {i : Nat} (hi : i < shape.size) (hiafter : start + count ≤ i) :
    (flatUpdateRange shape f start count h data)[i] = data[i] := by
  induction count generalizing start data with
  | zero => rfl
  | succ count ih =>
      simp [flatUpdateRange]
      have hstart : start < shape.size := by omega
      have hnext : start + 1 + count ≤ shape.size := by omega
      rw [ih hnext]
      · rw [Vector.getElem_set]
        have hne : start ≠ i := by omega
        simp [hne]
      · omega

theorem flatUpdateRange_get_inside {α r} (shape : Shape r) (f : FinTIndex shape → α → α)
    {start count : Nat} (h : start + count ≤ shape.size) (data : Vector α shape.size)
    {i : Nat} (hi : i < shape.size) (hile : start ≤ i) (hilt : i < start + count) :
    (flatUpdateRange shape f start count h data)[i] = f (fromFin ⟨i, hi⟩) data[i] := by
  induction count generalizing start data with
  | zero => omega
  | succ count ih =>
      simp [flatUpdateRange]
      have hstart : start < shape.size := by omega
      have hnext : start + 1 + count ≤ shape.size := by omega
      by_cases his : i = start
      · subst i
        rw [flatUpdateRange_get_before shape f hnext]
        · rw [Vector.getElem_set_self]
        · omega
      · rw [ih hnext]
        · rw [Vector.getElem_set]
          have hne : start ≠ i := by omega
          simp [hne]
        · omega
        · omega

theorem flatUpdateRange_full_eq_map {α r} (shape : Shape r) (data : Vector α shape.size)
    (f : FinTIndex shape → α → α) :
    flatUpdateRange shape f 0 shape.size (by omega) data =
      data.mapFinIdx (fun i x h => f (fromFin ⟨i, h⟩) x) := by
  apply Vector.ext
  intro i hi
  rw [flatUpdateRange_get_inside shape f (by omega) data hi (Nat.zero_le _) (by simpa using hi)]
  simp [Vector.mapFinIdx]

theorem flatUpdatePrefix_get_ge {α r} (shape : Shape r) (f : FinTIndex shape → α → α)
    {k : Nat} (hk : k ≤ shape.size) (data : Vector α shape.size)
    {i : Nat} (hi : i < shape.size) (hki : k ≤ i) :
    (flatUpdatePrefix shape f k hk data)[i] = data[i] := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
      simp [flatUpdatePrefix]
      rw [Vector.getElem_set]
      have hne : k ≠ i := by omega
      simp [hne]
      exact ih (Nat.le_trans (Nat.le_succ k) hk) hi (by omega)

theorem flatUpdatePrefix_get_lt {α r} (shape : Shape r) (f : FinTIndex shape → α → α)
    {k : Nat} (hk : k ≤ shape.size) (data : Vector α shape.size)
    {i : Nat} (hi : i < shape.size) (hik : i < k) :
    (flatUpdatePrefix shape f k hk data)[i] = f (fromFin ⟨i, hi⟩) data[i] := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
      have hk' : k ≤ shape.size := Nat.le_trans (Nat.le_succ k) hk
      have hklt : k < shape.size := Nat.lt_of_succ_le hk
      simp [flatUpdatePrefix]
      by_cases hik' : i < k
      · rw [Vector.getElem_set]
        have hne : k ≠ i := by omega
        simp [hne]
        exact ih hk' hi hik'
      · have hieq : i = k := by omega
        subst i
        rw [Vector.getElem_set_self]
        have hunchanged := flatUpdatePrefix_get_ge shape f hk' data hklt (le_rfl : k ≤ k)
        simpa using congrArg (fun x => f (fromFin ⟨k, hklt⟩) x) hunchanged

theorem flatUpdatePrefix_full_eq_map {α r} (shape : Shape r) (data : Vector α shape.size)
    (f : FinTIndex shape → α → α) :
    flatUpdatePrefix shape f shape.size (Nat.le_refl _) data =
      data.mapFinIdx (fun i x h => f (fromFin ⟨i, h⟩) x) := by
  apply Vector.ext
  intro i hi
  rw [flatUpdatePrefix_get_lt shape f (Nat.le_refl _) data hi hi]
  simp [Vector.mapFinIdx]

theorem flatUpdateRange_full_eq_prefix {α r} (shape : Shape r) (data : Vector α shape.size)
    (f : FinTIndex shape → α → α) :
    flatUpdateRange shape f 0 shape.size (by omega) data =
      flatUpdatePrefix shape f shape.size (Nat.le_refl _) data := by
  rw [flatUpdateRange_full_eq_map, flatUpdatePrefix_full_eq_map]

def tensorMap {α r} (shape : Shape r) (data : Vector α shape.size) (f : FinTIndex shape → α → α) := Id.run do
  let mut data := data
  for i in rowMajorIter shape do
    data := data.set (toFin i) (f i data[toFin i])
  return data

theorem rowMajorIter_fold_set_eq_flatUpdateRange {α r} (shape : Shape r)
    (data : Vector α shape.size) (f : FinTIndex shape → α → α) :
    Iter.fold (fun data i => data.set (toFin i) (f i data[toFin i])) data (rowMajorIter shape) =
      flatUpdateRange shape f 0 shape.size (by omega) data := by
  sorry

theorem rowMajorIter_fold_set_eq_flatUpdatePrefix {α r} (shape : Shape r)
    (data : Vector α shape.size) (f : FinTIndex shape → α → α) :
    Iter.fold (fun data i => data.set (toFin i) (f i data[toFin i])) data (rowMajorIter shape) =
      flatUpdatePrefix shape f shape.size (Nat.le_refl _) data := by
  rw [rowMajorIter_fold_set_eq_flatUpdateRange]
  exact flatUpdateRange_full_eq_prefix shape data f

theorem rowMajorIter_fold_set_eq_map {α r} (shape : Shape r) (data : Vector α shape.size)
    (f : FinTIndex shape → α → α) :
    Iter.fold (fun data i => data.set (toFin i) (f i data[toFin i])) data (rowMajorIter shape) =
      data.mapFinIdx (fun i x h => f (fromFin ⟨i, h⟩) x) := by
  rw [rowMajorIter_fold_set_eq_flatUpdatePrefix]
  exact flatUpdatePrefix_full_eq_map shape data f

theorem tensorMap_eq_map (shape : Shape r) (data : Vector α shape.size) (f : FinTIndex shape → α → α) :
  tensorMap shape data f = data.mapFinIdx (fun i x h => f (fromFin ⟨i,h⟩) x) := by
  unfold tensorMap
  simpa using rowMajorIter_fold_set_eq_map shape data f


end FinTIndex

end TensorIndex

end NumLean
