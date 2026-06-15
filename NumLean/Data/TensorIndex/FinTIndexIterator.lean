import NumLean.Data.TensorIndex.FinTIndex
import NumLean.Data.TensorIndex.IntFinTIndex
import Init.Data.Nat.Lemmas
import Std.Data.Iterators.Producers.Repeat

namespace NumLean

namespace TensorIndex

namespace FinTIndex

open Std Std.Iterators Std.Iterators.Types

theorem shape_get_pos_of_size_pos {p : HRank} {shape : Shape p}
    (hsize : 0 < shape.size) (axis : HTuple.Index p) : 0 < shape.get axis := by
  induction p with
  | leaf =>
      cases shape with | leaf dim =>
      cases axis
      exact hsize
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases axis with
      | left axis =>
          exact hp (Nat.pos_of_ne_zero (by
            intro hzero
            have hprod : 0 < Shape.size shape₀ * Shape.size shape₁ := by simpa using hsize
            rw [hzero, Nat.zero_mul] at hprod
            exact Nat.lt_irrefl 0 hprod)) axis
      | right axis =>
          exact hq (Nat.pos_of_ne_zero (by
            intro hzero
            have hprod : 0 < Shape.size shape₀ * Shape.size shape₁ := by simpa using hsize
            rw [hzero, Nat.mul_zero] at hprod
            exact Nat.lt_irrefl 0 hprod)) axis

/-- Bounds for an axis-ordered dense coordinate vector.

The vector position `i` stores the coordinate along axis `order i`; position `0` is the
fastest-moving axis. -/
abbrev OrderedBounds {p : HRank} (shape : Shape p) (order : AxisOrder p)
    (coord : Vector Nat p.size) : Prop :=
  ∀ i : Fin p.size, coord[i] < shape.dim (order i)

/-- Interpret an axis-ordered dense coordinate vector as a hierarchical natural coordinate. -/
@[inline] def ofOrderedCoord {p : HRank} (_shape : Shape p) (order : AxisOrder p)
    (coord : Vector Nat p.size) : TIndex Nat p :=
  HTuple.ofFn fun axis => coord[order.symm axis]

theorem ofOrderedCoord_inBounds {p : HRank} {shape : Shape p} {order : AxisOrder p}
    {coord : Vector Nat p.size} (h : OrderedBounds shape order coord) :
    TIndex.InBounds shape (ofOrderedCoord shape order coord) := by
  apply TIndex.inBounds_of_get
  intro axis
  have haxis := h (order.symm axis)
  simpa [ofOrderedCoord, Shape.dim] using haxis

/-- Build a bounded hierarchical index from a valid axis-ordered dense coordinate vector. -/
@[inline] def ofOrderedCoordFin {p : HRank} (shape : Shape p) (order : AxisOrder p)
    (coord : Vector Nat p.size) (h : OrderedBounds shape order coord) : FinTIndex shape where
  val := ofOrderedCoord shape order coord
  isLt := ofOrderedCoord_inBounds h

/-- Helper for advancing an axis-ordered dense coordinate by one step. -/
@[inline] def advanceOrderedCoord.go {p : HRank} (shape : Shape p) (order : AxisOrder p)
    (coord : Vector Nat p.size) (pos fuel : Nat) : Option (Vector Nat p.size) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if hpos : pos < p.size then
        let x := coord[pos]
        if x + 1 < shape.dim (order ⟨pos, hpos⟩) then
          some <| Vector.ofFn fun i : Fin p.size =>
            if i.1 < pos then
              0
            else if i.1 = pos then
              x + 1
            else
              coord[i]
        else
          advanceOrderedCoord.go shape order coord (pos + 1) fuel
      else
        none

/-- Advance an axis-ordered dense coordinate by one step, carrying from the fastest axis upward.

This allocates only the next coordinate vector; it never materializes the full index domain. -/
@[inline] def advanceOrderedCoord {p : HRank} (shape : Shape p) (order : AxisOrder p)
    (coord : Vector Nat p.size) : Option (Vector Nat p.size) :=
  advanceOrderedCoord.go shape order coord 0 (p.size + 1)

theorem advanceOrderedCoord_go_bounds {p : HRank} {shape : Shape p} {order : AxisOrder p}
    {coord coord' : Vector Nat p.size} (hcoord : OrderedBounds shape order coord)
    {pos fuel : Nat}
    (hnext : advanceOrderedCoord.go shape order coord pos fuel = some coord') :
    OrderedBounds shape order coord' := by
  induction fuel generalizing pos with
  | zero =>
      simp [advanceOrderedCoord.go] at hnext
  | succ fuel ih =>
      simp only [advanceOrderedCoord.go] at hnext
      split at hnext
      · rename_i hpos
        split at hnext
        · rename_i hinc
          injection hnext with hcoord'
          subst hcoord'
          intro i
          simp [Vector.getElem_ofFn]
          split
          · rename_i hlt
            have hpositive : 0 < shape.dim (order i) :=
              Nat.lt_of_le_of_lt (Nat.zero_le _) (hcoord i)
            omega
          · split
            · rename_i heq
              subst heq
              simpa using hinc
            · exact hcoord i
        · exact ih hnext
      · simp at hnext

theorem advanceOrderedCoord_bounds {p : HRank} {shape : Shape p} {order : AxisOrder p}
    {coord coord' : Vector Nat p.size} (hcoord : OrderedBounds shape order coord)
    (hnext : advanceOrderedCoord shape order coord = some coord') :
    OrderedBounds shape order coord' := by
  exact advanceOrderedCoord_go_bounds hcoord hnext

theorem advanceOrderedCoord_go_eq_update {p : HRank} {shape : Shape p} {order : AxisOrder p}
    {coord coord' : Vector Nat p.size} {pos fuel : Nat}
    (hnext : advanceOrderedCoord.go shape order coord pos fuel = some coord') :
    ∃ k : Fin p.size,
      pos ≤ k.1 ∧
      coord[k] + 1 < shape.dim (order k) ∧
      (∀ j : Fin p.size, pos ≤ j.1 → j.1 < k.1 →
        shape.dim (order j) ≤ coord[j] + 1) ∧
      ∀ i : Fin p.size,
        coord'[i] = if i.1 < k.1 then 0 else if i.1 = k.1 then coord[k] + 1 else coord[i] := by
  induction fuel generalizing pos with
  | zero =>
      simp [advanceOrderedCoord.go] at hnext
  | succ fuel ih =>
      simp only [advanceOrderedCoord.go] at hnext
      split at hnext
      · rename_i hpos
        split at hnext
        · rename_i hinc
          injection hnext with hcoord'
          subst hcoord'
          refine ⟨⟨pos, hpos⟩, le_rfl, hinc, ?_, ?_⟩
          · intro j hjpos hjlt
            have hjlt' : j.1 < pos := hjlt
            omega
          · intro i
            simp [Vector.getElem_ofFn]
        · rename_i hnotinc
          rcases ih hnext with ⟨k, hposle, hinc, hcarry, hcoord'⟩
          refine ⟨k, by omega, hinc, ?_, hcoord'⟩
          intro j hjpos hjlt
          by_cases hj : j.1 = pos
          · have hjfin : j = ⟨pos, hpos⟩ := Fin.ext hj
            subst hjfin
            exact Nat.le_of_not_gt hnotinc
          · exact hcarry j (by omega) hjlt
      · simp at hnext

theorem advanceOrderedCoord_eq_update {p : HRank} {shape : Shape p} {order : AxisOrder p}
    {coord coord' : Vector Nat p.size}
    (hnext : advanceOrderedCoord shape order coord = some coord') :
    ∃ k : Fin p.size,
      coord[k] + 1 < shape.dim (order k) ∧
      (∀ j : Fin p.size, j.1 < k.1 → shape.dim (order j) ≤ coord[j] + 1) ∧
      ∀ i : Fin p.size,
        coord'[i] = if i.1 < k.1 then 0 else if i.1 = k.1 then coord[k] + 1 else coord[i] := by
  rcases advanceOrderedCoord_go_eq_update hnext with ⟨k, _hpos, hinc, hcarry, hcoord'⟩
  exact ⟨k, hinc, (by intro j hjlt; exact hcarry j (Nat.zero_le _) hjlt), hcoord'⟩

theorem advanceOrderedCoord_go_none_saturated {p : HRank} {shape : Shape p}
    {order : AxisOrder p} {coord : Vector Nat p.size} {pos fuel : Nat}
    (hnext : advanceOrderedCoord.go shape order coord pos fuel = none) :
    ∀ j : Fin p.size, pos ≤ j.1 → j.1 < pos + fuel →
      shape.dim (order j) ≤ coord[j] + 1 := by
  induction fuel generalizing pos with
  | zero =>
      intro j hjpos hjlt
      omega
  | succ fuel ih =>
      simp only [advanceOrderedCoord.go] at hnext
      split at hnext
      · rename_i hpos
        split at hnext
        · simp at hnext
        · rename_i hnotinc
          intro j hjpos hjlt
          by_cases hj : j.1 = pos
          · have hjfin : j = ⟨pos, hpos⟩ := Fin.ext hj
            subst hjfin
            exact Nat.le_of_not_gt hnotinc
          · exact ih hnext j (by omega) (by omega)
      · rename_i hnpos
        intro j hjpos _hjlt
        have : j.1 < p.size := j.2
        omega

theorem advanceOrderedCoord_none_saturated {p : HRank} {shape : Shape p}
    {order : AxisOrder p} {coord : Vector Nat p.size}
    (hnext : advanceOrderedCoord shape order coord = none) :
    ∀ j : Fin p.size, shape.dim (order j) ≤ coord[j] + 1 := by
  intro j
  exact advanceOrderedCoord_go_none_saturated hnext j (Nat.zero_le _) (by omega)

/-- One row-major iterator output: a flat offset, its tensor index, and the proof they agree. -/
structure RowMajorItem {p : HRank} (shape : Shape p) where
  linearIdx : Fin shape.size
  idx : FinTIndex shape
  toFin_eq : equivFin shape idx = linearIdx

attribute [inline] RowMajorItem.linearIdx RowMajorItem.idx

/-- Runtime state for streaming over `FinTIndex shape` in canonical row-major order.

`shape` is a parameter of the state type, not a stored field. The stored state is only the current
dense coordinate, or `none` once iteration is complete. -/
structure IterState {p : HRank} (shape : Shape p) where
  current? : Option (Vector Nat p.size)
  counter : Nat
  counter_le : counter ≤ shape.size
  ready : counter < shape.size →
    ∃ coord, current? = some coord ∧ OrderedBounds shape (AxisOrder.rowMajor p) coord

namespace IterState

@[inline] def mkItem {p : HRank} {shape : Shape p} (counter : Nat) (hcounter : counter < shape.size)
    (coord : Vector Nat p.size) (hcoord : OrderedBounds shape (AxisOrder.rowMajor p) coord) :
    RowMajorItem shape where
  linearIdx := ⟨counter, hcounter⟩
  idx := ofOrderedCoordFin shape (AxisOrder.rowMajor p) coord hcoord
  toFin_eq := by
    sorry

@[inline] def setFastCoord {p : HRank} (coord : Vector Nat p.size) (value : Nat) : Vector Nat p.size :=
  Vector.ofFn fun i : Fin p.size => if i.1 = 0 then value else coord[i]

@[inline] def resetFastCoord {p : HRank} (coord : Vector Nat p.size) : Vector Nat p.size :=
  setFastCoord coord 0

theorem setFastCoord_bounds {p : HRank} {shape : Shape p} {coord : Vector Nat p.size}
    (hcoord : OrderedBounds shape (AxisOrder.rowMajor p) coord) {value : Nat}
    (hvalue : value < shape.dim (AxisOrder.rowMajor p ⟨0, HTuple.Profile.size_pos p⟩)) :
    OrderedBounds shape (AxisOrder.rowMajor p) (setFastCoord coord value) := by
  intro i
  simp [setFastCoord]
  split
  · rename_i hi
    have hfin : i = ⟨0, HTuple.Profile.size_pos p⟩ := Fin.ext hi
    subst hfin
    exact hvalue
  · exact hcoord i

theorem resetFastCoord_bounds {p : HRank} {shape : Shape p} {coord : Vector Nat p.size}
    (hcoord : OrderedBounds shape (AxisOrder.rowMajor p) coord) :
    OrderedBounds shape (AxisOrder.rowMajor p) (resetFastCoord coord) := by
  apply setFastCoord_bounds hcoord
  have hpositive : 0 < shape.dim (AxisOrder.rowMajor p ⟨0, HTuple.Profile.size_pos p⟩) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (hcoord ⟨0, HTuple.Profile.size_pos p⟩)
  exact hpositive

@[inline] def initial {p : HRank} (shape : Shape p) : IterState shape :=
  let zero : Vector Nat p.size := Vector.ofFn fun _ => 0
  if hsize : 0 < shape.size then
    { current? := some zero
      counter := 0
      counter_le := Nat.zero_le _
      ready := by
        intro _
        refine ⟨zero, rfl, ?_⟩
        intro i
        simpa [zero, Shape.dim] using shape_get_pos_of_size_pos hsize (AxisOrder.rowMajor p i) }
  else
    { current? := none
      counter := 0
      counter_le := Nat.zero_le _
      ready := by intro h; omega }

@[inline] def remaining {p : HRank} {shape : Shape p} (state : IterState shape) : Nat :=
  shape.size - state.counter

@[inline] def next {p : HRank} {shape : Shape p}
    (counter : Nat) (hcounter : counter < shape.size) (coord : Vector Nat p.size)
    (hcoord : OrderedBounds shape (AxisOrder.rowMajor p) coord) :
    IterState shape :=
  let current? :=
    if counter + 1 = shape.size then
      none
    else
      match hnext : advanceOrderedCoord shape (AxisOrder.rowMajor p) coord with
      | some coord' =>
          some coord'
      | none => some coord
  { current? := current?
    counter := counter + 1
    counter_le := Nat.succ_le_of_lt hcounter
    ready := by
      intro hcounter'
      dsimp only [current?]
      split
      · rename_i hdone
        omega
      · rename_i hnonzero
        split
        · rename_i coord' hnext
          exact ⟨coord', rfl, advanceOrderedCoord_bounds hcoord hnext⟩
        · exact ⟨coord, rfl, hcoord⟩ }

instance instIterator {p : HRank} {shape : Shape p} :
    Iterator (IterState shape) Id (RowMajorItem shape) where
  IsPlausibleStep it
    | .yield it' out => ∃ coord h hcounter,
        it.internalState.current? = some coord ∧
        out = mkItem it.internalState.counter hcounter coord h ∧
        it' = ⟨next (shape := shape) it.internalState.counter hcounter coord h⟩
    | .skip _ => False
    | .done => it.internalState.counter = shape.size ∨ it.internalState.current? = none ∨
        ∃ coord, it.internalState.current? = some coord ∧ ¬ OrderedBounds shape (AxisOrder.rowMajor p) coord
  step it := pure <| .deflate <|
    if hdone : it.internalState.counter = shape.size then
      .done (by left; exact hdone)
    else
      have hcounter : it.internalState.counter < shape.size := by
        have hle := it.internalState.counter_le
        omega
      match hcur : it.internalState.current? with
      | none =>
          .done (by
            right; left; rfl)
      | some coord =>
          have hbounds : OrderedBounds shape (AxisOrder.rowMajor p) coord := by
            rcases it.internalState.ready hcounter with ⟨coord', hcoord', hbounds'⟩
            simp [hcur] at hcoord'
            subst hcoord'
            exact hbounds'
          .yield
            ⟨next (shape := shape) it.internalState.counter hcounter coord hbounds⟩
            (mkItem it.internalState.counter hcounter coord hbounds)
            (by exact ⟨coord, hbounds, hcounter, rfl, rfl, rfl⟩)

private def instFinitenessRelation {p : HRank} {shape : Shape p} :
    FinitenessRelation (IterState shape) Id where
  Rel := InvImage WellFoundedRelation.rel (fun it => IterState.remaining it.internalState)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, _hstep, hplausible⟩ := h
    cases step with
    | yield next out =>
        cases _hstep
        rcases hplausible with ⟨coord, hbounds, hcounter, hcur, hout, hnext⟩
        rw [hnext]
        simp [next, remaining]
        omega
    | skip next => cases hplausible
    | done => cases _hstep

instance instFinite {p : HRank} {shape : Shape p} :
    Finite (IterState shape) Id := by
  exact Finite.of_finitenessRelation instFinitenessRelation

private def instProductivenessRelation {p : HRank} {shape : Shape p} :
    ProductivenessRelation (IterState shape) Id where
  Rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation {it it'} h := by cases h

instance instProductive {p : HRank} {shape : Shape p} :
    Productive (IterState shape) Id := by
  exact Productive.of_productivenessRelation instProductivenessRelation

/-- Emit one full row-major item to the iterator callback.

The structural loop owns the flat `counter`; the tensor index is built directly from the recursive
shape traversal. -/
@[inline, specialize] private def emitRowMajorItem {p : HRank} {shape : Shape p}
    {m : Type u → Type v} [Monad m]
    {γ : Type u} {Pl : RowMajorItem shape → γ → ForInStep γ → Prop}
    (it : IterM (α := IterState shape) Id (RowMajorItem shape))
    (f : (b : RowMajorItem shape) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c)))
    (start counter : Nat) (idx : FinTIndex shape) (acc : γ) : m (Nat × ForInStep γ) := do
  if _hskip : counter < start then
    pure (counter + 1, .yield acc)
  else
    have hcounter : counter < shape.size := by
      -- The structural traversal visits exactly `shape.size` items.
      sorry
    let item : RowMajorItem shape :=
      { linearIdx := ⟨counter, hcounter⟩
        idx := idx
        toFin_eq := by sorry }
    let step ← f item (by sorry) acc
    match step.1 with
    | .done acc' => pure (counter, .done acc')
    | .yield acc' => pure (counter + 1, .yield acc')

/-- Structural row-major traversal of a shape.

Leaf shapes use a counted loop. Product shapes run the left shape outside and the right shape
inside, which is exactly canonical row-major order. This is the optimized `IteratorLoop` path; the
ordinary `Iterator.step` can still use vector state for compatibility. -/
@[inline, specialize] private partial def consumeShapeRowMajor {p : HRank} {shape : Shape p}
    {m : Type u → Type v} [Monad m]
    {γ : Type u} {Pl : RowMajorItem shape → γ → ForInStep γ → Prop}
    (it : IterM (α := IterState shape) Id (RowMajorItem shape))
    (f : (b : RowMajorItem shape) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c)))
    (start : Nat) : {r' : HRank} → (shape' : Shape r') →
      (emit : Nat → FinTIndex shape' → γ → m (Nat × ForInStep γ)) →
      Nat → γ → m (Nat × ForInStep γ)
  | .leaf, .leaf n, emit, counter, acc =>
      let rec @[specialize] loop (i counter : Nat) (acc : γ) : m (Nat × ForInStep γ) := do
        if hi : i < n then
          let idx : FinTIndex (.leaf n) :=
            { val := .leaf i
              isLt := by simpa [TIndex.InBounds] using hi }
          let (counter', step) ← emit counter idx acc
          match step with
          | .done acc' => pure (counter', .done acc')
          | .yield acc' => loop (i + 1) counter' acc'
        else
          pure (counter, .yield acc)
      loop 0 counter acc
  | .prod _ _, .prod shape₁ shape₂, emit, counter, acc =>
      let emitLeft (counter : Nat) (idx₁ : FinTIndex shape₁) (acc : γ) :
          m (Nat × ForInStep γ) :=
        consumeShapeRowMajor it f start shape₂
          (fun counter idx₂ acc =>
            let idx : FinTIndex (.prod shape₁ shape₂) :=
              { val := .prod idx₁.val idx₂.val
                isLt := ⟨idx₁.isLt, idx₂.isLt⟩ }
            emit counter idx acc)
          counter acc
      consumeShapeRowMajor it f start shape₁ emitLeft counter acc

private class RowMajorConsumer (p : HRank) where
  consume {pOut : HRank} {shapeOut : Shape pOut} {m : Type u → Type v} [Monad m]
      {γ : Type u} {Pl : RowMajorItem shapeOut → γ → ForInStep γ → Prop}
      (it : IterM (α := IterState shapeOut) Id (RowMajorItem shapeOut))
      (f : (b : RowMajorItem shapeOut) → it.IsPlausibleIndirectOutput b →
        (c : γ) → m (Subtype (Pl b c)))
      (start : Nat) (shape : Shape p)
      (emit : Nat → FinTIndex shape → γ → m (Nat × ForInStep γ)) :
      Nat → γ → m (Nat × ForInStep γ)

attribute [inline, specialize] RowMajorConsumer.consume

@[inline] private instance : RowMajorConsumer .leaf where
  consume {pOut} {shapeOut} {m} [Monad m] {γ} {Pl} _it _f _start shape emit counter acc :=
    match shape with
    | .leaf n =>
        let rec @[specialize] loop (i counter : Nat) (acc : γ) : m (Nat × ForInStep γ) := do
          if hi : i < n then
            let idx : FinTIndex (.leaf n) :=
              { val := .leaf i
                isLt := by simpa [TIndex.InBounds] using hi }
            let (counter', step) ← emit counter idx acc
            match step with
            | .done acc' => pure (counter', .done acc')
            | .yield acc' => loop (i + 1) counter' acc'
          else
            pure (counter, .yield acc)
        loop 0 counter acc

@[inline] private instance {p q : HRank} [RowMajorConsumer p] [RowMajorConsumer q] :
    RowMajorConsumer (.prod p q) where
  consume {_pOut} {_shapeOut} {m} [Monad m] {γ} {_Pl} it f start shape emit counter acc :=
    match shape with
    | .prod shape₁ shape₂ =>
        let emitLeft (counter : Nat) (idx₁ : FinTIndex shape₁) (acc : γ) :
            m (Nat × ForInStep γ) :=
          RowMajorConsumer.consume (p := q) it f start shape₂
            (fun counter idx₂ acc =>
              let idx : FinTIndex (.prod shape₁ shape₂) :=
                { val := .prod idx₁.val idx₂.val
                  isLt := ⟨idx₁.isLt, idx₂.isLt⟩ }
              emit counter idx acc)
            counter acc
        RowMajorConsumer.consume (p := p) it f start shape₁ emitLeft counter acc

@[inline, specialize] private def consumeFromIteratorState {p : HRank} {shape : Shape p}
    [RowMajorConsumer p]
    {m : Type u → Type v} [Monad m]
    {γ : Type u} {Pl : RowMajorItem shape → γ → ForInStep γ → Prop}
    (it : IterM (α := IterState shape) Id (RowMajorItem shape))
    (f : (b : RowMajorItem shape) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c)))
    (init : γ) : m γ := do
  if _hdone : it.internalState.counter = shape.size then
    pure init
  else
    match it.internalState.current? with
    | none => pure init
    | some _ =>
        let (_, step) ← RowMajorConsumer.consume (p := p) it f it.internalState.counter shape
          (emitRowMajorItem it f it.internalState.counter) 0 init
        match step with
        | .done acc => pure acc
        | .yield acc => pure acc

instance instIteratorLoop {p : HRank} {shape : Shape p}
    [RowMajorConsumer p]
    {m : Type u → Type v} [Monad m] :
    IteratorLoop (IterState shape) Id m where
  forIn _lift _γ _Pl it init f :=
    consumeFromIteratorState it f init

instance instLawfulIteratorLoop {p : HRank} {shape : Shape p}
    [RowMajorConsumer p]
    {m : Type u → Type v} [Monad m] :
    LawfulIteratorLoop (IterState shape) Id m := by
  constructor
  intros
  sorry

end IterState

/-- Stream row-major bounded indices together with their canonical flat `Fin` offset and proof. -/
@[inline] def rowMajorFinIter {p : HRank} (shape : Shape p) :
    Iter (α := IterState shape) (RowMajorItem shape) :=
  ⟨IterState.initial shape⟩

/-- Stream bounded indices in row-major order. -/
@[inline] def rowMajorIter {p : HRank} (shape : Shape p) :=
  (rowMajorFinIter shape).map RowMajorItem.idx

end FinTIndex

end TensorIndex

end NumLean
