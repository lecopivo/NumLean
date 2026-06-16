import NumLean.Data.TensorIndex.FinTIndexIterator
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
import Init.Data.List.Nat.Range

namespace NumLean

namespace TensorIndex

namespace FinTIndex

open Std Std.Iterators Std.Iterators.Types

namespace RowMajorIterator

variable {p : HRank} {shape : Shape p}

/-- A structurally generated row-major output together with its mathematical validity proof. -/
private structure Output {p : HRank} (shape : Shape p) where
  linear : Nat
  idx : TIndex Nat p
  valid : RowMajor.Valid shape (linear, idx)

private def leafOutput (n : Nat) (i : { j // j < n }) : Output (.leaf n) :=
  { linear := i.1
    idx := .leaf i.1
    valid := { linear_lt := i.2, idx_inBounds := i.2, toFin_eq := by rfl } }

private def prodOutput {p q : HRank} {shape₁ : Shape p} {shape₂ : Shape q}
    (out₁ : Output shape₁) (out₂ : Output shape₂) : Output (.prod shape₁ shape₂) :=
  let linear := out₂.linear + Shape.size shape₂ * out₁.linear
  have hlinear : linear < Shape.size (.prod shape₁ shape₂) := by
    have h₁ := out₁.valid.linear_lt
    have h₂ := out₂.valid.linear_lt
    simp [Shape.size]
    calc
      out₂.linear + Shape.size shape₂ * out₁.linear
          < Shape.size shape₂ + Shape.size shape₂ * out₁.linear :=
        Nat.add_lt_add_right h₂ _
      _ = Shape.size shape₂ * (out₁.linear + 1) := by
        rw [Nat.mul_succ]
        omega
      _ ≤ Shape.size shape₂ * Shape.size shape₁ :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h₁)
      _ = Shape.size shape₁ * Shape.size shape₂ := by
        rw [Nat.mul_comm]
  { linear := linear
    idx := .prod out₁.idx out₂.idx
    valid :=
      { linear_lt := hlinear
        idx_inBounds := ⟨out₁.valid.idx_inBounds, out₂.valid.idx_inBounds⟩
        toFin_eq := by
          have h₁ : FinTIndex.equivFin shape₁
              ({ val := out₁.idx, isLt := out₁.valid.idx_inBounds } : FinTIndex shape₁) =
              ⟨out₁.linear, out₁.valid.linear_lt⟩ := by
            simpa [IndexType.toFin] using out₁.valid.toFin_eq
          have h₂ : FinTIndex.equivFin shape₂
              ({ val := out₂.idx, isLt := out₂.valid.idx_inBounds } : FinTIndex shape₂) =
              ⟨out₂.linear, out₂.valid.linear_lt⟩ := by
            simpa [IndexType.toFin] using out₂.valid.toFin_eq
          change FinTIndex.equivFin (.prod shape₁ shape₂)
              ({ val := .prod out₁.idx out₂.idx
                 isLt := ⟨out₁.valid.idx_inBounds, out₂.valid.idx_inBounds⟩ } :
                FinTIndex (.prod shape₁ shape₂)) =
              ⟨out₂.linear + Shape.size shape₂ * out₁.linear, hlinear⟩
          set_option backward.isDefEq.respectTransparency false in
            simp [FinTIndex.equivFin, FinTIndex.prodEquiv, finProdFinEquiv, h₁, h₂] } }

private theorem Output.idx_eq_fromFin {p : HRank} {shape : Shape p} (out : Output shape) :
    out.idx =
      (IndexType.fromFin (⟨out.linear, out.valid.linear_lt⟩ : Fin shape.size) :
        FinTIndex shape).val := by
  let idx : FinTIndex shape := ⟨out.idx, out.valid.idx_inBounds⟩
  have hidx : idx =
      (IndexType.fromFin (⟨out.linear, out.valid.linear_lt⟩ : Fin shape.size) :
        FinTIndex shape) := by
    calc
      idx = IndexType.fromFin (IndexType.toFin idx) := by
        exact (IndexType.fromFin_toFin idx).symm
      _ = IndexType.fromFin (⟨out.linear, out.valid.linear_lt⟩ : Fin shape.size) := by
        rw [out.valid.toFin_eq]
  exact congrArg FinTIndex.val hidx

private theorem map_add_mul_range (k i : Nat) :
    (List.range k).map (fun j => j + k * i) = List.range' (k * i) k := by
  rw [show (List.range k).map (fun j => j + k * i) =
      (List.range k).map (fun j => k * i + j) by
        apply List.map_congr_left
        intro j
        omega]
  simpa [List.range_eq_range'] using (List.map_add_range' (a := k * i) 0 k 1)

private def natRangeOutputs (stop i : Nat) : List { j // j < stop } :=
  if hi : i < stop then
    ⟨i, hi⟩ :: natRangeOutputs stop (i + 1)
  else
    []
termination_by stop - i
decreasing_by omega

private theorem natRangeOutputs_unattach_eq_range' (stop i : Nat) :
    (natRangeOutputs stop i).unattach = List.range' i (stop - i) := by
  rw [natRangeOutputs]
  split
  · rename_i hi
    change i :: (natRangeOutputs stop (i + 1)).unattach = List.range' i (stop - i)
    rw [natRangeOutputs_unattach_eq_range']
    rw [show stop - i = (stop - (i + 1)) + 1 by omega]
    rw [List.range'_succ]
  · rename_i hi
    have h : stop - i = 0 := by omega
    simp [h]
termination_by stop - i

private theorem natRangeOutputs_linears_eq_range' (stop i : Nat) :
    (natRangeOutputs stop i).map (fun j => j.1) = List.range' i (stop - i) := by
  change (natRangeOutputs stop i).unattach = List.range' i (stop - i)
  exact natRangeOutputs_unattach_eq_range' stop i

/-- Pure row-major arithmetic: nested `(i, j)` loops enumerate the flat range in order. -/
private theorem flatMap_range_product (n k : Nat) :
    (List.range n).flatMap (fun i => (List.range k).map (fun j => j + k * i)) =
      List.range (n * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [map_add_mul_range]
      rw [show List.range (n * k) = List.range' 0 (n * k) by rw [List.range_eq_range']]
      rw [show List.range ((n + 1) * k) = List.range' 0 ((n + 1) * k) by
        rw [List.range_eq_range']]
      rw [Nat.mul_comm k n]
      simpa [Nat.succ_mul] using (List.range'_append_1 (s := 0) (m := n * k) (n := k))

private def outputs : {p : HRank} → (shape : Shape p) → List (Output shape)
  | .leaf, .leaf n =>
      (natRangeOutputs n 0).map (leafOutput n)
  | .prod _ _, .prod shape₁ shape₂ =>
      (outputs shape₁).flatMap fun (out₁ : Output shape₁) =>
        (outputs shape₂).map fun (out₂ : Output shape₂) => prodOutput out₁ out₂

/-- The structural output list has exactly the flat row-major linear order. -/
private theorem outputs_linears_eq_range : {p : HRank} → (shape : Shape p) →
    (outputs shape).map Output.linear = List.range shape.size
  | .leaf, .leaf n => by
      unfold outputs
      simp only [Shape.size, List.map_map]
      change (natRangeOutputs n 0).map (fun j => j.1) = List.range n
      rw [natRangeOutputs_linears_eq_range']
      simp [List.range_eq_range']
  | .prod _ _, .prod shape₁ shape₂ => by
      unfold outputs
      simp only [Shape.size, List.map_flatMap, List.map_map]
      change
        ((outputs shape₁).flatMap fun (out₁ : Output shape₁) =>
          (outputs shape₂).map fun (out₂ : Output shape₂) =>
            out₂.linear + Shape.size shape₂ * out₁.linear) =
          List.range (Shape.size shape₁ * Shape.size shape₂)
      rw [← flatMap_range_product (Shape.size shape₁) (Shape.size shape₂)]
      rw [← outputs_linears_eq_range shape₁]
      rw [List.flatMap_map]
      congr 1
      funext out₁
      simpa [List.map_map, Function.comp_def] using
        congrArg (List.map (fun j => j + Shape.size shape₂ * out₁.linear))
          (outputs_linears_eq_range shape₂)

@[inline, specialize] private def listStepLoop {m : Type u → Type v} [Monad m]
    {α : Type w} {γ : Type u} : List α → (α → γ → m (ForInStep γ)) → γ → m (ForInStep γ)
  | [], _emit, acc => pure (.yield acc)
  | x :: xs, emit, acc => do
      let step ← emit x acc
      match step with
      | .done acc' => pure (.done acc')
      | .yield acc' => listStepLoop xs emit acc'

private theorem listStepLoop_map {m : Type u → Type v} [Monad m]
    {α : Type w} {β : Type x} {γ : Type u} (xs : List α) (f : α → β)
    (emit : β → γ → m (ForInStep γ)) (acc : γ) :
    listStepLoop (xs.map f) emit acc =
      listStepLoop xs (fun x acc => emit (f x) acc) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp [listStepLoop]
      apply bind_congr
      intro step
      cases step <;> simp [ih]

private theorem listStepLoop_congr {m : Type u → Type v} [Monad m]
    {α : Type w} {γ : Type u} (xs : List α)
    {emit emit' : α → γ → m (ForInStep γ)}
    (h : ∀ x acc, emit x acc = emit' x acc) (acc : γ) :
    listStepLoop xs emit acc = listStepLoop xs emit' acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp [listStepLoop, h]
      apply bind_congr
      intro step
      cases step <;> simp [ih]

private theorem call_eq_of_output_eq {β : Type w} {P : β → Prop} {δ : Type u}
    (f : (b : β) → P b → δ) {b b' : β} (hb : b = b')
    (h : P b) (h' : P b') :
    f b h = f b' h' := by
  subst hb
  congr

private theorem listStepLoop_append {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α : Type w} {γ : Type u} (xs ys : List α) (emit : α → γ → m (ForInStep γ))
    (acc : γ) :
    listStepLoop (xs ++ ys) emit acc = (do
      let step ← listStepLoop xs emit acc
      match step with
      | .done acc' => pure (.done acc')
      | .yield acc' => listStepLoop ys emit acc') := by
  induction xs generalizing acc with
  | nil => simp [listStepLoop]
  | cons x xs ih =>
      simp [listStepLoop]
      apply bind_congr
      intro step
      cases step <;> simp [ih]

private theorem listStepLoop_flatMap {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α : Type w} {β : Type x} {γ : Type u} (xs : List α) (f : α → List β)
    (emit : β → γ → m (ForInStep γ)) (acc : γ) :
    listStepLoop (xs.flatMap f) emit acc =
      listStepLoop xs (fun x acc => listStepLoop (f x) emit acc) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      rw [List.flatMap_cons, listStepLoop_append]
      simp [listStepLoop]
      apply bind_congr
      intro step
      cases step <;> simp [ih]

@[inline, specialize] private def rangeStepLoop {m : Type u → Type v} [Monad m]
    {γ : Type u} (stop : Nat)
    (emit : (i : Nat) → i < stop → γ → m (ForInStep γ))
    (i : Nat) (acc : γ) : m (ForInStep γ) := do
  if hi : i < stop then
    let step ← emit i hi acc
    match step with
    | .done acc' => pure (.done acc')
    | .yield acc' => rangeStepLoop stop emit (i + 1) acc'
  else
    pure (.yield acc)
termination_by stop - i
decreasing_by omega

private theorem rangeStepLoop_eq_listStepLoop {m : Type u → Type v} [Monad m]
    {γ : Type u} (stop : Nat)
    (emit : (i : Nat) → i < stop → γ → m (ForInStep γ))
    (i : Nat) (acc : γ) :
    rangeStepLoop stop emit i acc =
      listStepLoop (natRangeOutputs stop i) (fun j acc => emit j.1 j.2 acc) acc := by
  rw [rangeStepLoop, natRangeOutputs]
  by_cases hi : i < stop
  · simp only [dif_pos hi, listStepLoop]
    apply bind_congr
    intro step
    cases step with
    | done _ => rfl
    | yield acc' => exact rangeStepLoop_eq_listStepLoop stop emit (i + 1) acc'
  · simp [hi, listStepLoop]
termination_by stop - i
decreasing_by omega

private class NatConsumer (p : HRank) where
  consume {pOut : HRank} {shapeOut : Shape pOut}
    {m : Type u → Type v} [Monad m] {γ : Type u}
    {Pl : Nat × TIndex Nat pOut → γ → ForInStep γ → Prop}
    (it : IterM (α := RowMajorIterator shapeOut) Id (Nat × TIndex Nat pOut))
    (f : (b : Nat × TIndex Nat pOut) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c)))
    (shape : Shape p)
    (emit : (linear : Nat) → (idx : TIndex Nat p) →
      RowMajor.Valid shape (linear, idx) → γ → m (ForInStep γ)) :
      γ → m (ForInStep γ)

attribute [inline, specialize] NatConsumer.consume

@[inline] private instance : NatConsumer .leaf where
  consume {_pOut} {_shapeOut} {m} [Monad m] {_γ} {_Pl} _it _f shape emit acc :=
    match shape with
    | .leaf n =>
        rangeStepLoop n
          (fun i hi acc =>
            let out := leafOutput n ⟨i, hi⟩
            emit out.linear out.idx out.valid acc)
          0 acc

@[inline] private instance {p q : HRank} [NatConsumer p] [NatConsumer q] :
    NatConsumer (.prod p q) where
  consume {_pOut} {_shapeOut} {m} [Monad m] {_γ} {_Pl} it f shape emit acc :=
    match shape with
    | .prod shape₁ shape₂ =>
        let emitLeft (linear₁ : Nat) (idx₁ : TIndex Nat p)
            (hvalid₁ : RowMajor.Valid shape₁ (linear₁, idx₁))
            (acc : _γ) : m (ForInStep _γ) :=
          NatConsumer.consume (p := q) it f shape₂
            (fun linear₂ idx₂ hvalid₂ acc =>
              let out₁ : Output shape₁ := ⟨linear₁, idx₁, hvalid₁⟩
              let out₂ : Output shape₂ := ⟨linear₂, idx₂, hvalid₂⟩
              let out := prodOutput out₁ out₂
              emit out.linear out.idx out.valid acc)
            acc
        NatConsumer.consume (p := p) it f shape₁ emitLeft acc

@[inline, specialize] private def natConsume
    {pOut : HRank} {shapeOut : Shape pOut}
    {m : Type u → Type v} [Monad m]
    {γ : Type u} {Pl : Nat × TIndex Nat pOut → γ → ForInStep γ → Prop}
    (it : IterM (α := RowMajorIterator shapeOut) Id (Nat × TIndex Nat pOut))
    (f : (b : Nat × TIndex Nat pOut) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c))) :
    {p : HRank} → (shape : Shape p) →
      (emit : (linear : Nat) → (idx : TIndex Nat p) →
        RowMajor.Valid shape (linear, idx) → γ → m (ForInStep γ)) →
      γ → m (ForInStep γ)
  | .leaf, .leaf n, emit, acc =>
      rangeStepLoop n
        (fun i hi acc =>
          let out := leafOutput n ⟨i, hi⟩
          emit out.linear out.idx out.valid acc)
        0 acc
  | .prod _ _, .prod shape₁ shape₂, emit, acc =>
      let emitLeft (linear₁ : Nat) (idx₁ : TIndex Nat _)
          (hvalid₁ : RowMajor.Valid shape₁ (linear₁, idx₁))
          (acc : γ) : m (ForInStep γ) :=
        natConsume it f shape₂
          (fun linear₂ idx₂ hvalid₂ acc =>
            let out₁ : Output shape₁ := ⟨linear₁, idx₁, hvalid₁⟩
            let out₂ : Output shape₂ := ⟨linear₂, idx₂, hvalid₂⟩
            let out := prodOutput out₁ out₂
            emit out.linear out.idx out.valid acc)
          acc
      natConsume it f shape₁ emitLeft acc

private theorem natConsume_eq_outputs
    {pOut : HRank} {shapeOut : Shape pOut}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {γ : Type u} {Pl : Nat × TIndex Nat pOut → γ → ForInStep γ → Prop}
    (it : IterM (α := RowMajorIterator shapeOut) Id (Nat × TIndex Nat pOut))
    (f : (b : Nat × TIndex Nat pOut) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c))) :
    {p : HRank} → (shape : Shape p) →
      (emit : (linear : Nat) → (idx : TIndex Nat p) →
        RowMajor.Valid shape (linear, idx) → γ → m (ForInStep γ)) →
      (acc : γ) →
      natConsume it f shape emit acc =
        listStepLoop (outputs shape) (fun out acc => emit out.linear out.idx out.valid acc) acc
  | .leaf, .leaf n, emit, acc => by
      unfold outputs
      change
        rangeStepLoop n
            (fun i hi acc =>
              let out := leafOutput n ⟨i, hi⟩
              emit out.linear out.idx out.valid acc)
            0 acc =
          listStepLoop ((natRangeOutputs n 0).map (leafOutput n))
            (fun out acc => emit out.linear out.idx out.valid acc) acc
      rw [rangeStepLoop_eq_listStepLoop]
      rw [listStepLoop_map]
  | .prod _ _, .prod shape₁ shape₂, emit, acc => by
      change
        natConsume it f shape₁
            (fun linear₁ idx₁ hvalid₁ acc =>
              natConsume it f shape₂
                (fun linear₂ idx₂ hvalid₂ acc =>
                  let out₁ : Output shape₁ := ⟨linear₁, idx₁, hvalid₁⟩
                  let out₂ : Output shape₂ := ⟨linear₂, idx₂, hvalid₂⟩
                  let out := prodOutput out₁ out₂
                  emit out.linear out.idx out.valid acc)
                acc)
            acc =
          listStepLoop
            ((outputs shape₁).flatMap fun (out₁ : Output shape₁) =>
              (outputs shape₂).map fun (out₂ : Output shape₂) => prodOutput out₁ out₂)
            (fun out acc => emit out.linear out.idx out.valid acc) acc
      rw [natConsume_eq_outputs it f shape₁]
      rw [listStepLoop_flatMap]
      apply listStepLoop_congr
      intro out₁ acc
      rw [natConsume_eq_outputs it f shape₂]
      rw [listStepLoop_map]

theorem isPlausibleIndirectOutput_of_valid_of_le
    {it : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p)}
    {out : Nat × TIndex Nat p} (hvalid : RowMajor.Valid shape out)
    (hpos : it.internalState.pos ≤ out.1) : it.IsPlausibleIndirectOutput out := by
  by_cases hEq : it.internalState.pos = out.1
  · apply IterM.IsPlausibleIndirectOutput.direct
    refine ⟨⟨⟨it.internalState.pos + 1⟩⟩, ?_⟩
    exact ⟨hvalid, hEq.symm, rfl⟩
  · have hlt : it.internalState.pos < out.1 := Nat.lt_of_le_of_ne hpos hEq
    have hshape : it.internalState.pos < shape.size :=
      Nat.lt_of_lt_of_le hlt (Nat.le_of_lt hvalid.linear_lt)
    let linearIdx : Fin shape.size := ⟨it.internalState.pos, hshape⟩
    let idx : FinTIndex shape := IndexType.fromFin linearIdx
    let current : Nat × TIndex Nat p := (it.internalState.pos, idx.val)
    have hcurrent : RowMajor.Valid shape current :=
      { linear_lt := hshape
        idx_inBounds := idx.isLt
        toFin_eq := by
          change IndexType.toFin idx = linearIdx
          exact IndexType.toFin_fromFin linearIdx }
    let it' : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p) :=
      ⟨⟨it.internalState.pos + 1⟩⟩
    have hsucc : it'.IsPlausibleSuccessorOf it := by
      refine ⟨.yield it' current, rfl, ?_⟩
      exact ⟨hcurrent, rfl, rfl⟩
    exact IterM.IsPlausibleIndirectOutput.indirect hsucc
      (isPlausibleIndirectOutput_of_valid_of_le (it := it') hvalid (Nat.succ_le_of_lt hlt))
termination_by out.1 - it.internalState.pos
decreasing_by
  omega

@[inline, specialize] private def emitRowMajorOutput {p : HRank} {shape : Shape p}
    {m : Type u → Type v} [Monad m]
    {γ : Type u} {Pl : Nat × TIndex Nat p → γ → ForInStep γ → Prop}
    (it : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p))
    (f : (b : Nat × TIndex Nat p) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c)))
    (linear : Nat) (idx : TIndex Nat p) (hvalid : RowMajor.Valid shape (linear, idx))
    (acc : γ) : m (ForInStep γ) := do
  if hskip : linear < it.internalState.pos then
    pure (.yield acc)
  else
    let out : Nat × TIndex Nat p := (linear, idx)
    let hmem : it.IsPlausibleIndirectOutput out :=
      isPlausibleIndirectOutput_of_valid_of_le hvalid (Nat.le_of_not_gt hskip)
    let step ← f out hmem acc
    match step.1 with
    | .done acc' => pure (.done acc')
    | .yield acc' => pure (.yield acc')

@[inline, specialize] private def consumeFromIteratorState {p : HRank} {shape : Shape p}
    {m : Type u → Type v} [Monad m]
    {γ : Type u} {Pl : Nat × TIndex Nat p → γ → ForInStep γ → Prop}
    (it : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p))
    (f : (b : Nat × TIndex Nat p) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c)))
    (init : γ) : m γ := do
  if _hdone : shape.size ≤ it.internalState.pos then
    pure init
  else
    let step ← natConsume it f shape (emitRowMajorOutput it f) init
    match step with
    | .done acc => pure acc
    | .yield acc => pure acc

@[inline, specialize] private def consumeFromIteratorStateFast {p : HRank} {shape : Shape p}
    [NatConsumer p]
    {m : Type u → Type v} [Monad m]
    {γ : Type u} {Pl : Nat × TIndex Nat p → γ → ForInStep γ → Prop}
    (it : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p))
    (f : (b : Nat × TIndex Nat p) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c)))
    (init : γ) : m γ := do
  if _hdone : shape.size ≤ it.internalState.pos then
    pure init
  else
    let step ← NatConsumer.consume (p := p) it f shape (emitRowMajorOutput it f) init
    match step with
    | .done acc => pure acc
    | .yield acc => pure acc

private theorem listStepLoop_eq_default_of_zero {p : HRank} {shape : Shape p}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (lift : (γ' : Type) → (δ : Type u) → (γ' → m δ) → Id γ' → m δ)
    [Std.Internal.LawfulMonadLiftBindFunction lift]
    (γ : Type u)
    (Pl : Nat × TIndex Nat p → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded (RowMajorIterator shape) Id Pl)
    (it0 : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p))
    (hzero : it0.internalState.pos = 0)
    (f : (b : Nat × TIndex Nat p) → it0.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c))) :
    (xs : List (Output shape)) → (start : Nat) →
    (it : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p)) →
    xs.map Output.linear = List.range' start xs.length →
    start + xs.length = shape.size →
    it.internalState.pos = start →
    (hP : ∀ b, it.IsPlausibleIndirectOutput b → it0.IsPlausibleIndirectOutput b) →
    (init : γ) →
    (do
      let step ← listStepLoop xs
        (fun out acc => emitRowMajorOutput it0 f out.linear out.idx out.valid acc) init
      match step with
      | .done acc => pure acc
      | .yield acc => pure acc) =
      IterM.DefaultConsumers.forIn'.wf lift γ Pl wf it init
        it0.IsPlausibleIndirectOutput hP f
  | [], start, it, _hlinears, hsize, hpos, _hP, init => by
      have hstart : start = shape.size := by simpa using hsize
      have hdone : shape.size ≤ it.internalState.pos := by omega
      have hnot : ¬ it.internalState.pos < shape.size := by omega
      rw [IterM.DefaultConsumers.forIn'.wf]
      simp only [IterM.step_eq, Std.Internal.LawfulMonadLiftBindFunction.liftBind_pure,
        Shrink.inflate_deflate]
      simp [listStepLoop, hnot]
  | out :: xs, start, it, hlinears, hsize, hpos, hP, init => by
      rcases out with ⟨linear, rawIdx, hvalid⟩
      simp only [List.map_cons, List.length_cons] at hlinears hsize
      rw [List.range'_succ] at hlinears
      injection hlinears with hhead htail
      subst start
      have htailSize : linear + 1 + xs.length = shape.size := by omega
      have hlt : it.internalState.pos < shape.size := by omega
      have hnotSkip : ¬ linear < it0.internalState.pos := by omega
      have hidx : rawIdx =
          (IndexType.fromFin (⟨it.internalState.pos, hlt⟩ : Fin shape.size) :
            FinTIndex shape).val := by
        let out' : Output shape :=
          { linear := linear
            idx := rawIdx
            valid := hvalid }
        have hidx' := Output.idx_eq_fromFin out'
        have hfin : (⟨linear, hvalid.linear_lt⟩ : Fin shape.size) =
            ⟨it.internalState.pos, hlt⟩ := by
          apply Fin.ext
          simp [hhead]
        simpa [out', hfin] using hidx'
      subst rawIdx
      subst linear
      let linearIdx : Fin shape.size := ⟨it.internalState.pos, hlt⟩
      let idx : FinTIndex shape := IndexType.fromFin linearIdx
      let outDefault : Nat × TIndex Nat p := (it.internalState.pos, idx.val)
      have hvalidStep : RowMajor.Valid shape outDefault := by
        refine { linear_lt := hlt, idx_inBounds := idx.isLt, toFin_eq := ?_ }
        change IndexType.toFin idx = linearIdx
        exact IndexType.toFin_fromFin linearIdx
      have hsucc :
          (⟨⟨it.internalState.pos + 1⟩⟩ :
            IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p)).IsPlausibleSuccessorOf it := by
        refine ⟨.yield ⟨⟨it.internalState.pos + 1⟩⟩ outDefault, rfl, ?_⟩
        exact ⟨hvalidStep, rfl, rfl⟩
      rw [IterM.DefaultConsumers.forIn'.wf]
      simp only [IterM.step_eq, Std.Internal.LawfulMonadLiftBindFunction.liftBind_pure,
        Shrink.inflate_deflate]
      simp [listStepLoop, emitRowMajorOutput, RowMajorIterator.instIterator, hlt, hzero]
      apply bind_congr
      intro step
      cases step with
      | mk step hstep =>
          cases step with
          | done accDone =>
              simp
          | yield accYield =>
              simp
              simpa [emitRowMajorOutput, hzero] using
                listStepLoop_eq_default_of_zero lift γ Pl wf it0 hzero f xs
                  (it.internalState.pos + 1)
                  ⟨⟨it.internalState.pos + 1⟩⟩ htail htailSize rfl
                  (fun b hb => hP b (.indirect hsucc hb)) accYield

private theorem consumeFromIteratorState_eq_default_of_zero {p : HRank} {shape : Shape p}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (lift : (γ' : Type) → (δ : Type u) → (γ' → m δ) → Id γ' → m δ)
    [Std.Internal.LawfulMonadLiftBindFunction lift]
    (γ : Type u)
    (it : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p))
    (hzero : it.internalState.pos = 0)
    (init : γ)
    (Pl : Nat × TIndex Nat p → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded (RowMajorIterator shape) Id Pl)
    (f : (b : Nat × TIndex Nat p) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c))) :
    consumeFromIteratorState it f init =
      IterM.DefaultConsumers.forIn' lift γ Pl it init _ (fun _ => id) f := by
  rw [IterM.DefaultConsumers.forIn'_eq_wf Pl wf]
  by_cases hdone : shape.size ≤ it.internalState.pos
  · have hnot : ¬ it.internalState.pos < shape.size := by omega
    rw [consumeFromIteratorState]
    simp only [hdone, ↓reduceDIte]
    rw [IterM.DefaultConsumers.forIn'.wf]
    simp only [IterM.step_eq, Std.Internal.LawfulMonadLiftBindFunction.liftBind_pure,
      Shrink.inflate_deflate]
    simp [hnot]
  · have hlinearsRange := outputs_linears_eq_range shape
    have hlen : (outputs shape).length = shape.size := by
      have hlenMap := congrArg List.length hlinearsRange
      simpa using hlenMap
    have hlinears : (outputs shape).map Output.linear =
        List.range' 0 (outputs shape).length := by
      rw [hlinearsRange]
      rw [List.range_eq_range']
      simp [hlen]
    have hsize : 0 + (outputs shape).length = shape.size := by omega
    rw [consumeFromIteratorState]
    simp only [hdone, ↓reduceDIte]
    rw [natConsume_eq_outputs it f shape]
    exact listStepLoop_eq_default_of_zero lift γ Pl wf it hzero f (outputs shape) 0 it
      hlinears hsize hzero (fun _ h => h) init

@[inline, specialize] private def loopFromPos {p : HRank} {shape : Shape p}
    {m : Type u → Type v} [Monad m]
    {γ : Type u} {Pl : Nat × TIndex Nat p → γ → ForInStep γ → Prop}
    (it : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p))
    (init : γ)
    (f : (b : Nat × TIndex Nat p) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c))) : m γ := do
  if h : it.internalState.pos < shape.size then
    let linearIdx : Fin shape.size := ⟨it.internalState.pos, h⟩
    let idx : FinTIndex shape := IndexType.fromFin linearIdx
    let out : Nat × TIndex Nat p := (it.internalState.pos, idx.val)
    have hvalid : RowMajor.Valid shape out :=
      { linear_lt := h
        idx_inBounds := idx.isLt
        toFin_eq := by
          change IndexType.toFin idx = linearIdx
          exact IndexType.toFin_fromFin linearIdx }
    let it' : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p) :=
      ⟨⟨it.internalState.pos + 1⟩⟩
    have hdirect : it.IsPlausibleIndirectOutput out := by
      apply IterM.IsPlausibleIndirectOutput.direct
      refine ⟨it', ?_⟩
      exact ⟨hvalid, rfl, rfl⟩
    let step ← f out hdirect init
    match step.1 with
    | .done acc => pure acc
    | .yield acc =>
        have hsucc : it'.IsPlausibleSuccessorOf it := by
          refine ⟨.yield it' out, rfl, ?_⟩
          exact ⟨hvalid, rfl, rfl⟩
        loopFromPos it' acc (fun b hb c => f b (.indirect hsucc hb) c)
  else
    pure init
termination_by shape.size - it.internalState.pos
decreasing_by
  omega

@[inline, specialize] private def structuralLoop {p : HRank} {shape : Shape p}
    [NatConsumer p]
    {m : Type u → Type v} [Monad m]
    {γ : Type u} {Pl : Nat × TIndex Nat p → γ → ForInStep γ → Prop}
    (it : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p))
    (init : γ)
    (f : (b : Nat × TIndex Nat p) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c))) : m γ :=
  if _hzero : it.internalState.pos = 0 then
    consumeFromIteratorStateFast it f init
  else
    loopFromPos it init f

private theorem loopFromPos_eq_default {p : HRank} {shape : Shape p}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (lift : (γ' : Type) → (δ : Type u) → (γ' → m δ) → Id γ' → m δ)
    [Std.Internal.LawfulMonadLiftBindFunction lift]
    (γ : Type u)
    (it : IterM (α := RowMajorIterator shape) Id (Nat × TIndex Nat p))
    (init : γ)
    (Pl : Nat × TIndex Nat p → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded (RowMajorIterator shape) Id Pl)
    (f : (b : Nat × TIndex Nat p) → it.IsPlausibleIndirectOutput b →
      (c : γ) → m (Subtype (Pl b c))) :
    loopFromPos it init f =
      IterM.DefaultConsumers.forIn' lift γ Pl it init _ (fun _ => id) f := by
  rw [IterM.DefaultConsumers.forIn'_eq_wf Pl wf]
  fun_induction loopFromPos it init f
  case case1 it0 init0 f0 h linearIdx idx out hvalid itNext hdirect ih =>
    rw [IterM.DefaultConsumers.forIn'.wf]
    simp only [IterM.step_eq, Std.Internal.LawfulMonadLiftBindFunction.liftBind_pure,
      Shrink.inflate_deflate]
    simp [RowMajorIterator.instIterator, *]
    apply bind_congr
    intro step
    cases step with
    | mk step hstep =>
      cases step with
      | yield accYield =>
          simp only
          have hsucc : itNext.IsPlausibleSuccessorOf it0 := by
            refine ⟨.yield itNext out, rfl, ?_⟩
            exact ⟨hvalid, rfl, rfl⟩
          exact
            calc
              IterM.DefaultConsumers.forIn'.wf lift γ Pl wf itNext accYield itNext.IsPlausibleIndirectOutput
                  (fun _ h => h)
                  (fun b hb c => f0 b (.indirect hsucc hb) c)
                  = IterM.DefaultConsumers.forIn' lift γ Pl itNext accYield itNext.IsPlausibleIndirectOutput
                      (fun _ h => h)
                      (fun b hb c => f0 b (.indirect hsucc hb) c) := by
                    exact (IterM.DefaultConsumers.forIn'_eq_wf (lift := lift) (it := itNext)
                      (init := accYield) (P := itNext.IsPlausibleIndirectOutput)
                      (hP := fun _ h => h) Pl wf
                      (fun b hb c => f0 b (.indirect hsucc hb) c)).symm
              _ = IterM.DefaultConsumers.forIn' lift γ Pl itNext accYield it0.IsPlausibleIndirectOutput
                      (fun _ h => .indirect hsucc h) f0 := by
                    apply IterM.DefaultConsumers.forIn'_eq_forIn' Pl wf
                    intro b c hP hQ
                    congr 1
              _ = IterM.DefaultConsumers.forIn'.wf lift γ Pl wf itNext accYield it0.IsPlausibleIndirectOutput
                      (fun _ h => .indirect hsucc h) f0 := by
                    exact IterM.DefaultConsumers.forIn'_eq_wf (lift := lift) (it := itNext)
                      (init := accYield) (P := it0.IsPlausibleIndirectOutput)
                      (hP := fun _ h => .indirect hsucc h) Pl wf f0
      | done _ =>
          simp only
  case case2 it0 init0 f0 h =>
    rw [IterM.DefaultConsumers.forIn'.wf]
    simp only [IterM.step_eq, Std.Internal.LawfulMonadLiftBindFunction.liftBind_pure,
      Shrink.inflate_deflate]
    simp [*]

@[inline, specialize]
instance (priority := 1100) instIteratorLoop {m : Type u → Type v} [Monad m] [NatConsumer p] :
    IteratorLoop (RowMajorIterator shape) Id m where
  forIn _lift _γ _Pl it init f :=
    structuralLoop it init f

@[always_inline, inline]
instance (priority := 100) instIteratorLoopDefault {m : Type u → Type v} [Monad m] :
    IteratorLoop (RowMajorIterator shape) Id m :=
  .defaultImplementation

end RowMajorIterator

instance instForInRowMajorIter {p : HRank} {shape : Shape p}
    {m : Type u → Type v} [Monad m] [IteratorLoop (RowMajorIterator shape) Id m] :
    ForIn' m (Iter (α := RowMajorIterator shape) (Nat × TIndex Nat p)) (Nat × TIndex Nat p)
      inferInstance where
  forIn' it init f :=
    (Std.Iter.instForIn' (α := RowMajorIterator shape) (β := Nat × TIndex Nat p) (n := m)).forIn'
      it init fun out h acc => f out (RowMajorIterator.valid_of_isPlausibleIndirectOutput h) acc

end FinTIndex

end TensorIndex

end NumLean
