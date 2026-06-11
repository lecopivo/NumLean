import NumLean.Data.TensorIndex.Basic

open scoped BigOperators

namespace NumLean
namespace TensorIndex

/-- `order` is sorted by decreasing stride magnitude.

The permutation maps significance positions to tensor axes: `order 0` is the most significant
axis, `order 1` is next, and so on. -/
def IsStrideOrder {r : Nat} (strides : Vector Nat r) (order : AxisOrder r) : Prop :=
  ∀ i j : Fin r, i.1 < j.1 → strides[order j] ≤ strides[order i]

instance {r : Nat} (strides : Vector Nat r) (order : AxisOrder r) :
    Decidable (IsStrideOrder strides order) := by
  unfold IsStrideOrder
  exact Fintype.decidableForallFintype

/-- An axis order sorted by decreasing stride magnitude. -/
abbrev StrideOrder {r : Nat} (strides : Vector Nat r) :=
  { order : AxisOrder r // IsStrideOrder strides order }

/-- Lexicographic order on tensor indices using an explicit axis significance order.

The first differing component is chosen by `order`: compare `order 0`, then `order 1`, etc. -/
def LexLt {r : Nat} (order : AxisOrder r) (idx idx' : Vector Nat r) : Prop :=
  ∃ i : Fin r,
    (∀ j : Fin r, j.1 < i.1 → idx[order j] = idx'[order j]) ∧
      idx[order i] < idx'[order i]

/-- A stride layout whose flat offsets strictly increase in lexicographic tensor-index order. -/
def IncreasingOffsets {r : Nat} (dims stride : Vector Nat r) (order : AxisOrder r) : Prop :=
  ∀ idx idx' : TensorIndex dims,
    LexLt order idx.val idx'.val → offset idx stride < offset idx' stride

/-- Maximum flat-offset variation contributed by axes less significant than position `i`.

If the index at position `i` increases by one, its stride must be larger than this span to ensure
that lexicographic order also increases flat offsets. -/
def lessSignificantSpan {r : Nat} (dims strides : Vector Nat r) (order : AxisOrder r)
    (i : Fin r) : Nat :=
  ∑ j : Fin r, if i.1 < j.1 then (dims[order j] - 1) * strides[order j] else 0

/-- Minimum stride needed at position `i` to jump over all less-significant axes. -/
def requiredStride {r : Nat} (dims strides : Vector Nat r) (order : AxisOrder r)
    (i : Fin r) : Nat :=
  lessSignificantSpan dims strides order i + 1

/-- Arithmetic monotonicity condition for a concrete axis order.

The order must be sorted by decreasing stride, and each stride must jump over the full possible
span of all less-significant axes. -/
def MonotonicStridesForOrder {r : Nat} (dims strides : Vector Nat r)
    (order : AxisOrder r) : Prop :=
  IsStrideOrder strides order ∧
    ∀ i : Fin r, requiredStride dims strides order i ≤ strides[order i]

instance {r : Nat} (dims strides : Vector Nat r) (order : AxisOrder r) :
    Decidable (MonotonicStridesForOrder dims strides order) := by
  unfold MonotonicStridesForOrder
  infer_instance

/-- A stride layout is monotonic when some stride-sorted axis order satisfies the arithmetic gap
condition. This condition is finite and decidable. -/
def MonotonicStrides {r : Nat} (dims strides : Vector Nat r) : Prop :=
  ∃ order : AxisOrder r, MonotonicStridesForOrder dims strides order

instance {r : Nat} (dims strides : Vector Nat r) : Decidable (MonotonicStrides dims strides) :=
  Fintype.decidableExistsFintype

/-- The arithmetic stride-gap condition is sufficient for lexicographic traversal to increase
flat offsets. -/
theorem increasingOffsets_of_monotonicStridesForOrder {r : Nat}
    {dims strides : Vector Nat r} {order : AxisOrder r}
    (h : MonotonicStridesForOrder dims strides order) :
    IncreasingOffsets dims strides order := by
  intro idx idx' hlex
  rcases hlex with ⟨i, hprefix, hpivot⟩
  have hupper :
        orderedOffset order strides idx.val ≤
        (∑ j : Fin r,
          if j < i then idx.val[order j] * strides[order j] else 0)
        + idx.val[order i] * strides[order i]
        + lessSignificantSpan dims strides order i := by
    have hupperRaw :
        orderedOffset order strides idx.val ≤
          (∑ j : Fin r,
            ((if j < i then idx.val[order j] * strides[order j] else 0) +
            (if j = i then idx.val[order i] * strides[order i] else 0) +
            (if i < j then (dims[order j] - 1) * strides[order j] else 0))) := by
      unfold orderedOffset
      apply Finset.sum_le_sum
      intro j _
      by_cases hlt : j < i
      · have hne : j ≠ i := by
          intro hji
          subst hji
          omega
        have hnlt : ¬ i < j := by omega
        simp [hlt, hne, hnlt]
      · by_cases heq : j = i
        · simp [heq]
        · have hgt : i < j := by
            have hne : j.val ≠ i.val := by
              intro hval
              apply heq
              exact Fin.ext hval
            omega
          have hidxle : idx.val[order j] ≤ dims[order j] - 1 :=
            Nat.le_sub_one_of_lt (idx.valid (order j))
          have hmul : idx.val[order j] * strides[order j] ≤
              (dims[order j] - 1) * strides[order j] :=
            Nat.mul_le_mul_right (strides[order j]) hidxle
          simpa [hlt, heq, hgt] using hmul
    calc
      orderedOffset order strides idx.val ≤ _ := hupperRaw
      _ = (∑ j : Fin r, if j < i then idx.val[order j] * strides[order j] else 0)
          + idx.val[order i] * strides[order i]
          + lessSignificantSpan dims strides order i := by
            simp [Finset.sum_add_distrib, lessSignificantSpan, Nat.add_assoc]
  have hlower :
      (∑ j : Fin r,
        if j < i then idx'.val[order j] * strides[order j] else 0)
      + idx'.val[order i] * strides[order i]
      ≤ orderedOffset order strides idx'.val := by
    have hlowerRaw :
        (∑ j : Fin r,
          ((if j < i then idx'.val[order j] * strides[order j] else 0) +
          (if j = i then idx'.val[order i] * strides[order i] else 0)))
        ≤ orderedOffset order strides idx'.val := by
      unfold orderedOffset
      apply Finset.sum_le_sum
      intro j _
      by_cases hlt : j < i
      · have hne : j ≠ i := by
          intro hji
          subst hji
          omega
        simp [hlt, hne]
      · by_cases heq : j = i
        · simp [heq]
        · simp [hlt, heq]
    calc
      (∑ j : Fin r, if j < i then idx'.val[order j] * strides[order j] else 0)
          + idx'.val[order i] * strides[order i]
        = (∑ j : Fin r,
            ((if j < i then idx'.val[order j] * strides[order j] else 0) +
            (if j = i then idx'.val[order i] * strides[order i] else 0))) := by
            simp [Finset.sum_add_distrib]
      _ ≤ orderedOffset order strides idx'.val := hlowerRaw
  have hprefixSum :
      (∑ j : Fin r, if j < i then idx.val[order j] * strides[order j] else 0) =
      (∑ j : Fin r, if j < i then idx'.val[order j] * strides[order j] else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hlt : j < i
    · simp [hlt, hprefix j hlt]
    · simp [hlt]
  have hpivotGap :
      idx.val[order i] * strides[order i] + lessSignificantSpan dims strides order i <
        idx'.val[order i] * strides[order i] := by
    have hspan : lessSignificantSpan dims strides order i < strides[order i] := by
      have hreq := h.2 i
      simp [requiredStride] at hreq
      omega
    have hidx : idx.val[order i] + 1 ≤ idx'.val[order i] := Nat.succ_le_of_lt hpivot
    have hmul : (idx.val[order i] + 1) * strides[order i] ≤
        idx'.val[order i] * strides[order i] :=
      Nat.mul_le_mul_right (strides[order i]) hidx
    calc
      idx.val[order i] * strides[order i] + lessSignificantSpan dims strides order i
          < idx.val[order i] * strides[order i] + strides[order i] :=
            Nat.add_lt_add_left hspan _
      _ = (idx.val[order i] + 1) * strides[order i] := by ring
      _ ≤ idx'.val[order i] * strides[order i] := hmul
  have hupper' :
      orderedOffset order strides idx.val ≤
        (∑ j : Fin r, if j < i then idx'.val[order j] * strides[order j] else 0)
        + idx.val[order i] * strides[order i]
        + lessSignificantSpan dims strides order i := by
    simpa using (hprefixSum ▸ hupper)
  have hgap :
      (∑ j : Fin r, if j < i then idx'.val[order j] * strides[order j] else 0)
        + idx.val[order i] * strides[order i]
        + lessSignificantSpan dims strides order i
      < (∑ j : Fin r, if j < i then idx'.val[order j] * strides[order j] else 0)
        + idx'.val[order i] * strides[order i] := by
    omega
  have hordered : orderedOffset order strides idx.val < orderedOffset order strides idx'.val :=
    Nat.lt_of_le_of_lt hupper' (Nat.lt_of_lt_of_le hgap hlower)
  simpa [offset, offsetOf_eq_orderedOffset order] using hordered

/-- Strictly increasing offsets in a total lexicographic traversal imply offset injectivity. -/
theorem validStrides_of_increasingOffsets {r : Nat}
    {dims strides : Vector Nat r} {order : AxisOrder r}
    (h : IncreasingOffsets dims strides order) :
    ValidStrides dims strides := by
  intro idx idx' hoff
  by_cases hval : idx.val = idx'.val
  · cases idx
    cases idx'
    subst hval
    rfl
  · classical
    let s : Finset (Fin r) := Finset.univ.filter fun i => idx.val[order i] ≠ idx'.val[order i]
    have hs : s.Nonempty := by
      rw [Finset.filter_nonempty_iff]
      by_contra hnone
      push_neg at hnone
      apply hval
      apply Vector.ext
      intro axis haxislt
      let axis' : Fin r := ⟨axis, haxislt⟩
      have haxis := hnone (order.symm axis') (by simp)
      simpa [axis'] using haxis
    rcases Finset.exists_min_image s (fun i : Fin r => i.1) hs with ⟨i, hi_mem, hmin⟩
    have hidiff : idx.val[order i] ≠ idx'.val[order i] := (Finset.mem_filter.mp hi_mem).2
    have hprefix : ∀ j : Fin r, j.1 < i.1 → idx.val[order j] = idx'.val[order j] := by
      intro j hj
      by_contra hneq
      have hjmem : j ∈ s := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hneq⟩
      have hle := hmin j hjmem
      omega
    have hidxlt_or : idx.val[order i] < idx'.val[order i] ∨
        idx'.val[order i] < idx.val[order i] := Nat.lt_or_gt_of_ne hidiff
    rcases hidxlt_or with hlt | hgt
    · have hlex : LexLt order idx.val idx'.val := ⟨i, hprefix, hlt⟩
      have hltOff := h idx idx' hlex
      exact False.elim ((ne_of_lt hltOff) hoff)
    · have hprefix' : ∀ j : Fin r, j.1 < i.1 → idx'.val[order j] = idx.val[order j] := by
        intro j hj
        exact (hprefix j hj).symm
      have hlex : LexLt order idx'.val idx.val := ⟨i, hprefix', hgt⟩
      have hltOff := h idx' idx hlex
      exact False.elim ((ne_of_lt hltOff) hoff.symm)

end TensorIndex
end NumLean
