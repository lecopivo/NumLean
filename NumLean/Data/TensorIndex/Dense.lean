import NumLean.Data.TensorIndex.Monotone

open scoped BigOperators

namespace NumLean
namespace TensorIndex

private def denseOffset {rank : Nat} (dims idx : Vector Nat rank) : Nat :=
  ∑ i : Fin rank, idx[i] * (∏ j : Fin rank, if i < j then dims[j] else 1)

private theorem denseOffset_decomp {n : Nat} (dims idx : Vector Nat (n + 1)) :
    denseOffset dims idx =
      idx[0] * (∏ j : Fin n, dims[j.succ]) +
      denseOffset (Vector.ofFn fun j : Fin n => dims[j.succ])
        (Vector.ofFn fun j : Fin n => idx[j.succ]) := by
  unfold denseOffset
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.getElem_fin, Fin.val_succ, Vector.getElem_ofFn, mul_eq_mul_left_iff]
    left
    rw [Fin.prod_univ_succ]
    simp

private theorem numel_decomp {n : Nat} (dims : Vector Nat (n + 1)) :
    numel dims = dims[0] * numel (Vector.ofFn fun j : Fin n => dims[j.succ]) := by
  unfold numel
  rw [Fin.prod_univ_succ]
  simp

private theorem inBounds_tail {n : Nat} {dims idx : Vector Nat (n + 1)}
    (h : InBounds idx dims) :
    InBounds (Vector.ofFn fun j : Fin n => idx[j.succ])
      (Vector.ofFn fun j : Fin n => dims[j.succ]) := by
  intro j
  simpa using h j.succ

private theorem numel_pos_of_inBounds {rank : Nat} {dims idx : Vector Nat rank}
    (h : InBounds idx dims) : 0 < numel dims := by
  induction rank with
  | zero => simp [numel]
  | succ n ih =>
      rw [numel_decomp]
      have h0lt := h (0 : Fin (n + 1))
      have h0 : 0 < dims[0] := Nat.lt_of_le_of_lt (Nat.zero_le _) h0lt
      have ht := ih (inBounds_tail h)
      exact Nat.mul_pos h0 ht

private theorem denseOffset_lt_numel {rank : Nat} {dims idx : Vector Nat rank}
    (h : InBounds idx dims) : denseOffset dims idx < numel dims := by
  induction rank with
  | zero => simp [denseOffset, numel]
  | succ n ih =>
      rw [denseOffset_decomp, numel_decomp]
      have htBound := inBounds_tail h
      have ht := ih htBound
      have hprodEq : (∏ j : Fin n, dims[j.succ]) =
          numel (Vector.ofFn fun j : Fin n => dims[j.succ]) := by
        unfold numel
        simp
      rw [hprodEq]
      have h0 := h (0 : Fin (n + 1))
      calc
        idx[0] * numel (Vector.ofFn fun j : Fin n => dims[j.succ])
            + denseOffset (Vector.ofFn fun j : Fin n => dims[j.succ])
                (Vector.ofFn fun j : Fin n => idx[j.succ])
            < idx[0] * numel (Vector.ofFn fun j : Fin n => dims[j.succ])
              + numel (Vector.ofFn fun j : Fin n => dims[j.succ]) :=
                Nat.add_lt_add_left ht _
        _ = (idx[0] + 1) * numel (Vector.ofFn fun j : Fin n => dims[j.succ]) := by ring
        _ ≤ dims[0] * numel (Vector.ofFn fun j : Fin n => dims[j.succ]) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h0)

private theorem denseOffset_inj {rank : Nat} {dims idx idx' : Vector Nat rank}
    (h : InBounds idx dims) (h' : InBounds idx' dims)
    (hoff : denseOffset dims idx = denseOffset dims idx') : idx = idx' := by
  induction rank with
  | zero =>
      apply Vector.ext
      intro i hi
      omega
  | succ n ih =>
      let tdims := Vector.ofFn fun j : Fin n => dims[j.succ]
      let tidx := Vector.ofFn fun j : Fin n => idx[j.succ]
      let tidx' := Vector.ofFn fun j : Fin n => idx'[j.succ]
      have hdecomp := denseOffset_decomp dims idx
      have hdecomp' := denseOffset_decomp dims idx'
      have hprodEq : (∏ j : Fin n, dims[j.succ]) = numel tdims := by
        unfold tdims numel
        simp
      have ht : denseOffset tdims tidx < numel tdims := by
        exact denseOffset_lt_numel (inBounds_tail h)
      have ht' : denseOffset tdims tidx' < numel tdims := by
        exact denseOffset_lt_numel (inBounds_tail h')
      have hpos : 0 < numel tdims := numel_pos_of_inBounds (inBounds_tail h)
      have heq : idx[0] * numel tdims + denseOffset tdims tidx =
          idx'[0] * numel tdims + denseOffset tdims tidx' := by
        rw [← hprodEq]
        rw [← hdecomp, ← hdecomp']
        exact hoff
      have hdiv := congrArg (fun x => x / numel tdims) heq
      have hhead : idx[0] = idx'[0] := by
        have lhs : (idx[0] * numel tdims + denseOffset tdims tidx) / numel tdims = idx[0] := by
          rw [Nat.mul_comm]
          rw [Nat.mul_add_div hpos]
          simp [Nat.div_eq_of_lt ht]
        have rhs : (idx'[0] * numel tdims + denseOffset tdims tidx') / numel tdims = idx'[0] := by
          rw [Nat.mul_comm]
          rw [Nat.mul_add_div hpos]
          simp [Nat.div_eq_of_lt ht']
        simpa [lhs, rhs] using hdiv
      have htailEq : denseOffset tdims tidx = denseOffset tdims tidx' := by
        rw [hhead] at heq
        exact Nat.add_left_cancel heq
      have htailVec := ih (inBounds_tail h) (inBounds_tail h') htailEq
      apply Vector.ext
      intro k hk
      cases k with
      | zero => simpa using hhead
      | succ k =>
          have := congrArg (fun v : Vector Nat n => v[k]) htailVec
          simpa [tidx, tidx'] using this

private theorem offsetOf_denseStridesForOrder_eq_denseOffset {rank : Nat}
    (dims idx : Vector Nat rank) (order : AxisOrder rank) :
    offsetOf (denseStridesForOrder dims order) idx =
      denseOffset (Vector.ofFn fun i : Fin rank => dims[order i])
        (Vector.ofFn fun i : Fin rank => idx[order i]) := by
  rw [offsetOf_eq_orderedOffset order]
  unfold orderedOffset denseOffset denseStridesForOrder
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- Dense strides for any axis order are valid: the offset map is injective on bounded tensor
indices. -/
theorem validStrides_denseStridesForOrder {rank : Nat}
    (dims : Vector Nat rank) (order : AxisOrder rank) :
    ValidStrides dims (denseStridesForOrder dims order) := by
  intro idx idx' hoff
  have hbound : InBounds (Vector.ofFn fun i : Fin rank => idx.val[order i])
      (Vector.ofFn fun i : Fin rank => dims[order i]) := by
    intro i
    simpa using idx.valid (order i)
  have hbound' : InBounds (Vector.ofFn fun i : Fin rank => idx'.val[order i])
      (Vector.ofFn fun i : Fin rank => dims[order i]) := by
    intro i
    simpa using idx'.valid (order i)
  have hoff' :
      denseOffset (Vector.ofFn fun i : Fin rank => dims[order i])
          (Vector.ofFn fun i : Fin rank => idx.val[order i]) =
        denseOffset (Vector.ofFn fun i : Fin rank => dims[order i])
          (Vector.ofFn fun i : Fin rank => idx'.val[order i]) := by
    simpa [offset] using
      (offsetOf_denseStridesForOrder_eq_denseOffset dims idx.val order ▸
        offsetOf_denseStridesForOrder_eq_denseOffset dims idx'.val order ▸ hoff)
  have hordered := denseOffset_inj hbound hbound' hoff'
  have hval : idx.val = idx'.val := by
    apply Vector.ext
    intro axis haxis
    let axis' : Fin rank := ⟨axis, haxis⟩
    have hget := congrArg (fun v : Vector Nat rank => v[order.symm axis']) hordered
    simpa [axis'] using hget
  cases idx
  cases idx'
  subst hval
  rfl

/-- Dense offsets are always within the tensor's flat element count. -/
theorem offset_denseStridesForOrder_lt_numel {rank : Nat}
    {dims : Vector Nat rank} (order : AxisOrder rank) (idx : TensorIndex dims) :
    idx.offset (denseStridesForOrder dims order) < numel dims := by
  have hbound : InBounds (Vector.ofFn fun i : Fin rank => idx.val[order i])
      (Vector.ofFn fun i : Fin rank => dims[order i]) := by
    intro i
    simpa using idx.valid (order i)
  have hnumel : numel (Vector.ofFn fun i : Fin rank => dims[order i]) = numel dims := by
    unfold numel
    simpa using (Equiv.prod_comp order (fun i : Fin rank => dims[i]))
  simpa [offset, offsetOf_denseStridesForOrder_eq_denseOffset dims idx.val order] using
    (hnumel ▸ denseOffset_lt_numel hbound)

theorem validStrides_colMajorStrides {rank : Nat} (dims : Vector Nat rank) :
    ValidStrides dims (colMajorStrides dims) := by
  simpa [colMajorStrides] using
    validStrides_denseStridesForOrder dims (colMajorAxisOrder rank)

theorem validStrides_rowMajorStrides {rank : Nat} (dims : Vector Nat rank) :
    ValidStrides dims (rowMajorStrides dims) := by
  simpa [rowMajorStrides] using
    validStrides_denseStridesForOrder dims (rowMajorAxisOrder rank)

end TensorIndex
end NumLean
