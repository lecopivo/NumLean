import NumLean.Data.TensorIndex.Basic
import NumLean.Data.HTuple.RangeIterator

namespace NumLean

namespace TensorIndex

namespace HTupleRange

@[simp] theorem card_zero_shape {p : HRank} (shape : Shape p) :
    HTuple.Range.card 0 shape = Shape.size shape := by
  induction p with
  | leaf => cases shape; rfl
  | prod p q hp hq =>
      cases shape with
      | prod shape₀ shape₁ => simp [hp, hq]

theorem length_toList_zero_shape {p : HRank} (shape : Shape p) :
    (HTuple.Range.toList 0 shape).length = Shape.size shape := by
  rw [HTuple.Range.length_toList, card_zero_shape]

theorem valid_zero_shape_iff_inBounds {p : HRank}
    {shape : Shape p} {idx : TIndex Nat p} :
    idx ∈ ((0 : HTuple Nat p)...shape) ↔ TIndex.InBounds shape idx := by
  induction p with
  | leaf =>
      cases shape with | leaf dim =>
      cases idx with | leaf i =>
      rw [HTuple.Range.mem_iff_Valid]
      change (0 ≤ i ∧ i < dim) ↔ i < dim
      omega
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases idx with | prod idx₀ idx₁ =>
      rw [HTuple.Range.mem_iff_Valid, HTuple.zero_prod]
      change (HTuple.Range.Valid (0 : HTuple Nat p) shape₀ idx₀ ∧
          HTuple.Range.Valid (0 : HTuple Nat q) shape₁ idx₁) ↔
        TIndex.InBounds shape₀ idx₀ ∧ TIndex.InBounds shape₁ idx₁
      rw [← HTuple.Range.mem_iff_Valid, ← HTuple.Range.mem_iff_Valid, hp, hq]

theorem enum_valid_zero_shape {p : HRank} {shape : Shape p}
    {out : Nat × TIndex Nat p}
    (h : out ∈ (HTuple.Range.Enum.mk ((0 : HTuple Nat p)...shape) : HTuple.Range.Enum p)) :
    TIndex.InBounds shape out.2 ∧
      out.1 = HTuple.Range.linearIndex (0 : HTuple Nat p) shape out.2 := by
  exact ⟨valid_zero_shape_iff_inBounds.mp h.1, h.2⟩

end HTupleRange

end TensorIndex

end NumLean
