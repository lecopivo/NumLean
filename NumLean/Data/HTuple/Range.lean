module

public import NumLean.Data.HTuple.Order

@[expose] public section

namespace NumLean

namespace HTuple

private theorem sub_zero_nat {p : Profile} (x : HTuple Nat p) : x - 0 = x := by
  induction p with
  | leaf =>
      cases x with | leaf x => simp
  | prod p q hp hq =>
      cases x with | prod x₀ x₁ =>
      simp [hp, hq]

namespace Range

/-- Pointwise membership for half-open hierarchical tuple ranges. -/
@[inline] def Valid {α : Type u} [LE α] [LT α] : {p : Profile} →
    HTuple α p → HTuple α p → HTuple α p → Prop
  | .leaf, .leaf lo, .leaf hi, .leaf idx => idx ∈ (lo...hi)
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁, .prod idx₀ idx₁ =>
      Valid lo₀ hi₀ idx₀ ∧ Valid lo₁ hi₁ idx₁

theorem valid_iff_le_lt {p : Profile} [LE α] [LT α]
    {lo hi idx : HTuple α p} :
    Valid lo hi idx ↔ lo ≤ₑ idx ∧ idx <ₑ hi := by
  induction p with
  | leaf =>
      cases lo with | leaf lo =>
      cases hi with | leaf hi =>
      cases idx with | leaf idx =>
      rw [HTuple.elementwiseLE_leaf, HTuple.elementwiseLT_leaf]
      change (idx ∈ (lo...hi)) ↔ lo ≤ idx ∧ idx < hi
      exact Std.Rco.mem_iff
  | prod p q hp hq =>
      cases lo with | prod lo₀ lo₁ =>
      cases hi with | prod hi₀ hi₁ =>
      cases idx with | prod idx₀ idx₁ =>
      change (Valid lo₀ hi₀ idx₀ ∧ Valid lo₁ hi₁ idx₁) ↔
        (.prod lo₀ lo₁ : HTuple α (.prod p q)) ≤ₑ .prod idx₀ idx₁ ∧
          (.prod idx₀ idx₁ : HTuple α (.prod p q)) <ₑ .prod hi₀ hi₁
      rw [hp, hq, HTuple.elementwiseLE_prod, HTuple.elementwiseLT_prod]
      tauto

theorem mem_iff_Valid {p : Profile} [LE α] [LT α]
    {idx : HTuple α p} {lo hi : HTuple α p} :
    idx ∈ (lo...hi) ↔ Valid lo hi idx := by
  rw [mem_iff_le_lt, valid_iff_le_lt]

/-- Cardinality of a half-open natural tuple range. -/
@[inline] def card : {p : Profile} → HTuple Nat p → HTuple Nat p → Nat
  | _, lo, hi => (hi - lo).numel

/-- Row-major linear index inside a natural tuple range, with the rightmost coordinate fastest. -/
@[inline] def linearIndex : {p : Profile} → HTuple Nat p → HTuple Nat p → HTuple Nat p → Nat
  | _, lo, hi, idx => (idx - lo).rowMajorIndex (hi - lo)

/-- Structural list specification for natural tuple ranges, in row-major order. -/
@[inline] def toList : {p : Profile} → HTuple Nat p → HTuple Nat p → List (HTuple Nat p)
  | .leaf, .leaf lo, .leaf hi => (List.range' lo (hi - lo)).map HTuple.leaf
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁ =>
      (toList lo₀ hi₀).flatMap fun idx₀ =>
        (toList lo₁ hi₁).map fun idx₁ => HTuple.prod idx₀ idx₁

@[simp] theorem card_leaf (lo hi : Nat) : card (.leaf lo) (.leaf hi) = hi - lo := rfl

@[simp] theorem card_prod {p q : Profile}
    (lo₀ hi₀ : HTuple Nat p) (lo₁ hi₁ : HTuple Nat q) :
    card (.prod lo₀ lo₁) (.prod hi₀ hi₁) = card lo₀ hi₀ * card lo₁ hi₁ := rfl

@[simp] theorem toList_leaf (lo hi : Nat) :
    toList (.leaf lo) (.leaf hi) = (List.range' lo (hi - lo)).map HTuple.leaf := rfl

@[simp] theorem toList_prod {p q : Profile}
    (lo₀ hi₀ : HTuple Nat p) (lo₁ hi₁ : HTuple Nat q) :
    toList (.prod lo₀ lo₁) (.prod hi₀ hi₁) =
      (toList lo₀ hi₀).flatMap fun idx₀ =>
        (toList lo₁ hi₁).map fun idx₁ => HTuple.prod idx₀ idx₁ := rfl

theorem linearIndex_zero {p : Profile} (shape idx : HTuple Nat p) :
    linearIndex 0 shape idx = idx.rowMajorIndex shape := by
  induction p with
  | leaf =>
      cases shape with | leaf shape =>
      cases idx with | leaf idx =>
      simp [linearIndex, HTuple.rowMajorIndex]
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases idx with | prod idx₀ idx₁ =>
      simp [linearIndex, HTuple.rowMajorIndex, sub_zero_nat]

theorem length_toList : {p : Profile} → (lo hi : HTuple Nat p) →
    (toList lo hi).length = card lo hi
  | .leaf, .leaf lo, .leaf hi => by simp
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁ => by
      simp [length_toList lo₀ hi₀, length_toList lo₁ hi₁]

/-- Membership in the list specification implies membership in the corresponding tuple range. -/
theorem mem_of_mem_toList {p : Profile} {lo hi idx : HTuple Nat p}
    (h : idx ∈ toList lo hi) : idx ∈ (lo...hi) := by
  induction p with
  | leaf =>
      cases lo with | leaf lo =>
      cases hi with | leaf hi =>
      cases idx with | leaf idx =>
      simp [toList] at h
      rw [HTuple.Range.mem_iff_Valid]
      change idx ∈ (lo...hi)
      rw [Std.Rco.mem_iff]
      constructor
      · exact h.1
      · by_cases hlohi : lo ≤ hi
        · have hsum : lo + (hi - lo) = hi := Nat.add_sub_of_le hlohi
          rw [hsum] at h
          exact h.2
        · have hsub : hi - lo = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hlohi)
          rw [hsub, Nat.add_zero] at h
          omega
  | prod p q hp hq =>
      cases lo with | prod lo₀ lo₁ =>
      cases hi with | prod hi₀ hi₁ =>
      cases idx with | prod idx₀ idx₁ =>
      simp only [toList_prod, List.mem_flatMap, List.mem_map] at h
      rcases h with ⟨idx₀', hidx₀', idx₁', hidx₁', hprod⟩
      injection hprod with hidx₀ hidx₁
      subst idx₀'
      subst idx₁'
      rw [HTuple.Range.mem_iff_Valid]
      exact ⟨HTuple.Range.mem_iff_Valid.mp (hp hidx₀'), HTuple.Range.mem_iff_Valid.mp (hq hidx₁')⟩

end Range

end HTuple

end NumLean
