module

public import NumLean.Experimental.Data.BTuple.Order

@[expose] public section

/-!
# Unbundled ranges for `BTuple`

The index remains unbundled:

```lean
idx : BTuple Nat p
```

but bounds are shape-valued:

```lean
lo hi : BTuple.Shape p
idx ∈ (lo...hi : Std.Rco (BTuple.Shape p))
```

For products/tensors, bounds are checked in both factors. For direct sums, the index tag chooses a
summand and bounds are checked in that summand only. This preserves the expected loop shape:

```lean
for i in lo...hi do
  let linIdx := offset + BTuple.Range.linearIndex lo hi i
  x[i] := f i
```
-/

namespace NumLean

namespace BTuple

namespace Shape

/-- The zero lower bound with the same profile as a shape. -/
@[inline] def zero : {p : Profile} → Shape p → Shape p
  | .leaf, .leaf _ => .leaf 0
  | .prod _ _, .prod s t => .prod (zero s) (zero t)
  | .sum _ _, .sum s t => .sum (zero s) (zero t)

end Shape

namespace Range

/-- In-bounds predicate for an unbundled binary tuple index in a half-open shape range.

At product/tensor nodes, both child indices must be in bounds. At direct-sum nodes, the index tag
chooses the active summand and only that branch is checked. -/
@[inline] def InBounds : {p : Profile} → Shape p → Shape p → BTuple Nat p → Prop
  | .leaf, .leaf lo, .leaf hi, .leaf i => i ∈ (lo...hi)
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁, .prod i₀ i₁ =>
      InBounds lo₀ hi₀ i₀ ∧ InBounds lo₁ hi₁ i₁
  | .sum _ _, .sum lo₀ _, .sum hi₀ _, .sumLeft i _ => InBounds lo₀ hi₀ i
  | .sum _ _, .sum _ lo₁, .sum _ hi₁, .sumRight _ i => InBounds lo₁ hi₁ i

instance instMembershipRcoShape {p : Profile} : Membership (BTuple Nat p) (Std.Rco (Shape p)) where
  mem r idx := InBounds r.lower r.upper idx

/-- Cardinality of a half-open shape range. -/
@[inline] def card : {p : Profile} → Shape p → Shape p → Nat
  | .leaf, .leaf lo, .leaf hi => hi - lo
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁ => card lo₀ hi₀ * card lo₁ hi₁
  | .sum _ _, .sum lo₀ lo₁, .sum hi₀ hi₁ => card lo₀ hi₀ + card lo₁ hi₁

/-- Row-major linear index inside a half-open shape range.

For direct sums, the right summand starts after the whole left summand range block. -/
@[inline] def linearIndex : {p : Profile} → Shape p → Shape p → BTuple Nat p → Nat
  | .leaf, .leaf lo, .leaf _, .leaf i => i - lo
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁, .prod i₀ i₁ =>
      linearIndex lo₁ hi₁ i₁ + card lo₁ hi₁ * linearIndex lo₀ hi₀ i₀
  | .sum _ _, .sum lo₀ _, .sum hi₀ _, .sumLeft i _ => linearIndex lo₀ hi₀ i
  | .sum _ _, .sum lo₀ lo₁, .sum hi₀ hi₁, .sumRight _ i =>
      card lo₀ hi₀ + linearIndex lo₁ hi₁ i

/-- Structural list specification for half-open shape ranges, in row-major order. -/
@[inline] def toList : {p : Profile} → Shape p → Shape p → List (BTuple Nat p)
  | .leaf, .leaf lo, .leaf hi => (List.range' lo (hi - lo)).map BTuple.leaf
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁ =>
      (toList lo₀ hi₀).flatMap fun i₀ =>
        (toList lo₁ hi₁).map fun i₁ => BTuple.prod i₀ i₁
  | .sum _ _, .sum lo₀ lo₁, .sum hi₀ hi₁ =>
      (toList lo₀ hi₀).map (fun i => BTuple.sumLeft i _) ++
        (toList lo₁ hi₁).map (fun i => BTuple.sumRight _ i)

@[simp] theorem card_leaf (lo hi : Nat) : card (Shape.leaf lo) (Shape.leaf hi) = hi - lo := rfl

@[simp] theorem card_prod {p q : Profile} (lo₀ hi₀ : Shape p) (lo₁ hi₁ : Shape q) :
    card (Shape.prod lo₀ lo₁) (Shape.prod hi₀ hi₁) = card lo₀ hi₀ * card lo₁ hi₁ := rfl

@[simp] theorem card_sum {p q : Profile} (lo₀ hi₀ : Shape p) (lo₁ hi₁ : Shape q) :
    card (Shape.sum lo₀ lo₁) (Shape.sum hi₀ hi₁) = card lo₀ hi₀ + card lo₁ hi₁ := rfl

@[simp] theorem toList_leaf (lo hi : Nat) :
    toList (Shape.leaf lo) (Shape.leaf hi) = (List.range' lo (hi - lo)).map BTuple.leaf := rfl

@[simp] theorem toList_prod {p q : Profile} (lo₀ hi₀ : Shape p) (lo₁ hi₁ : Shape q) :
    toList (Shape.prod lo₀ lo₁) (Shape.prod hi₀ hi₁) =
      (toList lo₀ hi₀).flatMap fun i₀ =>
        (toList lo₁ hi₁).map fun i₁ => BTuple.prod i₀ i₁ := rfl

@[simp] theorem toList_sum {p q : Profile} (lo₀ hi₀ : Shape p) (lo₁ hi₁ : Shape q) :
    toList (Shape.sum lo₀ lo₁) (Shape.sum hi₀ hi₁) =
      (toList lo₀ hi₀).map (fun i => BTuple.sumLeft i q) ++
        (toList lo₁ hi₁).map (fun i => BTuple.sumRight p i) := rfl

/-- The list specification has the expected cardinality. -/
theorem length_toList : {p : Profile} → (lo hi : Shape p) → (toList lo hi).length = card lo hi
  | .leaf, .leaf lo, .leaf hi => by simp
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁ => by
      simp [length_toList lo₀ hi₀, length_toList lo₁ hi₁]
  | .sum _ _, .sum lo₀ lo₁, .sum hi₀ hi₁ => by
      simp [length_toList lo₀ hi₀, length_toList lo₁ hi₁]

/-- Membership in the list specification implies the unbundled in-bounds predicate. -/
theorem inBounds_of_mem_toList {p : Profile} {lo hi : Shape p} {idx : BTuple Nat p}
    (h : idx ∈ toList lo hi) : InBounds lo hi idx := by
  induction lo with
  | leaf lo =>
      cases hi with | leaf hi =>
      cases idx with | leaf i =>
      simp [toList] at h
      change lo ≤ i ∧ i < hi
      omega
  | prod lo₀ lo₁ h₀ h₁ =>
      cases hi with | prod hi₀ hi₁ =>
      cases idx with | prod i₀ i₁ =>
      simp only [toList_prod, List.mem_flatMap, List.mem_map] at h
      rcases h with ⟨i₀', hi₀', i₁', hi₁', hidx⟩
      injection hidx with hleft hright
      subst i₀'
      subst i₁'
      exact ⟨h₀ hi₀', h₁ hi₁'⟩
  | sum lo₀ lo₁ h₀ h₁ =>
      cases hi with | sum hi₀ hi₁ =>
      cases idx with
      | sumLeft i _ =>
          simp only [toList_sum, List.mem_append, List.mem_map] at h
          rcases h with h | h
          · rcases h with ⟨i', hi', hidx⟩
            injection hidx with heq
            subst i'
            exact h₀ hi'
          · rcases h with ⟨j', _, hidx⟩
            cases hidx
      | sumRight _ j =>
          simp only [toList_sum, List.mem_append, List.mem_map] at h
          rcases h with h | h
          · rcases h with ⟨i', _, hidx⟩
            cases hidx
          · rcases h with ⟨j', hj', hidx⟩
            injection hidx with heq
            subst j'
            exact h₁ hj'

/-- Every in-bounds unbundled index appears in the structural list specification. -/
theorem mem_toList_of_inBounds {p : Profile} {lo hi : Shape p} {idx : BTuple Nat p}
    (h : InBounds lo hi idx) : idx ∈ toList lo hi := by
  induction lo with
  | leaf lo =>
      cases hi with | leaf hi =>
      cases idx with | leaf i =>
      change lo ≤ i ∧ i < hi at h
      simp [toList]
      omega
  | prod lo₀ lo₁ h₀ h₁ =>
      cases hi with | prod hi₀ hi₁ =>
      cases idx with | prod i₀ i₁ =>
      rw [toList_prod, List.mem_flatMap]
      refine ⟨i₀, h₀ h.1, ?_⟩
      rw [List.mem_map]
      exact ⟨i₁, h₁ h.2, rfl⟩
  | sum lo₀ lo₁ h₀ h₁ =>
      cases hi with | sum hi₀ hi₁ =>
      cases idx with
      | sumLeft i _ =>
          rw [toList_sum, List.mem_append]
          apply Or.inl
          rw [List.mem_map]
          exact ⟨i, h₀ h, rfl⟩
      | sumRight _ j =>
          rw [toList_sum, List.mem_append]
          apply Or.inr
          rw [List.mem_map]
          exact ⟨j, h₁ h, rfl⟩

theorem mem_toList_iff_inBounds {p : Profile} {lo hi : Shape p} {idx : BTuple Nat p} :
    idx ∈ toList lo hi ↔ InBounds lo hi idx :=
  ⟨inBounds_of_mem_toList, mem_toList_of_inBounds⟩

theorem mem_iff_inBounds {p : Profile} {lo hi : Shape p} {idx : BTuple Nat p} :
    idx ∈ (lo...hi : Std.Rco (Shape p)) ↔ InBounds lo hi idx := Iff.rfl

end Range

end BTuple

end NumLean
