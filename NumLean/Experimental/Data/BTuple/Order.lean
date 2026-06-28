module

public import NumLean.Experimental.Data.BTuple.Basic
public import NumLean.Interfaces.Order
public import Mathlib.Data.List.Lex

@[expose] public section

/-!
# Orders for `BTuple`

This file is the `BTuple` analogue of `HTuple.Order`.

For product/tensor nodes, elementwise order behaves exactly as for `HTuple`: both children are
compared. This matches the intuition that a tensor/product-shaped tuple contains data in both
factors.

For direct-sum nodes, elementwise order follows the traversal order: values in the left summand are
strictly smaller than values in the right summand, and same-summand values compare recursively.

This is intentionally tag-aware: flattening with `toList` is not injective because left and right
summands can have the same leaf list, so sum tags must participate in ordering.
-/

open Std PRange

namespace NumLean

namespace BTuple

variable {α : Type u}

section Elementwise

/-- Strict elementwise order for binary tuples.

Products compare both children. Direct sums compare recursively in matching summands, with every
left-summand value strictly before every right-summand value. -/
def elementwiseLT {α : Type u} [LT α] : {p : Profile} → BTuple α p → BTuple α p → Prop
  | .leaf, .leaf x, .leaf y => x < y
  | .prod _ _, .prod x₀ x₁, .prod y₀ y₁ => elementwiseLT x₀ y₀ ∧ elementwiseLT x₁ y₁
  | .sum _ _, .sumLeft x _, .sumLeft y _ => elementwiseLT x y
  | .sum _ _, .sumLeft _ _, .sumRight _ _ => True
  | .sum _ _, .sumRight _ _, .sumLeft _ _ => False
  | .sum _ _, .sumRight _ x, .sumRight _ y => elementwiseLT x y

/-- Non-strict elementwise order for binary tuples.

Products compare both children. Direct sums compare recursively in matching summands, with every
left-summand value before every right-summand value. -/
def elementwiseLE {α : Type u} [LE α] : {p : Profile} → BTuple α p → BTuple α p → Prop
  | .leaf, .leaf x, .leaf y => x ≤ y
  | .prod _ _, .prod x₀ x₁, .prod y₀ y₁ => elementwiseLE x₀ y₀ ∧ elementwiseLE x₁ y₁
  | .sum _ _, .sumLeft x _, .sumLeft y _ => elementwiseLE x y
  | .sum _ _, .sumLeft _ _, .sumRight _ _ => True
  | .sum _ _, .sumRight _ _, .sumLeft _ _ => False
  | .sum _ _, .sumRight _ x, .sumRight _ y => elementwiseLE x y

instance {α : Type u} [LT α] {p : Profile} : LT (ElementwiseOrder (BTuple α p)) where
  lt x y := elementwiseLT x.val y.val

attribute [grind =] elementwiseLT_iff_mk_lt

instance {α : Type u} [LE α] {p : Profile} : LE (ElementwiseOrder (BTuple α p)) where
  le x y := elementwiseLE x.val y.val

attribute [grind =] elementwiseLE_iff_mk_le

section ElementwiseSimps

@[simp]
theorem elementwiseLE_leaf [LE α] {x y : α} :
    ((.leaf x : BTuple α .leaf) ≤ₑ .leaf y) ↔ x ≤ y := by rfl

@[simp]
theorem elementwiseLE_leaf' [LE α] {x : α} {y : BTuple α .leaf} :
    (.leaf x ≤ₑ y) ↔ x ≤ (y : α) := by
  cases y
  rfl

@[simp]
theorem elementwiseLE_leaf'' [LE α] {x : BTuple α .leaf} {y : α} :
    (x ≤ₑ .leaf y) ↔ (x : α) ≤ y := by
  cases x
  rfl

@[simp]
theorem elementwiseLT_leaf [LT α] {x y : α} :
    ((.leaf x : BTuple α .leaf) <ₑ .leaf y) ↔ x < y := by rfl

@[simp]
theorem elementwiseLT_leaf' [LT α] {x : α} {y : BTuple α .leaf} :
    (.leaf x <ₑ y) ↔ x < (y : α) := by
  cases y
  rfl

@[simp]
theorem elementwiseLT_leaf'' [LT α] {x : BTuple α .leaf} {y : α} :
    (x <ₑ .leaf y) ↔ (x : α) < y := by
  cases x
  rfl

@[simp]
theorem elementwiseLE_prod [LE α] {p q : Profile}
    {x₀ y₀ : BTuple α p} {x₁ y₁ : BTuple α q} :
    ((.prod x₀ x₁ : BTuple α (.prod p q)) ≤ₑ .prod y₀ y₁) ↔
      x₀ ≤ₑ y₀ ∧ x₁ ≤ₑ y₁ := by rfl

@[simp]
theorem elementwiseLT_prod [LT α] {p q : Profile}
    {x₀ y₀ : BTuple α p} {x₁ y₁ : BTuple α q} :
    ((.prod x₀ x₁ : BTuple α (.prod p q)) <ₑ .prod y₀ y₁) ↔
      x₀ <ₑ y₀ ∧ x₁ <ₑ y₁ := by rfl

@[simp]
theorem elementwiseLE_sumLeft [LE α] {p q : Profile} {x y : BTuple α p} :
    ((.sumLeft x q : BTuple α (.sum p q)) ≤ₑ .sumLeft y q) ↔ x ≤ₑ y := by rfl

@[simp]
theorem elementwiseLT_sumLeft [LT α] {p q : Profile} {x y : BTuple α p} :
    ((.sumLeft x q : BTuple α (.sum p q)) <ₑ .sumLeft y q) ↔ x <ₑ y := by rfl

@[simp]
theorem elementwiseLE_sumLeft_sumRight [LE α] {p q : Profile} {x : BTuple α p} {y : BTuple α q} :
    ((.sumLeft x q : BTuple α (.sum p q)) ≤ₑ .sumRight p y) := by
  change @elementwiseLE α _ (.sum p q) (BTuple.sumLeft x q) (BTuple.sumRight p y)
  trivial

@[simp]
theorem elementwiseLT_sumLeft_sumRight [LT α] {p q : Profile} {x : BTuple α p} {y : BTuple α q} :
    ((.sumLeft x q : BTuple α (.sum p q)) <ₑ .sumRight p y) := by
  change @elementwiseLT α _ (.sum p q) (BTuple.sumLeft x q) (BTuple.sumRight p y)
  trivial

@[simp]
theorem not_elementwiseLE_sumRight_sumLeft [LE α] {p q : Profile} {x : BTuple α q} {y : BTuple α p} :
    ¬ ((.sumRight p x : BTuple α (.sum p q)) ≤ₑ .sumLeft y q) := by
  intro h
  exact h

@[simp]
theorem not_elementwiseLT_sumRight_sumLeft [LT α] {p q : Profile} {x : BTuple α q} {y : BTuple α p} :
    ¬ ((.sumRight p x : BTuple α (.sum p q)) <ₑ .sumLeft y q) := by
  intro h
  exact h

@[simp]
theorem elementwiseLE_sumRight [LE α] {p q : Profile} {x y : BTuple α q} :
    ((.sumRight p x : BTuple α (.sum p q)) ≤ₑ .sumRight p y) ↔ x ≤ₑ y := by rfl

@[simp]
theorem elementwiseLT_sumRight [LT α] {p q : Profile} {x y : BTuple α q} :
    ((.sumRight p x : BTuple α (.sum p q)) <ₑ .sumRight p y) ↔ x <ₑ y := by rfl

end ElementwiseSimps

theorem elementwise_le_not_lt [LinearOrder α] {p : Profile} {a b : BTuple α p} :
    (a ≤ₑ b) → ¬(b <ₑ a) := by
  induction p with
  | leaf =>
      cases a
      cases b
      simp
  | prod p q hp hq =>
      cases a
      cases b
      simp_all
  | sum p q hp hq =>
      cases a <;> cases b
      · exact hp
      · intro _ h
        cases h
      · intro h
        cases h
      · exact hq

theorem elementwiseLE_refl [Preorder α] {p : Profile} (x : BTuple α p) : x ≤ₑ x := by
  induction p with
  | leaf =>
      cases x
      exact le_rfl
  | prod p q hp hq =>
      cases x
      exact ⟨hp _, hq _⟩
  | sum p q hp hq =>
      cases x
      · exact hp _
      · exact hq _

theorem elementwiseLE_trans [Preorder α] {p : Profile} {x y z : BTuple α p}
    (hxy : x ≤ₑ y) (hyz : y ≤ₑ z) : x ≤ₑ z := by
  induction p with
  | leaf =>
      cases x
      cases y
      cases z
      exact _root_.le_trans hxy hyz
  | prod p q hp hq =>
      cases x
      cases y
      cases z
      exact ⟨hp hxy.1 hyz.1, hq hxy.2 hyz.2⟩
  | sum p q hp hq =>
      cases x <;> cases y <;> cases z <;> try contradiction
      · exact hp hxy hyz
      · trivial
      · trivial
      · exact hq hxy hyz

end Elementwise

namespace Range

instance instMembershipRccBTuple {α : Type u} [LE α] {p : Profile} :
    Membership (BTuple α p) (Std.Rcc (BTuple α p)) where
  mem r idx := r.lower ≤ₑ idx ∧ idx ≤ₑ r.upper

instance instMembershipRcoBTuple {α : Type u} [LE α] [LT α] {p : Profile} :
    Membership (BTuple α p) (Std.Rco (BTuple α p)) where
  mem r idx := r.lower ≤ₑ idx ∧ idx <ₑ r.upper

instance instMembershipRciBTuple {α : Type u} [LE α] {p : Profile} :
    Membership (BTuple α p) (Std.Rci (BTuple α p)) where
  mem r idx := r.lower ≤ₑ idx

instance instMembershipRocBTuple {α : Type u} [LT α] [LE α] {p : Profile} :
    Membership (BTuple α p) (Std.Roc (BTuple α p)) where
  mem r idx := r.lower <ₑ idx ∧ idx ≤ₑ r.upper

instance instMembershipRooBTuple {α : Type u} [LT α] {p : Profile} :
    Membership (BTuple α p) (Std.Roo (BTuple α p)) where
  mem r idx := r.lower <ₑ idx ∧ idx <ₑ r.upper

instance instMembershipRoiBTuple {α : Type u} [LT α] {p : Profile} :
    Membership (BTuple α p) (Std.Roi (BTuple α p)) where
  mem r idx := r.lower <ₑ idx

instance instMembershipRicBTuple {α : Type u} [LE α] {p : Profile} :
    Membership (BTuple α p) (Std.Ric (BTuple α p)) where
  mem r idx := idx ≤ₑ r.upper

instance instMembershipRioBTuple {α : Type u} [LT α] {p : Profile} :
    Membership (BTuple α p) (Std.Rio (BTuple α p)) where
  mem r idx := idx <ₑ r.upper

instance instMembershipRiiBTuple {α : Type u} {p : Profile} :
    Membership (BTuple α p) (Std.Rii (BTuple α p)) where
  mem _ _ := True

theorem mem_iff_le_lt {p : Profile} [LT α] [LE α]
    {idx : BTuple α p} {lo hi : BTuple α p} :
    idx ∈ (lo...hi) ↔ lo ≤ₑ idx ∧ idx <ₑ hi := Iff.rfl

theorem mem_rcc_iff {p : Profile} [LE α]
    {idx : BTuple α p} {lo hi : BTuple α p} :
    idx ∈ (lo...=hi) ↔ lo ≤ₑ idx ∧ idx ≤ₑ hi := Iff.rfl

theorem mem_rco_iff {p : Profile} [LT α] [LE α]
    {idx : BTuple α p} {lo hi : BTuple α p} :
    idx ∈ (lo...hi) ↔ lo ≤ₑ idx ∧ idx <ₑ hi := Iff.rfl

theorem mem_rci_iff {p : Profile} [LE α]
    {idx : BTuple α p} {lo : BTuple α p} :
    idx ∈ (lo...*) ↔ lo ≤ₑ idx := Iff.rfl

theorem mem_roc_iff {p : Profile} [LT α] [LE α]
    {idx : BTuple α p} {lo hi : BTuple α p} :
    idx ∈ (lo<...=hi) ↔ lo <ₑ idx ∧ idx ≤ₑ hi := Iff.rfl

theorem mem_roo_iff {p : Profile} [LT α]
    {idx : BTuple α p} {lo hi : BTuple α p} :
    idx ∈ (lo<...hi) ↔ lo <ₑ idx ∧ idx <ₑ hi := Iff.rfl

theorem mem_roi_iff {p : Profile} [LT α]
    {idx : BTuple α p} {lo : BTuple α p} :
    idx ∈ (lo<...*) ↔ lo <ₑ idx := Iff.rfl

theorem mem_ric_iff {p : Profile} [LE α]
    {idx : BTuple α p} {hi : BTuple α p} :
    idx ∈ (*...=hi) ↔ idx ≤ₑ hi := Iff.rfl

theorem mem_rio_iff {p : Profile} [LT α]
    {idx : BTuple α p} {hi : BTuple α p} :
    idx ∈ (*...hi) ↔ idx <ₑ hi := Iff.rfl

theorem mem_rii_iff {p : Profile} {idx : BTuple α p} :
    idx ∈ (*...* : Std.Rii (BTuple α p)) ↔ True := Iff.rfl

end Range

end BTuple

end NumLean
