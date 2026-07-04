module

public import NumLean.Data.HTuple.Algebra
public import NumLean.Data.HTuple.GetElemTacticInit
public import Mathlib.Data.List.Lex

@[expose] public section

open Lean Std PRange

namespace NumLean

namespace HTuple

variable {α : Type u}

section Elementwise

def elementwiseLT {α : Type u} [LT α] : {p : Profile} → HTuple α p → HTuple α p → Prop
  | .leaf, .leaf x, .leaf y => x < y
  | .prod _ _, .prod x₀ x₁, .prod y₀ y₁ => elementwiseLT x₀ y₀ ∧ elementwiseLT x₁ y₁

def elementwiseLE {α : Type u} [LE α] : {p : Profile} → HTuple α p → HTuple α p → Prop
  | .leaf, .leaf x, .leaf y => x ≤ y
  | .prod _ _, .prod x₀ x₁, .prod y₀ y₁ => elementwiseLE x₀ y₀ ∧ elementwiseLE x₁ y₁

instance {α : Type u} [LT α] {p : Profile} : LT (ElementwiseOrder (HTuple α p)) where
  lt x y := elementwiseLT x.val y.val

attribute [grind_htuple_order =] elementwiseLT_iff_mk_lt

instance {α : Type u} [LE α] {p : Profile} : LE (ElementwiseOrder (HTuple α p)) where
  le x y := elementwiseLE x.val y.val

attribute [grind_htuple_order =] elementwiseLE_iff_mk_le

section ElwiseSimps

@[simp, grind ←, grind_htuple_order ←]
theorem elementwiseLE_leaf [LE α] {x y : α} :
    ((.leaf x : HTuple α .leaf) ≤ₑ .leaf y) ↔ x ≤ y := by  rfl

@[simp, grind =, grind_htuple_order _=_]
theorem elementwiseLE_leaf' [LE α] {x : α} {y : HTuple α .leaf} :
    (.leaf x ≤ₑ y) ↔ x ≤ (y : α) := by have .leaf y := y; rfl

@[simp, grind =, grind_htuple_order _=_]
theorem elementwiseLE_leaf'' [LE α] {x : HTuple α .leaf} {y : α} :
    (x ≤ₑ .leaf y) ↔ (x : α) ≤ y := by have .leaf x := x; rfl

@[simp, grind ←, grind_htuple_order ←]
theorem elementwiseLT_leaf [LT α] {x y : α} :
    ((.leaf x : HTuple α .leaf) <ₑ .leaf y) ↔ x < y := by rfl

@[simp, grind =, grind_htuple_order _=_]
theorem elementwiseLT_leaf' [LT α] {x : α} {y : HTuple α .leaf} :
    (.leaf x <ₑ y) ↔ x < (y : α) := by have .leaf y := y; rfl

@[simp, grind =, grind_htuple_order _=_]
theorem elementwiseLT_leaf'' [LT α] {x : HTuple α .leaf} {y : α} :
    (x <ₑ .leaf y) ↔ (x : α) < y := by have .leaf x := x; rfl

@[simp, grind =, grind_htuple_order =]
theorem elementwiseLE_natCast_left {x : Nat} {y : HTuple Nat .leaf} :
    ((Nat.cast x : HTuple Nat .leaf) ≤ₑ y) ↔ x ≤ (y : Nat) := by
  cases y
  rfl

@[simp, grind =, grind_htuple_order =]
theorem elementwiseLE_natCast_right {x : HTuple Nat .leaf} {y : Nat} :
    (x ≤ₑ (Nat.cast y : HTuple Nat .leaf)) ↔ (x : Nat) ≤ y := by
  cases x
  rfl

@[simp, grind =, grind_htuple_order =]
theorem elementwiseLT_natCast_left {x : Nat} {y : HTuple Nat .leaf} :
    ((Nat.cast x : HTuple Nat .leaf) <ₑ y) ↔ x < (y : Nat) := by
  cases y
  rfl

@[simp, grind =, grind_htuple_order =]
theorem elementwiseLT_natCast_right {x : HTuple Nat .leaf} {y : Nat} :
    (x <ₑ (Nat.cast y : HTuple Nat .leaf)) ↔ (x : Nat) < y := by
  cases x
  rfl

@[simp, grind =, grind_htuple_order =]
theorem elementwiseLE_prod [LE α] {p q : Profile}
    {x₀ y₀ : HTuple α p} {x₁ y₁ : HTuple α q} :
    ((.prod x₀ x₁ : HTuple α (.prod p q)) ≤ₑ .prod y₀ y₁) ↔
      x₀ ≤ₑ y₀ ∧ x₁ ≤ₑ y₁ := by rfl

@[simp, grind =, grind_htuple_order =]
theorem elementwiseLT_prod [LT α] {p q : Profile}
    {x₀ y₀ : HTuple α p} {x₁ y₁ : HTuple α q} :
    ((.prod x₀ x₁ : HTuple α (.prod p q)) <ₑ .prod y₀ y₁) ↔
      x₀ <ₑ y₀ ∧ x₁ <ₑ y₁ := by rfl

end ElwiseSimps

/-- Row-major indices of bounded coordinates are bounded by the shape's cardinality. -/
theorem rowMajorIndex_lt_numel {p : Profile} {shape i : HTuple Nat p}
    (hi : i <ₑ shape) : i.rowMajorIndex shape < shape.numel := by
  induction p with
  | leaf =>
      cases shape with | leaf shape =>
      cases i with | leaf i =>
      simpa [rowMajorIndex, numel] using hi
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases i with | prod i₀ i₁ =>
      have hidx₀ : i₀.rowMajorIndex shape₀ < shape₀.numel := hp hi.1
      have hidx₁ : i₁.rowMajorIndex shape₁ < shape₁.numel := hq hi.2
      simp [rowMajorIndex, numel]
      calc
        i₁.rowMajorIndex shape₁ + shape₁.numel * i₀.rowMajorIndex shape₀
            < shape₁.numel + shape₁.numel * i₀.rowMajorIndex shape₀ := by
              exact Nat.add_lt_add_right hidx₁ _
        _ = shape₁.numel * (i₀.rowMajorIndex shape₀ + 1) := by
              rw [Nat.mul_succ, Nat.add_comm]
        _ ≤ shape₁.numel * shape₀.numel := by
              exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hidx₀)
        _ = shape₀.numel * shape₁.numel := by
              rw [Nat.mul_comm]

/-- Column-major indices of bounded coordinates are bounded by the shape's cardinality. -/
theorem colMajorIndex_lt_numel {p : Profile} {shape i : HTuple Nat p}
    (hi : i <ₑ shape) : i.colMajorIndex shape < shape.numel := by
  induction p with
  | leaf =>
      cases shape with | leaf shape =>
      cases i with | leaf i =>
      simpa [colMajorIndex, numel] using hi
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases i with | prod i₀ i₁ =>
      have hidx₀ : i₀.colMajorIndex shape₀ < shape₀.numel := hp hi.1
      have hidx₁ : i₁.colMajorIndex shape₁ < shape₁.numel := hq hi.2
      simp [colMajorIndex, numel]
      calc
        i₀.colMajorIndex shape₀ + shape₀.numel * i₁.colMajorIndex shape₁
            < shape₀.numel + shape₀.numel * i₁.colMajorIndex shape₁ := by
              exact Nat.add_lt_add_right hidx₀ _
        _ = shape₀.numel * (i₁.colMajorIndex shape₁ + 1) := by
              rw [Nat.mul_succ, Nat.add_comm]
        _ ≤ shape₀.numel * shape₁.numel := by
               exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hidx₁)

theorem rowMajorUnflatten_lt {p : Profile} (shape : HTuple Nat p) {i : Nat}
    (hi : i < shape.numel) : rowMajorUnflatten shape i <ₑ shape := by
  induction shape generalizing i with
  | leaf n => simpa [rowMajorUnflatten] using hi
  | prod l r hl hr =>
      have hprodpos : 0 < l.numel * r.numel := by
        exact Nat.lt_of_le_of_lt (Nat.zero_le i) (by simpa [HTuple.numel] using hi)
      have hrpos : 0 < r.numel := pos_of_mul_pos_right hprodpos (Nat.zero_le l.numel)
      constructor
      · apply hl
        exact (Nat.div_lt_iff_lt_mul hrpos).2 (by simpa [HTuple.numel, Nat.mul_comm] using hi)
      · apply hr
        exact Nat.mod_lt i hrpos

theorem colMajorUnflatten_lt {p : Profile} (shape : HTuple Nat p) {i : Nat}
    (hi : i < shape.numel) : colMajorUnflatten shape i <ₑ shape := by
  induction shape generalizing i with
  | leaf n => simpa [colMajorUnflatten] using hi
  | prod l r hl hr =>
      have hprodpos : 0 < l.numel * r.numel := by
        exact Nat.lt_of_le_of_lt (Nat.zero_le i) (by simpa [HTuple.numel] using hi)
      have hlpos : 0 < l.numel := pos_of_mul_pos_left hprodpos (Nat.zero_le r.numel)
      constructor
      · apply hl
        exact Nat.mod_lt i hlpos
      · apply hr
        exact (Nat.div_lt_iff_lt_mul hlpos).2 (by simpa [HTuple.numel, Nat.mul_comm] using hi)

theorem rowMajorIndex_rowMajorUnflatten {p : Profile} (shape : HTuple Nat p) {i : Nat}
    (hi : i < shape.numel) : (rowMajorUnflatten shape i).rowMajorIndex shape = i := by
  induction shape generalizing i with
  | leaf n => simp [rowMajorUnflatten, rowMajorIndex]
  | prod l r hl hr =>
      have hprodpos : 0 < l.numel * r.numel := by
        exact Nat.lt_of_le_of_lt (Nat.zero_le i) (by simpa [HTuple.numel] using hi)
      have hrpos : 0 < r.numel := pos_of_mul_pos_right hprodpos (Nat.zero_le l.numel)
      have hdiv : i / r.numel < l.numel :=
        (Nat.div_lt_iff_lt_mul hrpos).2 (by simpa [HTuple.numel, Nat.mul_comm] using hi)
      have hmod : i % r.numel < r.numel := Nat.mod_lt i hrpos
      simp [rowMajorUnflatten, rowMajorIndex, hl hdiv, hr hmod, Nat.mod_add_div]

theorem colMajorIndex_colMajorUnflatten {p : Profile} (shape : HTuple Nat p) {i : Nat}
    (hi : i < shape.numel) : (colMajorUnflatten shape i).colMajorIndex shape = i := by
  induction shape generalizing i with
  | leaf n => simp [colMajorUnflatten, colMajorIndex]
  | prod l r hl hr =>
      have hprodpos : 0 < l.numel * r.numel := by
        exact Nat.lt_of_le_of_lt (Nat.zero_le i) (by simpa [HTuple.numel] using hi)
      have hlpos : 0 < l.numel := pos_of_mul_pos_left hprodpos (Nat.zero_le r.numel)
      have hmod : i % l.numel < l.numel := Nat.mod_lt i hlpos
      have hdiv : i / l.numel < r.numel :=
        (Nat.div_lt_iff_lt_mul hlpos).2 (by simpa [HTuple.numel, Nat.mul_comm] using hi)
      simp [colMajorUnflatten, colMajorIndex, hl hmod, hr hdiv, Nat.mod_add_div]

theorem rowMajorUnflatten_rowMajorIndex {p : Profile} (shape i : HTuple Nat p)
    (hi : i <ₑ shape) : rowMajorUnflatten shape (i.rowMajorIndex shape) = i := by
  induction shape with
  | leaf n =>
      cases i with | leaf i => simp [rowMajorUnflatten, rowMajorIndex]
  | prod l r hl hr =>
      cases i with | prod il ir =>
      have hir : ir.rowMajorIndex r < r.numel := rowMajorIndex_lt_numel hi.2
      have hdiv : (ir.rowMajorIndex r + r.numel * il.rowMajorIndex l) / r.numel =
          il.rowMajorIndex l := by
        rw [Nat.add_mul_div_left _ _ (by omega : 0 < r.numel), Nat.div_eq_of_lt hir]
        simp
      simp [rowMajorUnflatten, rowMajorIndex, hdiv, Nat.mod_eq_of_lt hir, hl il hi.1, hr ir hi.2]

theorem colMajorUnflatten_colMajorIndex {p : Profile} (shape i : HTuple Nat p)
    (hi : i <ₑ shape) : colMajorUnflatten shape (i.colMajorIndex shape) = i := by
  induction shape with
  | leaf n =>
      cases i with | leaf i => simp [colMajorUnflatten, colMajorIndex]
  | prod l r hl hr =>
      cases i with | prod il ir =>
      have hil : il.colMajorIndex l < l.numel := colMajorIndex_lt_numel hi.1
      have hdiv : (il.colMajorIndex l + l.numel * ir.colMajorIndex r) / l.numel =
          ir.colMajorIndex r := by
        rw [Nat.add_mul_div_left _ _ (by omega : 0 < l.numel), Nat.div_eq_of_lt hil]
        simp
      simp [colMajorUnflatten, colMajorIndex, hdiv, Nat.mod_eq_of_lt hil, hl il hi.1, hr ir hi.2]

@[grind ←, grind_htuple_order ←]
theorem elementwise_lt_not_le {α} [LinearOrder α] {a b : HTuple α p} : (a <ₑ b) → ¬(b ≤ₑ a) := by
  induction p
  case leaf =>
    have .leaf a := a
    have .leaf b := b
    simp
  case prod p q hp hq =>
    have .prod a a' := a
    have .prod b b' := b
    simp_all

@[grind ←, grind_htuple_order ←]
theorem elementwise_le_not_lt {α} [LinearOrder α] {a b : HTuple α p} : (a ≤ₑ b) → ¬(b <ₑ a) := by
  induction p
  case leaf =>
    have .leaf a := a
    have .leaf b := b
    simp
  case prod p q hp hq =>
    have .prod a a' := a
    have .prod b b' := b
    simp_all

@[grind ←, grind_htuple_order ←]
theorem elementwiseLE_refl [Preorder α] {p : Profile} (x : HTuple α p) : x ≤ₑ x := by
  induction p with
  | leaf =>
      cases x with | leaf x =>
      exact le_rfl
  | prod p q hp hq =>
      cases x with | prod x₀ x₁ =>
      exact ⟨hp x₀, hq x₁⟩

@[grind →, grind_htuple_order →]
theorem elementwiseLE_trans [Preorder α] {p : Profile} {x y z : HTuple α p}
    (hxy : x ≤ₑ y) (hyz : y ≤ₑ z) : x ≤ₑ z := by
  induction p with
  | leaf =>
      cases x with | leaf x =>
      cases y with | leaf y =>
      cases z with | leaf z =>
      exact _root_.le_trans hxy hyz
  | prod p q hp hq =>
      cases x with | prod x₀ x₁ =>
      cases y with | prod y₀ y₁ =>
      cases z with | prod z₀ z₁ =>
      exact ⟨hp hxy.1 hyz.1, hq hxy.2 hyz.2⟩

theorem elementwiseLE_iff_get [LE α] {p : Profile} {x y : HTuple α p} :
    x ≤ₑ y ↔ ∀ i : Index p, x.get i ≤ y.get i := by
  induction p with
  | leaf =>
      cases x with | leaf x =>
      cases y with | leaf y =>
      rw [elementwiseLE_leaf]
      constructor
      · intro h i
        cases i
        exact h
      · intro h
        exact h .leaf
  | prod p q hp hq =>
      cases x with | prod x₀ x₁ =>
      cases y with | prod y₀ y₁ =>
      rw [elementwiseLE_prod, hp, hq]
      constructor
      · rintro ⟨h₀, h₁⟩ i
        cases i with
        | left i => exact h₀ i
        | right i => exact h₁ i
      · intro h
        exact ⟨fun i => h (.left i), fun i => h (.right i)⟩

theorem elementwiseLT_iff_get [LT α] {p : Profile} {x y : HTuple α p} :
    x <ₑ y ↔ ∀ i : Index p, x.get i < y.get i := by
  induction p with
  | leaf =>
      cases x with | leaf x =>
      cases y with | leaf y =>
      rw [elementwiseLT_leaf]
      constructor
      · intro h i
        cases i
        exact h
      · intro h
        exact h .leaf
  | prod p q hp hq =>
      cases x with | prod x₀ x₁ =>
      cases y with | prod y₀ y₁ =>
      rw [elementwiseLT_prod, hp, hq]
      constructor
      · rintro ⟨h₀, h₁⟩ i
        cases i with
        | left i => exact h₀ i
        | right i => exact h₁ i
      · intro h
        exact ⟨fun i => h (.left i), fun i => h (.right i)⟩

@[simp, grind =, grind_htuple_order =]
theorem elementwiseLE_zero_leaf [Zero α] [LE α] {x : α} :
    ((0 : HTuple α .leaf) ≤ₑ .leaf x) ↔ 0 ≤ x := by
  rw [zero_leaf, elementwiseLE_leaf]

@[simp, grind =, grind_htuple_order =]
theorem elementwiseLT_zero_leaf [Zero α] [LT α] {x : α} :
    ((0 : HTuple α .leaf) <ₑ .leaf x) ↔ 0 < x := by
  rw [zero_leaf, elementwiseLT_leaf]

@[simp, grind =, grind_htuple_order =]
theorem elementwiseLE_zero_prod [Zero α] [LE α] {p q : Profile}
    {x₀ : HTuple α p} {x₁ : HTuple α q} :
    ((0 : HTuple α (.prod p q)) ≤ₑ .prod x₀ x₁) ↔
      (0 : HTuple α p) ≤ₑ x₀ ∧ (0 : HTuple α q) ≤ₑ x₁ := by
  rw [zero_prod, elementwiseLE_prod]

@[simp, grind =, grind_htuple_order =]
theorem elementwiseLT_zero_prod [Zero α] [LT α] {p q : Profile}
    {x₀ : HTuple α p} {x₁ : HTuple α q} :
    ((0 : HTuple α (.prod p q)) <ₑ .prod x₀ x₁) ↔
      (0 : HTuple α p) <ₑ x₀ ∧ (0 : HTuple α q) <ₑ x₁ := by
  rw [zero_prod, elementwiseLT_prod]

-- Can we state a general theorem for all these cases?
@[simp, grind ←, grind_htuple_order ←]
theorem elementwiseLE_zero_nat {p} (x : HTuple ℕ p) : 0 ≤ₑ x := by
  induction p <;> (cases x; simp_all)

@[simp, grind ←, grind_htuple_order ←]
theorem elementwiseLE_zero_usize {p} (x : HTuple USize p) : 0 ≤ₑ x := by
  induction p <;> (cases x; simp_all)

@[simp, grind ←, grind_htuple_order ←]
theorem elementwiseLE_zero_uint32 {p} (x : HTuple UInt32 p) : 0 ≤ₑ x := by
  induction p <;> (cases x; simp_all)

@[simp, grind ←, grind_htuple_order ←]
theorem elementwiseLE_zero_uint64 {p} (x : HTuple UInt64 p) : 0 ≤ₑ x := by
  induction p <;> (cases x; simp_all)

end Elementwise

section Lexocographic

instance instLexOrderLinearOrder [LinearOrder α] {p : Profile} :
    LinearOrder (LexOrder (HTuple α p)) :=
  LinearOrder.lift' (fun x : LexOrder (HTuple α p) => x.val.toList) (by
    intro x y h
    cases x with | mk x =>
    cases y with | mk y =>
    exact congrArg LexOrder.mk (HTuple.toList_injective h))

instance instColexOrderLinearOrder [LinearOrder α] {p : Profile} :
    LinearOrder (ColexOrder (HTuple α p)) :=
  LinearOrder.lift' (fun x : ColexOrder (HTuple α p) => x.val.toList.reverse) (by
    intro x y h
    cases x with | mk x =>
    cases y with | mk y =>
    apply congrArg ColexOrder.mk
    apply HTuple.toList_injective
    exact List.reverse_injective h)

attribute [grind_htuple_order =]
  lexLT_iff_mk_lt
  lexLE_iff_mk_le
  colexLT_iff_mk_lt
  colexLE_iff_mk_le

section Elementwise


end Elementwise

namespace Range

instance instMembershipRccHTuple {α : Type u} [LE α] {p : Profile} :
    Membership (HTuple α p) (Std.Rcc (HTuple α p)) where
  mem r idx := r.lower ≤ₑ idx ∧ idx ≤ₑ r.upper

instance instMembershipRcoHTuple {α : Type u} [LE α] [LT α] {p : Profile} :
    Membership (HTuple α p) (Std.Rco (HTuple α p)) where
  mem r idx := r.lower ≤ₑ idx ∧ idx <ₑ r.upper

instance instMembershipRciHTuple {α : Type u} [LE α] {p : Profile} :
    Membership (HTuple α p) (Std.Rci (HTuple α p)) where
  mem r idx := r.lower ≤ₑ idx

instance instMembershipRocHTuple {α : Type u} [LT α] [LE α] {p : Profile} :
    Membership (HTuple α p) (Std.Roc (HTuple α p)) where
  mem r idx := r.lower <ₑ idx ∧ idx ≤ₑ r.upper

instance instMembershipRooHTuple {α : Type u} [LT α] {p : Profile} :
    Membership (HTuple α p) (Std.Roo (HTuple α p)) where
  mem r idx := r.lower <ₑ idx ∧ idx <ₑ r.upper

instance instMembershipRoiHTuple {α : Type u} [LT α] {p : Profile} :
    Membership (HTuple α p) (Std.Roi (HTuple α p)) where
  mem r idx := r.lower <ₑ idx

instance instMembershipRicHTuple {α : Type u} [LE α] {p : Profile} :
    Membership (HTuple α p) (Std.Ric (HTuple α p)) where
  mem r idx := idx ≤ₑ r.upper

instance instMembershipRioHTuple {α : Type u} [LT α] {p : Profile} :
    Membership (HTuple α p) (Std.Rio (HTuple α p)) where
  mem r idx := idx <ₑ r.upper

instance instMembershipRiiHTuple {α : Type u} {p : Profile} :
    Membership (HTuple α p) (Std.Rii (HTuple α p)) where
  mem _ _ := True

@[grind =, grind_htuple_order =]
theorem mem_iff_le_lt {p : Profile} [LT α] [LE α]
    {idx : HTuple α p} {lo hi : HTuple α p} :
    idx ∈ (lo...hi) ↔ lo ≤ₑ idx ∧ idx <ₑ hi := Iff.rfl

@[grind =, grind_htuple_order =]
theorem mem_rcc_iff {p : Profile} [LE α]
    {idx : HTuple α p} {lo hi : HTuple α p} :
    idx ∈ (lo...=hi) ↔ lo ≤ₑ idx ∧ idx ≤ₑ hi := Iff.rfl

@[grind =, grind_htuple_order =]
theorem mem_rco_iff {p : Profile} [LT α] [LE α]
    {idx : HTuple α p} {lo hi : HTuple α p} :
    idx ∈ (lo...hi) ↔ lo ≤ₑ idx ∧ idx <ₑ hi := Iff.rfl

@[grind =, grind_htuple_order =]
theorem mem_rci_iff {p : Profile} [LE α]
    {idx : HTuple α p} {lo : HTuple α p} :
    idx ∈ (lo...*) ↔ lo ≤ₑ idx := Iff.rfl

@[grind =, grind_htuple_order =]
theorem mem_roc_iff {p : Profile} [LT α] [LE α]
    {idx : HTuple α p} {lo hi : HTuple α p} :
    idx ∈ (lo<...=hi) ↔ lo <ₑ idx ∧ idx ≤ₑ hi := Iff.rfl

@[grind =, grind_htuple_order =]
theorem mem_roo_iff {p : Profile} [LT α]
    {idx : HTuple α p} {lo hi : HTuple α p} :
    idx ∈ (lo<...hi) ↔ lo <ₑ idx ∧ idx <ₑ hi := Iff.rfl

@[grind =, grind_htuple_order =]
theorem mem_roi_iff {p : Profile} [LT α]
    {idx : HTuple α p} {lo : HTuple α p} :
    idx ∈ (lo<...*) ↔ lo <ₑ idx := Iff.rfl

@[grind =, grind_htuple_order =]
theorem mem_ric_iff {p : Profile} [LE α]
    {idx : HTuple α p} {hi : HTuple α p} :
    idx ∈ (*...=hi) ↔ idx ≤ₑ hi := Iff.rfl

@[grind =, grind_htuple_order =]
theorem mem_rio_iff {p : Profile} [LT α]
    {idx : HTuple α p} {hi : HTuple α p} :
    idx ∈ (*...hi) ↔ idx <ₑ hi := Iff.rfl

@[grind =, grind_htuple_order =]
theorem mem_rii_iff {p : Profile} {idx : HTuple α p} :
    idx ∈ (*...* : Std.Rii (HTuple α p)) ↔ True := Iff.rfl

theorem mem_rco_mono {α : Type u} [Preorder α] {p : Profile}
    {lo hi lo' hi' idx : HTuple α p} :
    idx ∈ (lo...hi) → lo' ≤ₑ lo → hi ≤ₑ hi' → idx ∈ (lo'...hi') := by
  induction p with
  | leaf =>
      intro hmem hlo hhi
      cases lo with | leaf lo =>
      cases hi with | leaf hi =>
      cases lo' with | leaf lo' =>
      cases hi' with | leaf hi' =>
      cases idx with | leaf idx =>
      rw [HTuple.elementwiseLE_leaf] at hlo hhi
      rw [mem_iff_le_lt, HTuple.elementwiseLE_leaf, HTuple.elementwiseLT_leaf] at hmem ⊢
      exact ⟨_root_.le_trans hlo hmem.1, _root_.lt_of_lt_of_le hmem.2 hhi⟩
  | prod p q hp hq =>
      intro hmem hlo hhi
      cases lo with | prod lo₀ lo₁ =>
      cases hi with | prod hi₀ hi₁ =>
      cases lo' with | prod lo₀' lo₁' =>
      cases hi' with | prod hi₀' hi₁' =>
      cases idx with | prod idx₀ idx₁ =>
      rw [mem_iff_le_lt, HTuple.elementwiseLE_prod, HTuple.elementwiseLT_prod] at hmem ⊢
      rw [HTuple.elementwiseLE_prod] at hlo hhi
      have hleft := mem_iff_le_lt.mp (hp (mem_iff_le_lt.2 ⟨hmem.1.1, hmem.2.1⟩) hlo.1 hhi.1)
      have hright := mem_iff_le_lt.mp (hq (mem_iff_le_lt.2 ⟨hmem.1.2, hmem.2.2⟩) hlo.2 hhi.2)
      exact ⟨⟨hleft.1, hright.1⟩, ⟨hleft.2, hright.2⟩⟩

@[grind_htuple_order →]
theorem nat_lt_of_mem_zero_div {i k d : Nat} (h : i ∈ (0...(k / d))) : i < k := by
  rw [Std.Rco.mem_iff] at h
  change 0 ≤ i ∧ i < k / d at h
  have hdiv : k / d ≤ k := Nat.div_le_self k d
  omega

end Range

end Lexocographic

end HTuple

end NumLean
