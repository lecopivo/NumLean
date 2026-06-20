import NumLean.Algebra.Order
import NumLean.Data.Prod.OrderInit
import Mathlib.Data.Prod.Lex

public section

namespace NumLean

/-
Project-wide product ordering convention.

Within `NumLean`, product `LT` and `LE` instances use row-major lexicographic order: the
first component is compared first, and the second component is compared only when the first
components are equal. This is a project-wide assumption for products imported through this file;
other product order notions are available through `Elementwise*`, `Lex*`, and `Colex*`.
WARNING: importing this file installs these product `LT`/`LE` instances for the project.
-/
namespace Prod

variable {α : Type u} {β : Type v}

instance instElementwiseLT [LT (ElementwiseOrder α)] [LT (ElementwiseOrder β)] :
    LT (ElementwiseOrder (α × β)) where
  lt x y := x.val.1 <ₑ y.val.1 ∧ x.val.2 <ₑ y.val.2

@[simp, grind =, grind_prod_order =]
theorem elementwiseLT_mk [LT (ElementwiseOrder α)] [LT (ElementwiseOrder β)]
    {a c : α} {b d : β} :
    (((a, b) : α × β) <ₑ (c, d)) ↔ a <ₑ c ∧ b <ₑ d := Iff.rfl

instance instElementwiseLE [LE (ElementwiseOrder α)] [LE (ElementwiseOrder β)] :
    LE (ElementwiseOrder (α × β)) where
  le x y := x.val.1 ≤ₑ y.val.1 ∧ x.val.2 ≤ₑ y.val.2

@[simp, grind =, grind_prod_order =]
theorem elementwiseLE_mk [LE (ElementwiseOrder α)] [LE (ElementwiseOrder β)]
    {a c : α} {b d : β} :
    (((a, b) : α × β) ≤ₑ (c, d)) ↔ a ≤ₑ c ∧ b ≤ₑ d := Iff.rfl

instance instLexLT [LT (LexOrder α)] [LT (LexOrder β)] : LT (LexOrder (α × β)) where
  lt x y := x.val.1 <ˡ y.val.1 ∨ (x.val.1 = y.val.1 ∧ x.val.2 <ˡ y.val.2)

@[simp, grind =, grind_prod_order =]
theorem lexLT_mk [LT (LexOrder α)] [LT (LexOrder β)] {a c : α} {b d : β} :
    (((a, b) : α × β) <ˡ (c, d)) ↔ a <ˡ c ∨ (a = c ∧ b <ˡ d) := Iff.rfl

instance instLexLE [LT (LexOrder α)] [LT (LexOrder β)] : LE (LexOrder (α × β)) where
  le x y := x.val = y.val ∨ x.val <ˡ y.val

@[simp, grind =, grind_prod_order =]
theorem lexLE_mk [LT (LexOrder α)] [LT (LexOrder β)] {a c : α} {b d : β} :
    (((a, b) : α × β) ≤ˡ (c, d)) ↔ (a, b) = (c, d) ∨ ((a, b) : α × β) <ˡ (c, d) :=
  Iff.rfl

instance instColexLT [LT (ColexOrder α)] [LT (ColexOrder β)] : LT (ColexOrder (α × β)) where
  lt x y := x.val.2 <ₗ y.val.2 ∨ (x.val.2 = y.val.2 ∧ x.val.1 <ₗ y.val.1)

@[simp, grind =, grind_prod_order =]
theorem colexLT_mk [LT (ColexOrder α)] [LT (ColexOrder β)] {a c : α} {b d : β} :
    (((a, b) : α × β) <ₗ (c, d)) ↔ b <ₗ d ∨ (b = d ∧ a <ₗ c) := Iff.rfl

instance instColexLE [LT (ColexOrder α)] [LT (ColexOrder β)] : LE (ColexOrder (α × β)) where
  le x y := x.val = y.val ∨ x.val <ₗ y.val

@[simp, grind =, grind_prod_order =]
theorem colexLE_mk [LT (ColexOrder α)] [LT (ColexOrder β)] {a c : α} {b d : β} :
    (((a, b) : α × β) ≤ₗ (c, d)) ↔ (a, b) = (c, d) ∨ ((a, b) : α × β) <ₗ (c, d) :=
  Iff.rfl

instance instLT [LT (LexOrder α)] [LT (LexOrder β)] : LT (α × β) where
  lt x y := x <ˡ y

instance instLE [LT (LexOrder α)] [LT (LexOrder β)] : LE (α × β) where
  le x y := x ≤ˡ y

instance instLexOrderLinearOrder [LinearOrder α] [LinearOrder β] :
    LinearOrder (LexOrder (α × β)) :=
  LinearOrder.lift' (fun x : LexOrder (α × β) => toLex x.val) (by
    intro x y h
    cases x
    cases y
    simp only [LexOrder.mk.injEq]
    exact toLex.injective h)

instance instColexOrderLinearOrder [LinearOrder α] [LinearOrder β] :
    LinearOrder (ColexOrder (α × β)) :=
  LinearOrder.lift' (fun x : ColexOrder (α × β) => toLex (x.val.2, x.val.1)) (by
    intro x y h
    cases x with | mk x =>
    cases y with | mk y =>
    have hswap : (x.2, x.1) = (y.2, y.1) := toLex.injective h
    exact congrArg ColexOrder.mk (Prod.ext (congrArg Prod.snd hswap) (congrArg Prod.fst hswap)))

instance instElementwiseOrderPreorder [Preorder (ElementwiseOrder α)] [Preorder (ElementwiseOrder β)] :
    Preorder (ElementwiseOrder (α × β)) where
  le x y := x.val.1 ≤ₑ y.val.1 ∧ x.val.2 ≤ₑ y.val.2
  lt x y := (x.val.1 ≤ₑ y.val.1 ∧ x.val.2 ≤ₑ y.val.2) ∧
    ¬ (y.val.1 ≤ₑ x.val.1 ∧ y.val.2 ≤ₑ x.val.2)
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ hxy hyz := ⟨le_trans hxy.1 hyz.1, le_trans hxy.2 hyz.2⟩
  lt_iff_le_not_ge _ _ := Iff.rfl

@[simp, grind =, grind_prod_order =]
theorem lt_mk [LT (LexOrder α)] [LT (LexOrder β)] {a c : α} {b d : β} :
    (((a, b) : α × β) < (c, d)) ↔ a <ˡ c ∨ (a = c ∧ b <ˡ d) := Iff.rfl

@[simp, grind =, grind_prod_order =]
theorem le_mk [LT (LexOrder α)] [LT (LexOrder β)] {a c : α} {b d : β} :
    (((a, b) : α × β) ≤ (c, d)) ↔ (a, b) = (c, d) ∨ a <ˡ c ∨ (a = c ∧ b <ˡ d) := by
  rfl

end Prod

end NumLean
