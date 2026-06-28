module

public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.UInt

@[expose] public section

namespace NumLean

/-- Wrapper selecting NumLean's lexicographic order as the standard order on a type. -/
structure LexOrder (α : Type u) where
  val : α
  deriving DecidableEq, Repr

/-- Wrapper selecting NumLean's colexicographic order as the standard order on a type. -/
structure ColexOrder (α : Type u) where
  val : α
  deriving DecidableEq, Repr

/-- Wrapper selecting NumLean's elementwise order as the standard order on a type. -/
structure ElementwiseOrder (α : Type u) where
  val : α
  deriving DecidableEq, Repr

namespace LexOrder

/-- Transfer an existing linear order to the lexicographic-order wrapper. -/
@[reducible]
def linearOrderOf [LinearOrder α] : LinearOrder (LexOrder α) where
  le x y := x.val ≤ y.val
  lt x y := x.val < y.val
  le_refl x := le_rfl
  le_trans x y z hxy hyz := le_trans hxy hyz
  lt_iff_le_not_ge x y := lt_iff_le_not_ge
  le_antisymm x y hxy hyx := by
    cases x
    cases y
    simp only [mk.injEq]
    exact le_antisymm hxy hyx
  le_total x y := le_total x.val y.val
  toDecidableLE x y := inferInstanceAs (Decidable (x.val ≤ y.val))
  toDecidableLT x y := inferInstanceAs (Decidable (x.val < y.val))

/-- Transfer an existing strict order to the lexicographic-order wrapper. -/
@[reducible]
def ltOf [LT α] : LT (LexOrder α) where
  lt x y := x.val < y.val

/-- Transfer an existing non-strict order to the lexicographic-order wrapper. -/
@[reducible]
def leOf [LE α] : LE (LexOrder α) where
  le x y := x.val ≤ y.val

end LexOrder

namespace ColexOrder

/-- Transfer an existing linear order to the colexicographic-order wrapper. -/
@[reducible]
def linearOrderOf [LinearOrder α] : LinearOrder (ColexOrder α) where
  le x y := x.val ≤ y.val
  lt x y := x.val < y.val
  le_refl x := le_rfl
  le_trans x y z hxy hyz := le_trans hxy hyz
  lt_iff_le_not_ge x y := lt_iff_le_not_ge
  le_antisymm x y hxy hyx := by
    cases x
    cases y
    simp only [mk.injEq]
    exact le_antisymm hxy hyx
  le_total x y := le_total x.val y.val
  toDecidableLE x y := inferInstanceAs (Decidable (x.val ≤ y.val))
  toDecidableLT x y := inferInstanceAs (Decidable (x.val < y.val))

/-- Transfer an existing strict order to the colexicographic-order wrapper. -/
@[reducible]
def ltOf [LT α] : LT (ColexOrder α) where
  lt x y := x.val < y.val

/-- Transfer an existing non-strict order to the colexicographic-order wrapper. -/
@[reducible]
def leOf [LE α] : LE (ColexOrder α) where
  le x y := x.val ≤ y.val

end ColexOrder

namespace ElementwiseOrder

/-- Transfer an existing linear order to the elementwise-order wrapper. -/
@[reducible]
def linearOrderOf [LinearOrder α] : LinearOrder (ElementwiseOrder α) where
  le x y := x.val ≤ y.val
  lt x y := x.val < y.val
  le_refl x := le_rfl
  le_trans x y z hxy hyz := le_trans hxy hyz
  lt_iff_le_not_ge x y := lt_iff_le_not_ge
  le_antisymm x y hxy hyx := by
    cases x
    cases y
    simp only [mk.injEq]
    exact le_antisymm hxy hyx
  le_total x y := le_total x.val y.val
  toDecidableLE x y := inferInstanceAs (Decidable (x.val ≤ y.val))
  toDecidableLT x y := inferInstanceAs (Decidable (x.val < y.val))

/-- Transfer an existing strict order to the elementwise-order wrapper. -/
@[reducible]
def ltOf [LT α] : LT (ElementwiseOrder α) where
  lt x y := x.val < y.val

/-- Transfer an existing non-strict order to the elementwise-order wrapper. -/
@[reducible]
def leOf [LE α] : LE (ElementwiseOrder α) where
  le x y := x.val ≤ y.val

end ElementwiseOrder

def lexLT {α} [LT (LexOrder α)] (x y : α) : Prop := LexOrder.mk x < LexOrder.mk y
def lexLE {α} [LE (LexOrder α)] (x y : α) : Prop := LexOrder.mk x ≤ LexOrder.mk y

def colexLT {α} [LT (ColexOrder α)] (x y : α) : Prop := ColexOrder.mk x < ColexOrder.mk y
def colexLE {α} [LE (ColexOrder α)] (x y : α) : Prop := ColexOrder.mk x ≤ ColexOrder.mk y

def elementwiseLT {α} [LT (ElementwiseOrder α)] (x y : α) : Prop :=
    ElementwiseOrder.mk x < ElementwiseOrder.mk y
def elementwiseLE {α} [LE (ElementwiseOrder α)] (x y : α) : Prop :=
    ElementwiseOrder.mk x ≤ ElementwiseOrder.mk y

infix:50 " <ˡ " => lexLT
infix:50 " ≤ˡ " => lexLE
infix:50 " <ₗ " => colexLT
infix:50 " ≤ₗ " => colexLE
infix:50 " <ₑ " => elementwiseLT
infix:50 " ≤ₑ " => elementwiseLE

instance : CoeOut (LexOrder α) α where
  coe x := x.val

@[grind =]
theorem lexLT_iff_mk_lt {α} [LT (LexOrder α)] (a b : α) :
    (a <ˡ b) ↔ (LexOrder.mk a < LexOrder.mk b) := by trivial

@[grind =]
theorem lexLE_iff_mk_le {α} [LE (LexOrder α)] (a b : α) :
    (a ≤ˡ b) ↔ (LexOrder.mk a ≤ LexOrder.mk b) := by trivial

@[grind =]
theorem colexLT_iff_mk_lt {α} [LT (ColexOrder α)] (a b : α) :
    (a <ₗ b) ↔ (ColexOrder.mk a < ColexOrder.mk b) := by trivial

@[grind =]
theorem colexLE_iff_mk_le {α} [LE (ColexOrder α)] (a b : α) :
    (a ≤ₗ b) ↔ (ColexOrder.mk a ≤ ColexOrder.mk b) := by trivial

@[grind =]
theorem elementwiseLT_iff_mk_lt {α} [LT (ElementwiseOrder α)] (a b : α) :
    (a <ₑ b) ↔ (ElementwiseOrder.mk a < ElementwiseOrder.mk b) := by trivial

@[grind =]
theorem elementwiseLE_iff_mk_le {α} [LE (ElementwiseOrder α)] (a b : α) :
    (a ≤ₑ b) ↔ (ElementwiseOrder.mk a ≤ ElementwiseOrder.mk b) := by trivial

section CoreScalarInstances

instance : LinearOrder (LexOrder Nat) := LexOrder.linearOrderOf
instance : LinearOrder (ColexOrder Nat) := ColexOrder.linearOrderOf
instance : LinearOrder (ElementwiseOrder Nat) := ElementwiseOrder.linearOrderOf

instance : LinearOrder (LexOrder Int) := LexOrder.linearOrderOf
instance : LinearOrder (ColexOrder Int) := ColexOrder.linearOrderOf
instance : LinearOrder (ElementwiseOrder Int) := ElementwiseOrder.linearOrderOf

instance : LT (LexOrder UInt8) := LexOrder.ltOf
instance : LE (LexOrder UInt8) := LexOrder.leOf
instance : DecidableLT (LexOrder UInt8) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (LexOrder UInt8) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ColexOrder UInt8) := ColexOrder.ltOf
instance : LE (ColexOrder UInt8) := ColexOrder.leOf
instance : DecidableLT (ColexOrder UInt8) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ColexOrder UInt8) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ElementwiseOrder UInt8) := ElementwiseOrder.ltOf
instance : LE (ElementwiseOrder UInt8) := ElementwiseOrder.leOf
instance : DecidableLT (ElementwiseOrder UInt8) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ElementwiseOrder UInt8) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))

instance : LT (LexOrder UInt16) := LexOrder.ltOf
instance : LE (LexOrder UInt16) := LexOrder.leOf
instance : DecidableLT (LexOrder UInt16) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (LexOrder UInt16) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ColexOrder UInt16) := ColexOrder.ltOf
instance : LE (ColexOrder UInt16) := ColexOrder.leOf
instance : DecidableLT (ColexOrder UInt16) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ColexOrder UInt16) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ElementwiseOrder UInt16) := ElementwiseOrder.ltOf
instance : LE (ElementwiseOrder UInt16) := ElementwiseOrder.leOf
instance : DecidableLT (ElementwiseOrder UInt16) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ElementwiseOrder UInt16) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))

instance : LT (LexOrder UInt32) := LexOrder.ltOf
instance : LE (LexOrder UInt32) := LexOrder.leOf
instance : DecidableLT (LexOrder UInt32) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (LexOrder UInt32) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ColexOrder UInt32) := ColexOrder.ltOf
instance : LE (ColexOrder UInt32) := ColexOrder.leOf
instance : DecidableLT (ColexOrder UInt32) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ColexOrder UInt32) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ElementwiseOrder UInt32) := ElementwiseOrder.ltOf
instance : LE (ElementwiseOrder UInt32) := ElementwiseOrder.leOf
instance : DecidableLT (ElementwiseOrder UInt32) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ElementwiseOrder UInt32) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))

instance : LT (LexOrder UInt64) := LexOrder.ltOf
instance : LE (LexOrder UInt64) := LexOrder.leOf
instance : DecidableLT (LexOrder UInt64) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (LexOrder UInt64) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ColexOrder UInt64) := ColexOrder.ltOf
instance : LE (ColexOrder UInt64) := ColexOrder.leOf
instance : DecidableLT (ColexOrder UInt64) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ColexOrder UInt64) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ElementwiseOrder UInt64) := ElementwiseOrder.ltOf
instance : LE (ElementwiseOrder UInt64) := ElementwiseOrder.leOf
instance : DecidableLT (ElementwiseOrder UInt64) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ElementwiseOrder UInt64) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))

instance : LT (LexOrder USize) := LexOrder.ltOf
instance : LE (LexOrder USize) := LexOrder.leOf
instance : DecidableLT (LexOrder USize) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (LexOrder USize) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ColexOrder USize) := ColexOrder.ltOf
instance : LE (ColexOrder USize) := ColexOrder.leOf
instance : DecidableLT (ColexOrder USize) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ColexOrder USize) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ElementwiseOrder USize) := ElementwiseOrder.ltOf
instance : LE (ElementwiseOrder USize) := ElementwiseOrder.leOf
instance : DecidableLT (ElementwiseOrder USize) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ElementwiseOrder USize) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))

instance : LT (LexOrder Int8) := LexOrder.ltOf
instance : LE (LexOrder Int8) := LexOrder.leOf
instance : DecidableLT (LexOrder Int8) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (LexOrder Int8) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ColexOrder Int8) := ColexOrder.ltOf
instance : LE (ColexOrder Int8) := ColexOrder.leOf
instance : DecidableLT (ColexOrder Int8) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ColexOrder Int8) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ElementwiseOrder Int8) := ElementwiseOrder.ltOf
instance : LE (ElementwiseOrder Int8) := ElementwiseOrder.leOf
instance : DecidableLT (ElementwiseOrder Int8) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ElementwiseOrder Int8) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))

instance : LT (LexOrder Int16) := LexOrder.ltOf
instance : LE (LexOrder Int16) := LexOrder.leOf
instance : DecidableLT (LexOrder Int16) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (LexOrder Int16) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ColexOrder Int16) := ColexOrder.ltOf
instance : LE (ColexOrder Int16) := ColexOrder.leOf
instance : DecidableLT (ColexOrder Int16) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ColexOrder Int16) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ElementwiseOrder Int16) := ElementwiseOrder.ltOf
instance : LE (ElementwiseOrder Int16) := ElementwiseOrder.leOf
instance : DecidableLT (ElementwiseOrder Int16) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ElementwiseOrder Int16) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))

instance : LT (LexOrder Int32) := LexOrder.ltOf
instance : LE (LexOrder Int32) := LexOrder.leOf
instance : DecidableLT (LexOrder Int32) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (LexOrder Int32) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ColexOrder Int32) := ColexOrder.ltOf
instance : LE (ColexOrder Int32) := ColexOrder.leOf
instance : DecidableLT (ColexOrder Int32) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ColexOrder Int32) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ElementwiseOrder Int32) := ElementwiseOrder.ltOf
instance : LE (ElementwiseOrder Int32) := ElementwiseOrder.leOf
instance : DecidableLT (ElementwiseOrder Int32) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ElementwiseOrder Int32) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))

instance : LT (LexOrder Int64) := LexOrder.ltOf
instance : LE (LexOrder Int64) := LexOrder.leOf
instance : DecidableLT (LexOrder Int64) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (LexOrder Int64) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ColexOrder Int64) := ColexOrder.ltOf
instance : LE (ColexOrder Int64) := ColexOrder.leOf
instance : DecidableLT (ColexOrder Int64) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ColexOrder Int64) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ElementwiseOrder Int64) := ElementwiseOrder.ltOf
instance : LE (ElementwiseOrder Int64) := ElementwiseOrder.leOf
instance : DecidableLT (ElementwiseOrder Int64) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ElementwiseOrder Int64) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))

instance : LT (LexOrder Float) := LexOrder.ltOf
instance : LE (LexOrder Float) := LexOrder.leOf
instance : DecidableLT (LexOrder Float) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (LexOrder Float) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ColexOrder Float) := ColexOrder.ltOf
instance : LE (ColexOrder Float) := ColexOrder.leOf
instance : DecidableLT (ColexOrder Float) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ColexOrder Float) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ElementwiseOrder Float) := ElementwiseOrder.ltOf
instance : LE (ElementwiseOrder Float) := ElementwiseOrder.leOf
instance : DecidableLT (ElementwiseOrder Float) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ElementwiseOrder Float) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))

instance : LT (LexOrder Float32) := LexOrder.ltOf
instance : LE (LexOrder Float32) := LexOrder.leOf
instance : DecidableLT (LexOrder Float32) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (LexOrder Float32) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ColexOrder Float32) := ColexOrder.ltOf
instance : LE (ColexOrder Float32) := ColexOrder.leOf
instance : DecidableLT (ColexOrder Float32) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ColexOrder Float32) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))
instance : LT (ElementwiseOrder Float32) := ElementwiseOrder.ltOf
instance : LE (ElementwiseOrder Float32) := ElementwiseOrder.leOf
instance : DecidableLT (ElementwiseOrder Float32) := fun x y => inferInstanceAs (Decidable (x.val < y.val))
instance : DecidableLE (ElementwiseOrder Float32) := fun x y => inferInstanceAs (Decidable (x.val ≤ y.val))

end CoreScalarInstances

namespace ColexOrder

instance : CoeOut (ColexOrder α) α where
  coe x := x.val

end ColexOrder

namespace ElementwiseOrder

instance : CoeOut (ElementwiseOrder α) α where
  coe x := x.val

end ElementwiseOrder

namespace List

/-- Strict lexicographic order on lists. -/
def lexLT [LT α] : List α → List α → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x < y ∨ (x = y ∧ lexLT xs ys)

/-- Non-strict lexicographic order on lists. -/
def lexLE [LT α] (xs ys : List α) : Prop :=
  xs = ys ∨ lexLT xs ys

/-- Strict colexicographic order on lists. -/
def colexLT [LT α] (xs ys : List α) : Prop :=
  lexLT xs.reverse ys.reverse

/-- Non-strict colexicographic order on lists. -/
def colexLE [LT α] (xs ys : List α) : Prop :=
  xs = ys ∨ colexLT xs ys

/-- Strict elementwise order on lists. -/
inductive elementwiseLT [LT α] : List α → List α → Prop where
  | nil : elementwiseLT [] []
  | cons {x y : α} {xs ys : List α} : x < y → elementwiseLT xs ys → elementwiseLT (x :: xs) (y :: ys)

/-- Non-strict elementwise order on lists. -/
inductive elementwiseLE [LE α] : List α → List α → Prop where
  | nil : elementwiseLE [] []
  | cons {x y : α} {xs ys : List α} : x ≤ y → elementwiseLE xs ys → elementwiseLE (x :: xs) (y :: ys)

end List

end NumLean
