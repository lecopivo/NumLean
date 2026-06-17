namespace NumLean

/-- Lexicographic strict order. -/
class LexLT (α : Type u) where
  lexLT : α → α → Prop

/-- Lexicographic non-strict order. -/
class LexLE (α : Type u) where
  lexLE : α → α → Prop

/-- Colexicographic strict order. -/
class ColexLT (α : Type u) where
  colexLT : α → α → Prop

/-- Colexicographic non-strict order. -/
class ColexLE (α : Type u) where
  colexLE : α → α → Prop

/-- Elementwise strict order. -/
class ElementwiseLT (α : Type u) where
  elementwiseLT : α → α → Prop

/-- Elementwise non-strict order. -/
class ElementwiseLE (α : Type u) where
  elementwiseLE : α → α → Prop

infix:50 " <ˡ " => LexLT.lexLT
infix:50 " ≤ˡ " => LexLE.lexLE
infix:50 " <ₗ " => ColexLT.colexLT
infix:50 " ≤ₗ " => ColexLE.colexLE
infix:50 " <ₑ " => ElementwiseLT.elementwiseLT
infix:50 " ≤ₑ " => ElementwiseLE.elementwiseLE

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
