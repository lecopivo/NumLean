import NumLean.Algebra.Order
import NumLean.Data.Vector.Basic

namespace Vector

variable {α : Type u} {n : Nat}

instance [One α] : One (Vector α n) where
  one := Vector.replicate n 1

attribute [instance] Vector.instMul

attribute [simp] Vector.getElem_mul

@[simp] theorem getElem_instOne [One α] (i : Nat) (h : i < n) :
    (1 : Vector α n)[i] = 1 := by
  change (Vector.replicate n 1)[i] = 1
  exact Vector.getElem_replicate h

/-- Elementwise strict order on vectors. -/
instance [LT α] : NumLean.ElementwiseLT (Vector α n) where
  elementwiseLT x y := ∀ i : Fin n, x[i] < y[i]

/-- Elementwise non-strict order on vectors. -/
instance [LE α] : NumLean.ElementwiseLE (Vector α n) where
  elementwiseLE x y := ∀ i : Fin n, x[i] ≤ y[i]

/-- Lexicographic strict order on vectors. -/
instance [LT α] : NumLean.LexLT (Vector α n) where
  lexLT x y := ∃ i : Fin n, x[i] < y[i] ∧
    ∀ j : Fin n, j.1 < i.1 → x[j] = y[j]

/-- Lexicographic non-strict order on vectors. -/
instance [LT α] : NumLean.LexLE (Vector α n) where
  lexLE x y := x = y ∨ NumLean.LexLT.lexLT x y

/-- Colexicographic strict order on vectors. -/
instance [LT α] : NumLean.ColexLT (Vector α n) where
  colexLT x y := ∃ i : Fin n, x[i] < y[i] ∧
    ∀ j : Fin n, i.1 < j.1 → x[j] = y[j]

/-- Colexicographic non-strict order on vectors. -/
instance [LT α] : NumLean.ColexLE (Vector α n) where
  colexLE x y := x = y ∨ NumLean.ColexLT.colexLT x y

end Vector
