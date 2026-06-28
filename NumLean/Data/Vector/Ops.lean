module

public import NumLean.Interfaces.Order
public import NumLean.Data.Vector.Basic

@[expose] public section

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
instance [LT α] : LT (NumLean.ElementwiseOrder (Vector α n)) where
  lt x y := ∀ i : Fin n, x.val[i] < y.val[i]

/-- Elementwise non-strict order on vectors. -/
instance [LE α] : LE (NumLean.ElementwiseOrder (Vector α n)) where
  le x y := ∀ i : Fin n, x.val[i] ≤ y.val[i]

/-- Lexicographic strict order on vectors. -/
instance [LT α] : LT (NumLean.LexOrder (Vector α n)) where
  lt x y := ∃ i : Fin n, x.val[i] < y.val[i] ∧
    ∀ j : Fin n, j.1 < i.1 → x.val[j] = y.val[j]

/-- Lexicographic non-strict order on vectors. -/
instance [LT α] : LE (NumLean.LexOrder (Vector α n)) where
  le x y := x.val = y.val ∨ x.val <ˡ y.val

/-- Colexicographic strict order on vectors. -/
instance [LT α] : LT (NumLean.ColexOrder (Vector α n)) where
  lt x y := ∃ i : Fin n, x.val[i] < y.val[i] ∧
    ∀ j : Fin n, i.1 < j.1 → x.val[j] = y.val[j]

/-- Colexicographic non-strict order on vectors. -/
instance [LT α] : LE (NumLean.ColexOrder (Vector α n)) where
  le x y := x.val = y.val ∨ x.val <ₗ y.val

end Vector
