import Mathlib


structure Vec3 (R : Type) where
  (x y z : R)

#check ForIn

/-- As is effectivelly `Array A` -/
class ArrayType (As : Type u) (A : outParam (Type w)) where
  size : As → Nat
  usize : As → UInt64

  uget (xs : As) (i : UInt64) (h : i.toNat < size xs) : A
  get  (xs : As) (i : Nat) (h : i < size xs) : A

  uset (xs : As) (i : UInt64) (v : α) (h : i.toNat < size xs) : A
  set (xs : As) (i : Nat) (v : α) (h : i < size xs) : As


structure Idx

class IndexType (ι : Type u) extends Fintype ι where
  to

variable {R : Type} {Vec : Type → Nat → Type} -- [Scalar R] [VectorType Vec]

def addVectors (x y : Vec (Vec3 R) 10) : Vec (Vec3 R) 10 := Id.run do

  for i in [0:10] do
    x[i] += y[i]

  return x



theorem addVectors_linear : IsLinearMap ℝ fun xy : Fin 10 → (Vec3 ℝ) => addVectors xy.1 xy.2 := sorry
