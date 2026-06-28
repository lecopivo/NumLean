module

public import NumLean.Data.Vector.Ops
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Ring.Basic

@[expose] public section

namespace Vector

variable {α : Type u} {R : Type v} {n : Nat}

/-- Pointwise natural powers. -/
def npow [Pow α Nat] (k : Nat) (x : Vector α n) : Vector α n :=
  x.map fun a => a ^ k

instance instNumLeanSemigroup [Semigroup α] : Semigroup (Vector α n) where
  mul_assoc x y z := by ext; simp; ac_rfl

instance instNumLeanCommSemigroup [CommSemigroup α] : CommSemigroup (Vector α n) where
  mul_comm x y := by ext; simp; ac_rfl

instance instNumLeanMonoid [Monoid α] : Monoid (Vector α n) where
  npow := Vector.npow
  one_mul x := by ext; simp
  mul_one x := by ext; simp
  npow_zero x := by ext; simp [Vector.npow]
  npow_succ k x := by ext; simp [Vector.npow, pow_succ]

instance instNumLeanCommMonoid [CommMonoid α] : CommMonoid (Vector α n) where
  mul_comm x y := by ext; simp; ac_rfl

instance instNumLeanAddCommMonoid [AddCommMonoid α] : AddCommMonoid (Vector α n) where
  nsmul := (· • ·)
  add_assoc x y z := by ext; simp; ac_rfl
  zero_add x := by ext; simp
  add_zero x := by ext; simp
  nsmul_zero x := by ext; simp
  nsmul_succ k x := by ext; simp [succ_nsmul]
  add_comm x y := by ext; simp; ac_rfl

instance instNumLeanAddCommGroup [AddCommGroup α] : AddCommGroup (Vector α n) where
  zsmul := (· • ·)
  neg_add_cancel x := by ext; simp
  sub_eq_add_neg x y := by
    ext i hi
    simpa using _root_.sub_eq_add_neg x[i] y[i]
  zsmul_zero' x := by ext; simp
  zsmul_succ' k x := by
    ext i hi
    simpa [add_comm] using SubNegMonoid.zsmul_succ' k x[i]
  zsmul_neg' k x := by
    ext i hi
    simpa using SubNegMonoid.zsmul_neg' k x[i]

instance instNumLeanModule [Semiring R] [AddCommMonoid α] [Module R α] : Module R (Vector α n) where
  smul := (· • ·)
  one_smul x := by ext; simp
  mul_smul r s x := by ext; simp [SemigroupAction.mul_smul]
  smul_zero r := by ext; simp
  smul_add r x y := by
    ext i hi
    simpa using _root_.smul_add r x[i] y[i]
  add_smul r s x := by
    ext i hi
    simpa using _root_.add_smul r s x[i]
  zero_smul x := by ext; simp

instance instNumLeanSemiring [Semiring α] : Semiring (Vector α n) where
  left_distrib x y z := by
    ext i hi
    simpa using _root_.left_distrib x[i] y[i] z[i]
  right_distrib x y z := by
    ext i hi
    simpa using _root_.right_distrib x[i] y[i] z[i]
  zero_mul x := by ext; simp
  mul_zero x := by ext; simp

instance instNumLeanCommSemiring [CommSemiring α] : CommSemiring (Vector α n) where
  mul_comm x y := by ext; simp; ac_rfl

instance instNumLeanRing [Ring α] : Ring (Vector α n) where

end Vector
