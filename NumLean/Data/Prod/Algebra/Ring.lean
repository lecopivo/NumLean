import NumLean.Interfaces.Algebra.Ring.Lawful
import NumLean.Data.Prod.Algebra.Group
import Mathlib.Algebra.Notation.Prod

set_option linter.unusedSimpArgs false

namespace NumLean
namespace Interfaces
namespace Algebra

instance {A B : Type _} [SemiringOps A] [SemiringOps B] : SemiringOps (A × B) where
  nsmul n a := ⟨AddMonoidOps.nsmul n a.1, AddMonoidOps.nsmul n a.2⟩
  npow n a := ⟨MonoidOps.npow n a.1, MonoidOps.npow n a.2⟩
  natCast n := ⟨Nat.cast n, Nat.cast n⟩

instance {A B : Type _} [SemiringOps A] [LawfulSemiringOps A]
    [SemiringOps B] [LawfulSemiringOps B] : LawfulSemiringOps (A × B) where
  add_assoc a b c := by ext <;> simp [LawfulAddMonoidOps.add_assoc]
  zero_add a := by ext <;> simp [LawfulAddMonoidOps.zero_add]
  add_zero a := by ext <;> simp [LawfulAddMonoidOps.add_zero]
  nsmul_zero a := by ext <;> simp [LawfulAddMonoidOps.nsmul_zero]
  nsmul_succ n a := by ext <;> simp [LawfulAddMonoidOps.nsmul_succ]
  add_comm a b := by ext <;> simp [LawfulAddMonoidOps.add_comm]
  mul_assoc a b c := by ext <;> simp [LawfulMonoidOps.mul_assoc]
  one_mul a := by ext <;> simp [LawfulMonoidOps.one_mul]
  mul_one a := by ext <;> simp [LawfulMonoidOps.mul_one]
  npow_zero a := by ext <;> simp [LawfulMonoidOps.npow_zero]
  npow_succ n a := by ext <;> simp [LawfulMonoidOps.npow_succ]
  mul_comm a b := by ext <;> simp [LawfulMonoidOps.mul_comm]
  zero_mul a := by ext <;> simp [LawfulSemiringOps.zero_mul]
  mul_zero a := by ext <;> simp [LawfulSemiringOps.mul_zero]
  left_distrib a b c := by ext <;> simp [LawfulSemiringOps.left_distrib]
  right_distrib a b c := by ext <;> simp [LawfulSemiringOps.right_distrib]
  natCast_zero := by
    ext
    · exact (LawfulSemiringOps.natCast_zero (K := A))
    · exact (LawfulSemiringOps.natCast_zero (K := B))
  natCast_succ n := by
    ext
    · exact (LawfulSemiringOps.natCast_succ (K := A) n)
    · exact (LawfulSemiringOps.natCast_succ (K := B) n)

instance {A B : Type _} [RingOps A] [RingOps B] : RingOps (A × B) where
  intCast n := ⟨Int.cast n, Int.cast n⟩

instance {A B : Type _} [RingOps A] [LawfulRingOps A]
    [RingOps B] [LawfulRingOps B] : LawfulRingOps (A × B) where
  add_assoc a b c := by ext <;> simp [LawfulAddMonoidOps.add_assoc]
  zero_add a := by ext <;> simp [LawfulAddMonoidOps.zero_add]
  add_zero a := by ext <;> simp [LawfulAddMonoidOps.add_zero]
  nsmul_zero a := by ext <;> simp [LawfulAddMonoidOps.nsmul_zero]
  nsmul_succ n a := by ext <;> simp [LawfulAddMonoidOps.nsmul_succ]
  add_comm a b := by ext <;> simp [LawfulAddMonoidOps.add_comm]
  mul_assoc a b c := by ext <;> simp [LawfulMonoidOps.mul_assoc]
  one_mul a := by ext <;> simp [LawfulMonoidOps.one_mul]
  mul_one a := by ext <;> simp [LawfulMonoidOps.mul_one]
  npow_zero a := by ext <;> simp [LawfulMonoidOps.npow_zero]
  npow_succ n a := by ext <;> simp [LawfulMonoidOps.npow_succ]
  mul_comm a b := by ext <;> simp [LawfulMonoidOps.mul_comm]
  zero_mul a := by ext <;> simp [LawfulSemiringOps.zero_mul]
  mul_zero a := by ext <;> simp [LawfulSemiringOps.mul_zero]
  left_distrib a b c := by ext <;> simp [LawfulSemiringOps.left_distrib]
  right_distrib a b c := by ext <;> simp [LawfulSemiringOps.right_distrib]
  natCast_zero := by
    ext
    · exact (LawfulSemiringOps.natCast_zero (K := A))
    · exact (LawfulSemiringOps.natCast_zero (K := B))
  natCast_succ n := by
    ext
    · exact (LawfulSemiringOps.natCast_succ (K := A) n)
    · exact (LawfulSemiringOps.natCast_succ (K := B) n)
  sub_eq_add_neg a b := by ext <;> simp [LawfulAddGroupOps.sub_eq_add_neg]
  zsmul_zero a := by ext <;> simp [LawfulAddGroupOps.zsmul_zero]
  zsmul_succ n a := by
    ext
    · exact (LawfulAddGroupOps.zsmul_succ (K := A) n a.1)
    · exact (LawfulAddGroupOps.zsmul_succ (K := B) n a.2)
  zsmul_neg n a := by ext <;> simp [LawfulAddGroupOps.zsmul_neg]
  neg_add_cancel a := by ext <;> simp [LawfulAddGroupOps.neg_add_cancel]
  intCast_ofNat n := by
    ext
    · exact (LawfulRingOps.intCast_ofNat (K := A) n)
    · exact (LawfulRingOps.intCast_ofNat (K := B) n)
  intCast_negSucc n := by
    ext
    · exact (LawfulRingOps.intCast_negSucc (K := A) n)
    · exact (LawfulRingOps.intCast_negSucc (K := B) n)

example {A B : Type _} [CommSemiring A] [CommSemiring B] :
    (instCommSemiringOfOps : CommSemiring (A × B)) =
      (inferInstance : CommSemiring (A × B)) :=
  rfl

example {A B : Type _} [CommRing A] [CommRing B] :
    (instCommRingOfOps : CommRing (A × B)) = (inferInstance : CommRing (A × B)) :=
  rfl

end Algebra
end Interfaces
end NumLean
