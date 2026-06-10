import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.ProxyType
import NumLean.Interfaces.FlatRepr.Basic

namespace NumLean

/-- This function moves `FlatRepr` instance from `X` to `Y` along an equivalence.

This function is manly used to derive an instance of FlatRepr for structures. -/
@[inline]
def FlatRepr.ofEquiv (K) (equiv : X ≃ Y) [inst : FlatRepr X K n] : FlatRepr Y K n where
  toVector y := toVector K (equiv.symm y)
  fromVector v := equiv (fromVector X v)
  left_inv := by intro _; simp
  right_inv := by intro _; simp
  getComp y i h := getComp K (equiv.symm y) i h
  getComp_spec := by intros; simp [inst.getComp_spec]
  setComp y i k h := equiv (setComp (equiv.symm y) i k h)
  setComp_spec := by intros; simp [inst.setComp_spec]


end NumLean
