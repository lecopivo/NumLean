import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.ProxyType
import NumLean.Interfaces.HasFlatRepr.Basic

namespace NumLean

/-- Move a `HasFlatRepr` instance from `X` to `Y` along an equivalence.

This is intended to support derived instances for structures and representation-equivalent
types during the migration from `FlatRepr`/`HasFlatVector`. -/
@[reducible, inline]
def HasFlatRepr.ofEquiv (Ks : Nat → Type v) (equiv : X ≃ Y)
    [VectorType Ks K] [inst : HasFlatRepr X Ks n] : HasFlatRepr Y Ks n where
  toVector y := HasFlatRepr.toVector (Ks := Ks) (equiv.symm y)
  fromVector v := equiv (HasFlatRepr.fromVector (Ks := Ks) (X := X) v)
  left_inv := by
    intro y
    change equiv (HasFlatRepr.fromVector (Ks := Ks) (HasFlatRepr.toVector (Ks := Ks) (equiv.symm y))) = y
    rw [HasFlatRepr.fromVector_toVector]
    exact equiv.apply_symm_apply y
  right_inv := by
    intro v
    change HasFlatRepr.toVector (Ks := Ks) (equiv.symm (equiv (HasFlatRepr.fromVector (Ks := Ks) (X := X) v))) = v
    rw [Equiv.symm_apply_apply, HasFlatRepr.toVector_fromVector]
  getComp y i h := HasFlatRepr.getComp (Ks := Ks) (equiv.symm y) i h
  getComp_spec := by
    intro y i h
    simp [inst.getComp_spec]
  setComp y i k h := equiv (HasFlatRepr.setComp (Ks := Ks) (equiv.symm y) i k h)
  setComp_spec := by
    intro y i k h
    simp [inst.setComp_spec]
  get ks off h := equiv (HasFlatRepr.get (X := X) ks off h)
  getComp_get_eq_vector_get := by
    intro n ks off i hoff hi
    rw [Equiv.symm_apply_apply]
    exact inst.getComp_get_eq_vector_get ks off i hoff hi
  set ks off y h := HasFlatRepr.set (X := X) ks off (equiv.symm y) h
  vector_get_set_eq := by
    intro n ks off i y hoff hi
    exact inst.vector_get_set_eq ks off i (equiv.symm y) hoff hi
  vector_get_set_ne := by
    intro n ks off i y hoff hi hi'
    exact inst.vector_get_set_ne ks off i (equiv.symm y) hoff hi hi'
  push ks y := HasFlatRepr.push (X := X) ks (equiv.symm y)
  vector_get_push_lt := by
    intro n ks y i hi
    exact inst.vector_get_push_lt ks (equiv.symm y) i hi
  vector_get_push_eq := by
    intro n ks y i hi
    exact inst.vector_get_push_eq ks (equiv.symm y) i hi
  toFlatVector y := HasFlatRepr.toFlatVector (Ks := Ks) (equiv.symm y)
  get_toFlatVector_eq_getComp := by
    intro y i h
    exact inst.get_toFlatVector_eq_getComp (equiv.symm y) i h
  replicate n y := HasFlatRepr.replicate (Ks := Ks) n (equiv.symm y)
  get_replicate := by
    intro n y i j hi hj
    exact inst.get_replicate n (equiv.symm y) i j hi hj

end NumLean
