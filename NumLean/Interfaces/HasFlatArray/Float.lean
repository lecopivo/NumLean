import NumLean.Interfaces.HasFlatArray.Basic
import NumLean.Interfaces.ArrayOps.FloatArray

namespace NumLean

instance : HasDefaultFlatArray Float FloatArray 1 where
  get xs i h := xs[i]

  getComp_get_eq_array_get := by
    intros _ _ i _ _
    have h : i = 0 := by grind
    simp [h]; rfl

  set xs i x h := xs.set i x h

  size_set := by intro ⟨ks⟩ _ _ _; simp [ArrayOps.size, FloatArray.set, FloatArray.size]
  array_get_set_eq := by
    intro ⟨ks⟩ off i _ _ _
    simp [ArrayOps.get, FloatArray.get, FloatArray.set, FlatRepr.getComp]
    have h : i = off := by grind
    simp [h]
  array_get_set_ne := by
    intro ⟨ks⟩ off i _ _ _ _
    simp [ArrayOps.get, FloatArray.get, FloatArray.set]
    grind

  push xs x := xs.push x
  size_push := by
    intro ⟨ks⟩ _
    simp [ArrayOps.size, FloatArray.size, FloatArray.push, Array.size_push]
  array_get_push_lt := by
    intro ⟨ks⟩ x i hi
    simpa [ArrayOps.get, FloatArray.get, FloatArray.push] using Array.getElem_push_lt (xs := ks) (x := x) hi
  array_get_push_eq := by
    intro ⟨ks⟩ x i hi
    have h : i = 0 := by grind
    subst h
    change (ks.push x)[ks.size] = x
    exact Array.getElem_push_eq (xs := ks) (x := x)

  toArray x := (FloatArray.emptyWithCapacity 1).push x
  size_toArray := by intro ⟨xs⟩; cbv
  get_toArray_eq_getComp := by
    intro x i h;
    have hi : i = 0 := by grind
    simp[hi]; cbv

end NumLean
