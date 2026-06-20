import Init.Data.Vector.Lemmas
import Init.Data.Vector.OfFn
import Init.Data.Vector.Zip
import NumLean.Interfaces.SetElem

namespace NumLean

instance : SetElem (Vector α n) Nat α (fun _ i => i < n) where
  setElem xs i x h := xs.set i x h
  setElem_valid := by intros; simp

instance : SetElem (Vector α n) (Fin n) α (fun _ i => True) where
  setElem xs i x h := xs.set i.1 x i.2
  setElem_valid := by intros; simp

namespace Vector

@[simp]
theorem setElem_fin_eq_set (xs : Vector α n) {x} (i : Fin n) :
    setElem xs i x (by trivial) = xs.set i.1 x := by rfl

@[simp]
theorem setElem_nat_eq_set (xs : Vector α n) {x} (i : Nat) (h : i < n) :
    setElem xs i x h = xs.set i x := by rfl
