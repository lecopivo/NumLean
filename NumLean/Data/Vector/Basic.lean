module

public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn
public import Init.Data.Vector.Zip
public import NumLean.Interfaces.SetElem

@[expose] public section

namespace NumLean

instance : SetElem (Vector α n) Nat α (fun _ i => i < n) where
  setElem xs i x h := xs.set i x h
  setElem_valid := by intros; simp

instance : LawfulSetElem (Vector α n) Nat where
  getElem_setElem_eq := by intros; simp [setElem]
  getElem_setElem_neq := by intros; simp_all [setElem]

namespace Vector
