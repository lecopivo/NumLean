import NumLean.Data.FlatArray.Basic
import NumLean.Interfaces.IndexType

namespace NumLean

structure FlatVector (X : Type u) (I : Type v)
    {Ks K nX nI} [ArrayType Ks K] [HasDefaultFlatArray X Ks nX] [IndexType I nI] where
  toFlatArray : FlatArray X
  size_toFlatArray : toFlatArray.size = nI

namespace FlatVector

variable {X : Type u} {I : Type v}
    {Ks K nX nI} [ArrayType Ks K] [HasDefaultFlatArray X Ks nX] [IndexType I nI]

instance : GetElem (FlatVector X I) I X (fun _ _ => True) where
  getElem xs i h := xs.toFlatArray[toFin i]'(by have := xs.2; grind)

instance : SetElem (FlatVector X I) I X (fun _ _ => True) where
  setElem xs i x h :=
    { toFlatArray := setElem xs.toFlatArray (toFin i).1 x (by have := xs.2; grind)
      size_toFlatArray := by simp [xs.2] }
  setElem_valid := by intros; simp

@[simp]
theorem getElem_mk (xs : FlatArray X) (i : I) (h : xs.size = nI) :
    (FlatVector.mk (I:=I) xs h)[i] = xs[toFin i]'(by grind) := rfl

@[simp]
theorem setElem_mk (xs : FlatArray X) (i : I) (x : X) (h : xs.size = nI) :
    setElem (FlatVector.mk (I:=I) xs h) i x .intro
    =
    FlatVector.mk (setElem xs (toFin i).1 x (by grind)) (by simp_all) := rfl

@[ext]
theorem ext (xs ys : FlatVector X I) : (∀ i : I, xs[i] = ys[i]) → xs = ys := by
  obtain ⟨xs, hx⟩ := xs
  obtain ⟨ys, hy⟩ := ys
  simp only [getElem_mk, Fin.getElem_fin, mk.injEq]
  intro h
  apply FlatArray.ext
  · simp only [hx, hy]
  · intro i h₁ h₂;
    have hh : i = (toFin (fromFin (I:=I) ⟨i, by grind⟩)).1 := by simp
    grind


end FlatVector

end NumLean
