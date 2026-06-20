import NumLean.Data.TensorIndex.AxisOrder
import NumLean.Interfaces.SetElem

namespace NumLean

namespace TensorIndex

namespace FinTIndex

@[implicit_reducible]
def fintype {p : HRank} (shape : Shape p) : Fintype (FinTIndex shape) :=
  Fintype.ofEquiv (Fin shape.size) (equivFin shape).symm

instance {p : HRank} {shape : Shape p} : Fintype (FinTIndex shape) :=
  fintype shape

theorem card_eq_shape_size {p : HRank} (shape : Shape p) :
    Fintype.card (FinTIndex shape) = shape.size := by
  simpa using Fintype.card_congr (equivFin shape)


@[coe]
def toFin {n} (i : FinTIndex (.leaf n)) : Fin n :=
  match i with
  | ⟨.leaf i, h⟩ => ⟨i, h⟩

instance : Coe (FinTIndex (.leaf n)) (Fin n) := ⟨fun i => i.toFin⟩
instance : CoeOut (FinTIndex (.leaf n)) Nat := ⟨fun i => i.toFin⟩

variable {n} (i : FinTIndex h(n)) (j : Fin n)

instance [GetElem cont (Fin n) elem dom] :
    GetElem cont (FinTIndex (.leaf n)) elem (fun xs i => dom xs i.toFin) where
  getElem xs i h := xs[i.toFin]'h

instance [SetElem cont (Fin n) elem dom] :
    SetElem cont (FinTIndex (.leaf n)) elem (fun xs i => dom xs i.toFin) where
  setElem xs i x h := setElem xs i.toFin x h
  setElem_valid := sorry

@[simp]
theorem getElem_toFin [GetElem cont (Fin n) elem dom] (xs : cont) (i : FinTIndex (.leaf n)) (h) :
  xs[i]'h = xs[i.toFin] := by rfl

end FinTIndex

end TensorIndex

end NumLean
