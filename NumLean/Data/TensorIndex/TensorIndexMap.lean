import NumLean.Data.TensorIndex.TensorIndexType

namespace NumLean

open TensorIndex

open TensorIndexType in
structure TensorIndexMap (J : Type u) (I : Type v)
  {shapeJ : Shape rankJ} [TensorIndexType J nJ rankJ shapeJ] [IndexType I nI]
  where
    map : J → I

    layout : Layout shapeJ Nat
    bounded : layout.BoundedBy 0 nI

    fromFin_eval_toFinTIndex : ∀ j : J,
      fromFin (layout.evalToFin bounded (toFinTIndex j)) = map j


namespace TensorIndexMap


variable {J I : Type u} {nJ nI : Nat} {rankJ} {shapeJ : Shape rankJ}
    [TensorIndexType J nJ rankJ shapeJ] [IndexType I nI]

/-- The map induced by a base offset and target strides. -/
def toFun (m : TensorIndexMap J I) : J → I :=
  m.map


def mkFinRange (start count : Nat) (h : start + count ≤ nI) : TensorIndexMap (Fin count) I where
  map j := fromFin ⟨start + j.1, by grind⟩

  layout := { offset := start, stride := .leaf 1 }
  bounded := by intro i; simp; have h := i.2; sorry

  fromFin_eval_toFinTIndex := by
    intro j;
    simp [Layout.evalToFin, TensorIndexType.toFinTIndex, TensorIndexTypeOfRank.tensorEquiv,
          FinTIndex.equivFin, IndexType.equivFin, toFin]



end TensorIndexMap

end NumLean
