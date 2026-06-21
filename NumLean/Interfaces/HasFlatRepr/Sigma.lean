import NumLean.Data.Sigma
import NumLean.Interfaces.HasFlatRepr.Equiv
import NumLean.Interfaces.HasFlatRepr.Prod

namespace NumLean

namespace HasFlatRepr

private def sigmaEquivProd (X : Type u) (Y : Type v) : ((_ : X) × Y) ≃ X × Y where
  toFun xy := (xy.1, xy.2)
  invFun xy := ⟨xy.1, xy.2⟩
  left_inv := by
    intro xy
    rfl
  right_inv := by
    intro xy
    rfl

instance {X : Type u} {Y : Type v} {Ks : Nat → Type w} {K : Type z} {nX nY : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [HasFlatRepr Y Ks nY] :
    HasFlatRepr ((_ : X) × Y) Ks (nX + nY) :=
  HasFlatRepr.ofEquiv Ks (sigmaEquivProd X Y).symm

end HasFlatRepr

end NumLean
