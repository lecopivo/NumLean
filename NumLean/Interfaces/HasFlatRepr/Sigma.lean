module

public import NumLean.Data.Sigma
public import NumLean.Interfaces.HasFlatRepr.Equiv
public import NumLean.Interfaces.HasFlatRepr.Prod

@[expose] public section

namespace NumLean

namespace HasFlatRepr

-- todo: move this to Data.Sigma and use this to infer instances on sigma
def sigmaEquivProd (X : Type u) (Y : Type v) : ((_ : X) × Y) ≃ X × Y where
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
