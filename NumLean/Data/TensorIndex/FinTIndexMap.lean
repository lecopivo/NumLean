import NumLean.Data.TensorIndex.Layout
import NumLean.Data.HTuple
import NumLean.Data.TensorIndex.TensorIndexType

namespace NumLean

namespace TensorIndex

structure FinTIndexMap {r r'} (shape : Shape r) (shape' : Shape r')
  extends Layout shape (TIndex Nat r') where
    in_bounds : toLayout.InBounds shape'

namespace FinTIndexMap

variable {r r'} {shape : Shape r} {shape' : Shape r'}

theorem ext (f g : FinTIndexMap shape shape') :
  (∀ i : FinTIndex shape, f.eval i.1 = g.eval i.1) → f = g := by sorry

instance : FunLike (FinTIndexMap shape shape') (FinTIndex shape) (FinTIndex shape') where
  coe f := f.evalToFinTIndex f.in_bounds
  coe_injective' := by
    intros f g h
    apply ext
    sorry

instance : GetElem (FinTIndexMap shape shape') (TIndex Nat r) (FinTIndex shape')
    (fun xs i => i ∈ 0...shape) where
  getElem xs i h := xs ⟨i, sorry⟩

def range (f : FinTIndexMap shape shape') : Set Nat :=
  Set.range fun i : FinTIndex shape => (FinTIndex.equivFin shape' (f i)).val

end FinTIndexMap
