import NumLean.Data.TensorIndex.Layout
import NumLean.Data.TensorIndex.TensorIndexType

namespace NumLean

namespace TensorIndex

structure FinTIndexMap {r r'} (shape : Shape r) (shape' : Shape r')
  extends Layout shape (TIndex Int r') where
    in_bounds : toLayout.InBounds shape'

open TensorIndexType in
structure TensorIndexMap (J : Type u) (I : Type v)
  {shapeJ : Shape rankJ} [TensorIndexType J nJ rankJ shapeJ] [IndexType I nI]
  where
    map : J → I

    layout : Layout shapeJ Int
    bounded : layout.BoundedBy 0 nI

    fromFin_eval_toFinTIndex : ∀ j : J,
      fromFin (layout.evalToFin bounded (toFinTIndex j)) = map j

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

end FinTIndexMap
