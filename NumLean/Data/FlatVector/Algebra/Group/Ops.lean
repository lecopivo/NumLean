import NumLean.Interfaces.Algebra.RCLike
import NumLean.Interfaces.Module
import NumLean.Data.FlatVector.Basic
import NumLean.Interfaces.TensorAlgebra

namespace NumLean.FlatVector

open Tensor TensorRingOps

variable {X : Type u} {I : Type v}
  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX] [IndexType I nI]

instance instZero [Zero K] : Zero (FlatVector X I) :=
  ⟨{ data := VectorType.replicate (nI * nX) 0 }⟩

theorem zero_def [Zero K] :
    (0 : FlatVector X I) =
      { data := VectorType.replicate (nI * nX) 0 } := rfl

instance instOne [One K] : One (FlatVector X I) :=
  ⟨{ data := VectorType.replicate (nI * nX) 1 }⟩

theorem one_def [One K] :
    (1 : FlatVector X I) =
      { data := VectorType.replicate (nI * nX) 1 } := rfl

section Ring

variable [RingOps K] [TensorRingOps Ks K .leaf]

instance instAdd : Add (FlatVector X I) := ⟨fun x y =>
  let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
  let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
  -- we on purpose reverse the order of `x` and `y`
  -- `tensorAxpy` mutates the second argument if it can, but in expressions like
  -- `x₁ + x₂ + x₃ + x₄` the left operand is usually temporari thus mutable. This is because
  -- that expression is associated as `((x₁ + x₂) + x₃) + x₄` by default
  { data := tensorAxpy (1 : K) y.data map x.data map hmap }⟩

theorem add_def (x y : FlatVector X I) :
    x + y =
      let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
      let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
      { data := tensorAxpy (1 : K) y.data map x.data map hmap } := rfl

instance instSub [TensorRingOps Ks K .leaf] : Sub (FlatVector X I) := ⟨fun x y =>
  let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
  let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
  { data := tensorAxpy (-1 : K) y.data map x.data map hmap }⟩

theorem sub_def (x y : FlatVector X I) :
    x - y =
      let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
      let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
      { data := tensorAxpy (-1 : K) y.data map x.data map hmap } := rfl

instance instSMul : SMul K (FlatVector X I) := ⟨fun s x =>
  let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
  let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
  { data := tensorScal s x.data map hmap }⟩

theorem smul_def (s : K) (x : FlatVector X I) :
    s • x =
      let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
      let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
      { data := tensorScal s x.data map hmap } := rfl

instance instNeg : Neg (FlatVector X I) :=
  ⟨fun x => (-1 : K) • x⟩

theorem neg_def (x : FlatVector X I) :
    -x = (-1 : K) • x := rfl

instance instAddMonoidOps : AddMonoidOps (FlatVector X I) where
  nsmul n x := (n : K) • x

instance instAddGroupOps : AddGroupOps (FlatVector X I) where
  zsmul n x := (n : K) • x

end Ring


section ROps

variable [ROps K] [TensorRingOps Ks K .leaf]

instance : RNorm (FlatVector X I) K where
  rnorm x :=
    let map := Layout.id h(nI * nX)
    ROps.sqrt (tensorDot x.data map x.data map)

instance : NormedAddMonoidOps K (FlatVector X I) where

instance : NormedAddGroupOps K (FlatVector X I) where

end ROps

end NumLean.FlatVector
