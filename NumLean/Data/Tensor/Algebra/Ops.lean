module

public import NumLean.Interfaces.Algebra.RCLike
public import NumLean.Interfaces.Module
public import NumLean.Data.Tensor.Basic
public import NumLean.Data.Tensor.Algebra.VMul
public import NumLean.Interfaces.TensorAlgebra

@[expose] public section

namespace NumLean.Tensor

open Tensor TensorRingOps

variable {X : Type u} {I : Type v}
  {Ks K nX nI} [HasDefaultFlatRepr X Ks] [VectorType Ks K] [HasFlatRepr X Ks nX] [IndexType I nI]

instance instZero [Zero K] : Zero (Tensor X I) :=
  ⟨{ data := VectorType.replicate (nI * nX) 0 }⟩

theorem zero_def [Zero K] :
    (0 : Tensor X I) =
      { data := VectorType.replicate (nI * nX) 0 } := rfl

instance instOne [One K] : One (Tensor X I) :=
  ⟨{ data := VectorType.replicate (nI * nX) 1 }⟩

theorem one_def [One K] :
    (1 : Tensor X I) =
      { data := VectorType.replicate (nI * nX) 1 } := rfl

section Ring

variable [RingOps K] [TensorRingOps Ks K]

instance instAdd : Add (Tensor X I) := ⟨fun x y =>
  let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
  let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
  -- we on purpose reverse the order of `x` and `y`
  -- `tensorAxpy` mutates the second argument if it can, but in expressions like
  -- `x₁ + x₂ + x₃ + x₄` the left operand is usually temporari thus mutable. This is because
  -- that expression is associated as `((x₁ + x₂) + x₃) + x₄` by default
  { data := tensorAxpy (1 : K) y.data map x.data map hmap }⟩

theorem add_def (x y : Tensor X I) :
    x + y =
      let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
      let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
      { data := tensorAxpy (1 : K) y.data map x.data map hmap } := rfl

instance instSub : Sub (Tensor X I) := ⟨fun x y =>
  let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
  let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
  { data := tensorAxpy (-1 : K) y.data map x.data map hmap }⟩

theorem sub_def (x y : Tensor X I) :
    x - y =
      let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
      let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
      { data := tensorAxpy (-1 : K) y.data map x.data map hmap } := rfl

instance instSMul : SMul K (Tensor X I) := ⟨fun s x =>
  let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
  let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
  { data := tensorScal s x.data map hmap }⟩

theorem smul_def (s : K) (x : Tensor X I) :
    s • x =
      let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
      let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
      { data := tensorScal s x.data map hmap } := rfl

instance instNeg : Neg (Tensor X I) :=
  ⟨fun x => (-1 : K) • x⟩

theorem neg_def (x : Tensor X I) :
    -x = (-1 : K) • x := rfl

instance instAddMonoidOps : AddMonoidOps (Tensor X I) where
  nsmul n x := (n : K) • x

instance instAddGroupOps : AddGroupOps (Tensor X I) where
  zsmul n x := (n : K) • x

end Ring


section ROps

variable [ROps K] [TensorRingOps Ks K]

instance : RNorm (Tensor X I) K where
  rnorm x :=
    let map := Layout.id h(nI * nX)
    ROps.sqrt (tensorDot x.data map x.data map)

instance : NormedAddMonoidOps K (Tensor X I) where

instance : NormedAddGroupOps K (Tensor X I) where

end ROps

end NumLean.Tensor
