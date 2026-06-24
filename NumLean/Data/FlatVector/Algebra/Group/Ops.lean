import NumLean.Algebra.Ops
import NumLean.Data.FlatVector.Basic
import NumLean.Interfaces.TensorAlgebra

namespace NumLean.FlatVector

open Tensor

variable {X : Type u} {I : Type v}
  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX] [IndexType I nI]

instance instZero [Zero K] : Zero (FlatVector X I) :=
  ⟨{ data := VectorType.replicate (nI * nX) 0 }⟩

instance instOne [One K] : One (FlatVector X I) :=
  ⟨{ data := VectorType.replicate (nI * nX) 1 }⟩

instance instAdd [One K] [TensorSemiringOps Ks K .leaf] : Add (FlatVector X I) := ⟨fun x y =>
  let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
  let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
  { data := TensorSemiringOps.tensorAxpy (1 : K) y.data map x.data map hmap }⟩

instance instSub [TensorRingOps Ks K .leaf] : Sub (FlatVector X I) := ⟨fun x y =>
  let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
  let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
  { data := TensorRingOps.tensorSub y.data map x.data map hmap }⟩

instance instSMul [TensorMulOps Ks K .leaf] : SMul K (FlatVector X I) := ⟨fun s x =>
  let map : Layout h(nI * nX) h(nI * nX) := Layout.id h(nI * nX)
  let hmap : map.Injective := by simpa [map] using FinHTupleMap.injective_id h(nI * nX)
  { data := TensorMulOps.tensorScal s x.data map hmap }⟩

instance instNeg [Neg K] [One K] [TensorMulOps Ks K .leaf] : Neg (FlatVector X I) :=
  ⟨fun x => (-1 : K) • x⟩

instance instAddMonoidOps [Zero K] [NatCast K] [One K] [TensorSemiringOps Ks K .leaf] :
    AddMonoidOps (FlatVector X I) where
  toAdd := instAdd
  toZero := instZero
  nsmul n x := (n : K) • x

instance instAddGroupOps [NatCast K] [IntCast K] [AddGroupOps K] [One K]
    [TensorRingOps Ks K .leaf] :
    AddGroupOps (FlatVector X I) where
  toAddMonoidOps := instAddMonoidOps
  toSub := instSub
  toNeg := instNeg
  zsmul n x := (n : K) • x

end NumLean.FlatVector
