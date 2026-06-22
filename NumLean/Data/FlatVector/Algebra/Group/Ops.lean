import NumLean.Algebra.Ops
import NumLean.Data.FlatVector.Basic
import NumLean.Interfaces.Algebra.RingArrayOps

namespace NumLean.FlatVector

variable {X : Type u} {I : Type v}
  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX] [IndexType I nI]

instance instZero [Zero K] : Zero (FlatVector X I) :=
  ⟨{ data := VectorType.replicate (nI * nX) 0 }⟩

instance instOne [One K] : One (FlatVector X I) :=
  ⟨{ data := VectorType.replicate (nI * nX) 1 }⟩

instance instAdd [One K] [RingArrayOps Ks] : Add (FlatVector X I) := ⟨fun x y =>
  { data := RingArrayOps.axpy (nI * nX) (1 : K) y.data 0 1 x.data 0 1 (by simp) (by simp) }⟩

instance instSub [Neg K] [One K] [RingArrayOps Ks] : Sub (FlatVector X I) := ⟨fun x y =>
  { data := RingArrayOps.axpy (nI * nX) (-1 : K) y.data 0 1 x.data 0 1 (by simp) (by simp) }⟩

instance instSMul [RingArrayOps Ks] : SMul K (FlatVector X I) := ⟨fun s x =>
  { data := RingArrayOps.scal (nI * nX) s x.data 0 1 (by simp) }⟩

instance instNeg [Neg K] [One K] [RingArrayOps Ks] : Neg (FlatVector X I) :=
  ⟨fun x => (-1 : K) • x⟩

-- todo: NatCast and IntCast should be part of some *Ops.
instance instAddMonoidOps [Zero K] [NatCast K] [One K] [RingArrayOps Ks] :
    AddMonoidOps (FlatVector X I) where
  toAdd := instAdd
  toZero := instZero
  nsmul n x := (n : K) • x

instance instAddGroupOps [NatCast K] [IntCast K] [AddGroupOps K] [One K] [RingArrayOps Ks] :
    AddGroupOps (FlatVector X I) where
  toAddMonoidOps := instAddMonoidOps
  toSub := instSub
  toNeg := instNeg
  zsmul n x := (n : K) • x

end NumLean.FlatVector
