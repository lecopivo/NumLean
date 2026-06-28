module

public import NumLean.Data.FlatVector.Basic
public import NumLean.Interfaces.Algebra.MatrixOps
public import NumLean.Interfaces.TensorAlgebra

@[expose] public section

namespace NumLean.FlatVector

open Interfaces.Algebra

variable {X : Type u} {I : Type v}
    {Rs R nI} [VectorType Rs R] [HasDefaultFlatRepr X Rs 1] [IndexType I nI]
    [RingOps R] [TensorRingOps Rs R .leaf]


open Tensor TensorRingOps

def dot (x y : FlatVector X I) : R :=
  let map := Layout.id h(nI * 1)
  tensorDot x.data map y.data map

instance : Inner R (FlatVector X I) where
  inner x y := x.dot y

theorem dot_def (x y : FlatVector X I) :
    Inner.inner R x y
    =
    let map := Layout.id h(nI * 1)
    tensorDot x.data map y.data map := by rfl


variable
  {J nJ} [IndexType J nJ]
  {K nK} [IndexType K nK]


def vecMatMul (x : FlatVector X I) (A : FlatVector X (I × J)) : FlatVector X J :=
  let amap : Layout h(nJ, nI) h(nI * nJ * 1) :=
    Layout.colMajor h(nJ, nI) |>.cast _ _ rfl (by simp; ring)
  let xmap : Layout h(nI) h(nI * 1) := (Layout.id h(nI)).cast h(nI) h(nI * 1)
  let ymap : Layout h(nJ) h(nJ * 1) := (Layout.id h(nJ)).cast h(nJ) h(nJ * 1)
  { data := tensorGemv .leaf (1 : R) 0 (rows := h(nJ)) (cols := h(nI))
              A.data amap x.data xmap (VectorType.replicate _ 0) ymap (by grind) }

instance : VMul (FlatVector X I) (FlatVector X (I × J)) (FlatVector X J) where
  vmul x A := vecMatMul x A


def matVecMul (A : FlatVector X (I × J)) (y : FlatVector X J)  : FlatVector X I :=
  let amap : Layout h(nI, nJ) h(nI * nJ * 1) := Layout.rowMajor h(nI, nJ) |>.cast _ _
  let xmap : Layout h(nI) h(nI * 1) := (Layout.id h(nI)).cast h(nI) h(nI * 1)
  let ymap : Layout h(nJ) h(nJ * 1) := (Layout.id h(nJ)).cast h(nJ) h(nJ * 1)
  { data := tensorGemv .leaf (1 : R) 0 (rows := h(nI)) (cols := h(nJ))
              A.data amap y.data ymap (VectorType.replicate _ 0) xmap (by grind) }

instance : VMul (FlatVector X (I × J)) (FlatVector X J) (FlatVector X I) where
  vmul A y := matVecMul A y


def matMul (A : FlatVector X (I × J)) (B : FlatVector X (J × K))  : FlatVector X (I × K) :=
  let amap := Layout.rowMajor h(nI, nJ)
  let bmap := Layout.rowMajor h(nJ, nK)
  let cmap := Layout.rowMajor h(nI, nK)
  { data := tensorGemm .leaf (1 : R) 0
       A.data (amap.cast h(nI, nJ) _)
       B.data (bmap.cast h(nJ, nK) _)
       (VectorType.replicate _ 0) (cmap.cast h(nI, nK) _) (by grind) }

instance : VMul (FlatVector X (I × J)) (FlatVector X (J × K)) (FlatVector X (I × K)) where
  vmul A B := matMul A B
