module

public import NumLean.Data.Tensor.Basic
public import NumLean.Interfaces.Algebra.MatrixOps
public import NumLean.Interfaces.TensorAlgebra

@[expose] public section

namespace NumLean.Tensor

open Interfaces.Algebra Tensor TensorRingOps

section Dot
variable {X : Type u} {I : Type v}
    {Rs R nI} [VectorType Rs R] [HasDefaultFlatRepr X Rs nX] [IndexType I nI]
    [RingOps R] [TensorRingOps Rs R]

def dot (x y : Tensor X I) : R :=
  let map := Layout.id h(nI * nX)
  tensorDot x.data map y.data map

instance : Inner R (Tensor X I) where
  inner x y := x.dot y

theorem dot_def (x y : Tensor X I) :
    Inner.inner R x y
    =
    let map := Layout.id h(nI * nX)
    tensorDot x.data map y.data map := by rfl

end Dot


section VectorMatrixMul

variable {X : Type u} {I : Type v}
    {Rs R nI} [VectorType Rs R] [HasDefaultFlatRepr X Rs 1] [IndexType I nI]
    [RingOps R] [TensorRingOps Rs R]

variable
  {J nJ} [IndexType J nJ]
  {K nK} [IndexType K nK]


def vecMatMul (x : Tensor X I) (A : Tensor X (I × J)) : Tensor X J :=
  let amap : Layout h(nJ, nI) h(nI * nJ * 1) :=
    Layout.colMajor h(nJ, nI) |>.cast _ _ rfl (by simp; ring)
  let xmap : Layout h(nI) h(nI * 1) := (Layout.id h(nI)).cast h(nI) h(nI * 1)
  let ymap : Layout h(nJ) h(nJ * 1) := (Layout.id h(nJ)).cast h(nJ) h(nJ * 1)
  { data := tensorGemv (1 : R) 0 (rows := h(nJ)) (cols := h(nI))
              A.data amap x.data xmap (VectorType.replicate _ 0) ymap (by grind) }

instance : VMul (Tensor X I) (Tensor X (I × J)) (Tensor X J) where
  vmul x A := vecMatMul x A


def matVecMul (A : Tensor X (I × J)) (y : Tensor X J)  : Tensor X I :=
  let amap : Layout h(nI, nJ) h(nI * nJ * 1) := Layout.rowMajor h(nI, nJ) |>.cast _ _
  let xmap : Layout h(nI) h(nI * 1) := (Layout.id h(nI)).cast h(nI) h(nI * 1)
  let ymap : Layout h(nJ) h(nJ * 1) := (Layout.id h(nJ)).cast h(nJ) h(nJ * 1)
  { data := tensorGemv (1 : R) 0 (rows := h(nI)) (cols := h(nJ))
              A.data amap y.data ymap (VectorType.replicate _ 0) xmap (by grind) }

instance : VMul (Tensor X (I × J)) (Tensor X J) (Tensor X I) where
  vmul A y := matVecMul A y


def matMul (A : Tensor X (I × J)) (B : Tensor X (J × K))  : Tensor X (I × K) :=
  let amap := Layout.rowMajor h(nI, nJ)
  let bmap := Layout.rowMajor h(nJ, nK)
  let cmap := Layout.rowMajor h(nI, nK)
  { data := tensorGemm (1 : R) 0
       A.data (amap.cast h(nI, nJ) _)
       B.data (bmap.cast h(nJ, nK) _)
       (VectorType.replicate _ 0) (cmap.cast h(nI, nK) _) (by grind) }

instance : VMul (Tensor X (I × J)) (Tensor X (J × K)) (Tensor X (I × K)) where
  vmul A B := matMul A B
