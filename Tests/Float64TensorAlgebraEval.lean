module

public import NumLean
public meta import NumLean.Interfaces.RealModel
public meta import NumLean.Data.Scalars.Float64.Algebra
public meta import NumLean.Data.Scalars.Float64.RealModel
public meta import NumLean.Data.Tensor.Algebra.Ops
public meta import NumLean.Data.Tensor.Algebra.VMul

@[expose] public section

namespace NumLean.Tests.Float64TensorAlgebraEval

set_option backward.do.legacy false

open NumLean

def flat4 (x : Float^[4]) : Array Float :=
  #[x[0], x[1], x[2], x[3]]

def flat2 (x : Float^[2]) : Array Float :=
  #[x[0], x[1]]

def flat22 (x : Float^[2, 2]) : Array Float :=
  #[x[0, 0], x[0, 1], x[1, 0], x[1, 1]]

def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw <| IO.userError s!"Float64 tensor algebra eval failed: {name}"

def stridedViewAdd : Float^[6, 10] :=
  let A : Float^[6, 10] := 0
  let B : Float^[4, 6] :=
    ⊞[[1.0, 2, 3, 4, 5, 6],
      [7.0, 8, 9, 10, 11, 12],
      [13.0, 14, 15, 16, 17, 18],
      [19.0, 20, 21, 22, 23, 24]]
  (A[1:5, 2:8]& + B).data

def run : IO Unit := do
  check "add" <|
    flat4 (⊞[1.0, 2, 3, 4] + ⊞[10.0, 20, 30, 40]) == #[11.0, 22.0, 33.0, 44.0]
  check "sub" <|
    flat4 (⊞[10.0, 20, 30, 40] - ⊞[1.0, 2, 3, 4]) == #[9.0, 18.0, 27.0, 36.0]
  check "smul" <|
    flat4 (3.0 • (⊞[1.0, 2, 3, 4] : Float^[4])) == #[3.0, 6.0, 9.0, 12.0]
  check "dot" <|
    (⊞[1.0, 2, 3, 4] : Float^[4]).dot (⊞[1.0, 2, 3, 4] : Float^[4]) == 30.0
  check "matvec" <|
    flat2 ((⊞[[1.0, 2, 3], [4, 5, 6]] : Float^[2, 3]) *ᵥ (⊞[10.0, 20, 30] : Float^[3]))
      == #[140.0, 320.0]
  check "matmul" <|
    flat22 ((⊞[[1.0, 2, 3], [4, 5, 6]] : Float^[2, 3]) *ᵥ
      (⊞[[7.0, 8], [9, 10], [11, 12]] : Float^[3, 2]))
      == #[58.0, 64.0, 139.0, 154.0]
  check "strided view first" <| stridedViewAdd[1, 2] == 1.0
  check "strided view last" <| stridedViewAdd[4, 7] == 24.0
  check "strided view untouched" <| stridedViewAdd[0, 0] == 0.0

end NumLean.Tests.Float64TensorAlgebraEval
