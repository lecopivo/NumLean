import NumLean.Data.TensorIndex.Basic
import NumLean.Interfaces.ArrayType.Array

namespace NumLean

namespace Array

mutual

  /-- Recursive flat-memory tensor slice copy reference implementation.

  `count` describes the copied box. `srcOffset`/`dstOffset` are flat base offsets, and
  `srcStride`/`dstStride` are flat strides for each copied axis. -/
  def copyTensorSliceList {α : Type u} (rank : Nat) (count : List Nat)
      (src : Array α) (srcOffset : Nat) (srcStride : List Nat)
      (dst : Array α) (dstOffset : Nat) (dstStride : List Nat)
      (hrank : count.length = rank ∧ srcStride.length = rank ∧ dstStride.length = rank) :
      Array α :=
    match rank, count, srcStride, dstStride with
    | 0, [], [], [] =>
        if h : srcOffset < src.size ∧ dstOffset < dst.size then
          dst.set dstOffset src[srcOffset]
        else
          dst
    | rank + 1, n :: count, srcS :: srcStride, dstS :: dstStride =>
        copyTensorSliceListLoop rank n 0 count src srcOffset srcS srcStride
          dst dstOffset dstS dstStride (by grind)
    | _, _, _, _ => dst
  termination_by (rank + 1, 0)

  /-- Tail-recursive loop over the current tensor axis. -/
  def copyTensorSliceListLoop {α : Type u} (rank fuel i : Nat) (count : List Nat)
      (src : Array α) (srcOffset srcS : Nat) (srcStride : List Nat)
      (dst : Array α) (dstOffset dstS : Nat) (dstStride : List Nat)
      (hrank : count.length = rank ∧ srcStride.length = rank ∧ dstStride.length = rank) :
      Array α :=
    match fuel with
    | 0 => dst
    | fuel + 1 =>
        copyTensorSliceListLoop rank fuel (i + 1) count src srcOffset srcS srcStride
          (copyTensorSliceList rank count src (srcOffset + i * srcS) srcStride
            dst (dstOffset + i * dstS) dstStride hrank)
          dstOffset dstS dstStride hrank
  termination_by (rank + 1, fuel + 1)
  decreasing_by
    all_goals simp_wf
    all_goals omega

end



/-- Flat-memory tensor slice copy reference implementation. -/
def copyTensorSlice {α : Type u} {r : Nat} (count : Vector Nat r)
    (src : Array α) (srcOffset : Nat) (srcStride : Vector Nat r)
    (dst : Array α) (dstOffset : Nat) (dstStride : Vector Nat r) : Array α :=
  copyTensorSliceList r count.toList src srcOffset srcStride.toList dst dstOffset dstStride.toList
    (by simp)

end Array

/-- Tensor-style operations on an array storage type.

The core operation copies a rank-polymorphic flat-memory strided slice from `src` to `dst`.
Its specification is agreement with the reference implementation on plain `Array`s. -/
class TensorArrayOps (Ks : Type u) (K : outParam (Type v)) [ArrayType Ks K] where
  copyTensorSlice {r : Nat} (count : Vector Nat r)
    (src : Ks) (srcOffset : Nat) (srcStride : Vector Nat r)
    (dst : Ks) (dstOffset : Nat) (dstStride : Vector Nat r) : Ks

  copyTensorSlice_spec {r : Nat} (count : Vector Nat r)
    (src : Ks) (srcOffset : Nat) (srcStride : Vector Nat r)
    (dst : Ks) (dstOffset : Nat) (dstStride : Vector Nat r) :
    ArrayType.toArray (copyTensorSlice count src srcOffset srcStride dst dstOffset dstStride)
    =
    Array.copyTensorSlice count (ArrayType.toArray src) srcOffset srcStride
      (ArrayType.toArray dst) dstOffset dstStride

namespace TensorArrayOps

variable {Ks : Type u} {K : Type v} [ArrayType Ks K] [TensorArrayOps Ks K]

theorem toArray_copyTensorSlice {r : Nat} (count : Vector Nat r)
    (src : Ks) (srcOffset : Nat) (srcStride : Vector Nat r)
    (dst : Ks) (dstOffset : Nat) (dstStride : Vector Nat r) :
    ArrayType.toArray (copyTensorSlice count src srcOffset srcStride dst dstOffset dstStride) =
      Array.copyTensorSlice count (ArrayType.toArray src) srcOffset srcStride
        (ArrayType.toArray dst) dstOffset dstStride :=
  TensorArrayOps.copyTensorSlice_spec count src srcOffset srcStride dst dstOffset dstStride

instance {K : Type u} : TensorArrayOps (Array K) K where
  copyTensorSlice count src srcOffset srcStride dst dstOffset dstStride :=
    Array.copyTensorSlice count src srcOffset srcStride dst dstOffset dstStride
  copyTensorSlice_spec _ _ _ _ _ _ _ := rfl

end TensorArrayOps

end NumLean
