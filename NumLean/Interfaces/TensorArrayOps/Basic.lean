import NumLean.Data.TensorIndex.TensorSliceMap
import NumLean.Data.Array.TensorOps
import NumLean.Data.FloatArray.TensorOps
import NumLean.Interfaces.ArrayOps.Array
import NumLean.Interfaces.ArrayOps.FloatArray

namespace NumLean

/-- Tensor-style operations on an array storage type.

Operations iterate over the logical tensor box `counts`, not over source or destination storage
sizes. Bounds and no-alias/injectivity assumptions belong to the lawful/spec layer. -/
class TensorArrayOps (Ks : Type u) (K : outParam (Type v)) [ArrayOps Ks K] where
  fillTensorSlice {rank : Nat} (counts : Vector Nat rank)
    (dst : Ks) (dstOff : Nat) (dstStrides : Vector Nat rank) (x : K) : Ks

  copyTensorSlice {rank : Nat} (counts : Vector Nat rank)
    (src : Ks) (srcOff : Nat) (srcStrides : Vector Nat rank)
    (dst : Ks) (dstOff : Nat) (dstStrides : Vector Nat rank) : Ks

  extractTensorSlice [Inhabited K] {rank : Nat} (counts : Vector Nat rank)
    (src : Ks) (srcOff : Nat) (srcStrides : Vector Nat rank) : Ks

namespace TensorArrayOps

variable {Ks : Type u} {K : Type v} [ArrayOps Ks K] [TensorArrayOps Ks K]
#exit
/-- Lawfulness of tensor array operations against the reference `Array` implementation.

The specs are stated under the assumptions that the logical tensor slice has injective strides and
that all produced offsets are in bounds for the corresponding storage. -/
class LawfulTensorArrayOps (Ks : Type u) {K : outParam (Type v)}
    [ArrayOps Ks K] [TensorArrayOps Ks K] where
  fillTensorSlice_spec {rank : Nat} (counts : Vector Nat rank)
    (dst : Ks) (dstOff : Nat) (dstStrides : Vector Nat rank) (x : K)
    (hdstValid : TensorIndex.ValidStrides counts dstStrides)
    (hdstBounds : TensorSliceInBounds counts dstOff dstStrides (ArrayOps.size dst)) :
    ArrayOps.toArray (fillTensorSlice counts dst dstOff dstStrides x) =
      Array.fillTensorSlice counts (ArrayOps.toArray dst) dstOff dstStrides x

  copyTensorSlice_spec {rank : Nat} (counts : Vector Nat rank)
    (src : Ks) (srcOff : Nat) (srcStrides : Vector Nat rank)
    (dst : Ks) (dstOff : Nat) (dstStrides : Vector Nat rank)
    (hsrcValid : TensorIndex.ValidStrides counts srcStrides)
    (hdstValid : TensorIndex.ValidStrides counts dstStrides)
    (hsrcBounds : TensorSliceInBounds counts srcOff srcStrides (ArrayOps.size src))
    (hdstBounds : TensorSliceInBounds counts dstOff dstStrides (ArrayOps.size dst)) :
    ArrayOps.toArray (copyTensorSlice counts src srcOff srcStrides dst dstOff dstStrides) =
      Array.copyTensorSlice counts (ArrayOps.toArray src) srcOff srcStrides
        (ArrayOps.toArray dst) dstOff dstStrides

  extractTensorSlice_spec [Inhabited K] {rank : Nat} (counts : Vector Nat rank)
    (src : Ks) (srcOff : Nat) (srcStrides : Vector Nat rank)
    (hsrcValid : TensorIndex.ValidStrides counts srcStrides)
    (hsrcBounds : TensorSliceInBounds counts srcOff srcStrides (ArrayOps.size src)) :
    ArrayOps.toArray (extractTensorSlice counts src srcOff srcStrides) =
      Array.extractTensorSlice counts (ArrayOps.toArray src) srcOff srcStrides

instance {K : Type u} : TensorArrayOps (Array K) K where
  fillTensorSlice counts dst dstOff dstStrides x :=
    Array.fillTensorSlice counts dst dstOff dstStrides x
  copyTensorSlice counts src srcOff srcStrides dst dstOff dstStrides :=
    Array.copyTensorSlice counts src srcOff srcStrides dst dstOff dstStrides
  extractTensorSlice counts src srcOff srcStrides :=
    Array.extractTensorSlice counts src srcOff srcStrides

instance {K : Type u} : LawfulTensorArrayOps (Array K) where
  fillTensorSlice_spec := by intros; rfl
  copyTensorSlice_spec := by intros; rfl
  extractTensorSlice_spec := by intros; rfl

instance : TensorArrayOps FloatArray Float where
  fillTensorSlice counts dst dstOff dstStrides x :=
    FloatArray.fillTensorSliceRef counts dst dstOff dstStrides x
  copyTensorSlice counts src srcOff srcStrides dst dstOff dstStrides :=
    FloatArray.copyTensorSliceRef counts src srcOff srcStrides dst dstOff dstStrides
  extractTensorSlice counts src srcOff srcStrides :=
    FloatArray.extractTensorSliceRef counts src srcOff srcStrides

-- instance : LawfulTensorArrayOps FloatArray where
--   fillTensorSlice_spec := by
--     intros
--     simp [TensorArrayOps.fillTensorSlice, FloatArray.fillTensorSliceRef, ArrayOps.toArray]
--   copyTensorSlice_spec := by
--     intros
--     simp [TensorArrayOps.copyTensorSlice, FloatArray.copyTensorSliceRef, ArrayOps.toArray]
--   extractTensorSlice_spec := by
--     intros
--     simp [TensorArrayOps.extractTensorSlice, FloatArray.extractTensorSliceRef, ArrayOps.toArray]

end TensorArrayOps

end NumLean
