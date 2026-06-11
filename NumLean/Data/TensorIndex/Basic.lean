import Mathlib.Data.Vector.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace NumLean

def TensorIndex.InBounds {rank : Nat} (idx dims : Vector Nat rank) : Prop :=
  ∀ i : Fin rank, idx[i] < dims[i]

open TensorIndex in
structure TensorIndex {rank : Nat} (dims : Vector Nat rank) where
  val : Vector Nat rank
  valid : InBounds val dims

namespace TensorIndex

variable {rank : Nat} {dims : Vector Nat rank}

/-- A permutation of axes, ordered from most significant to least significant. -/
abbrev AxisOrder (rank : Nat) := Equiv.Perm (Fin rank)

/-- Flat offset for a raw tensor index and one flat stride per tensor axis. -/
def offsetOf {rank : Nat} (strides idx : Vector Nat rank) : Nat :=
  ∑ i : Fin rank, idx[i] * strides[i]

/-- Flat offset for a bounded tensor index and one flat stride per tensor axis. -/
def offset (idx : TensorIndex dims) (strides : Vector Nat rank) : Nat :=
  offsetOf strides idx.val

/-- Valid strides are those whose offset map is injective on the bounded tensor index set. -/
def ValidStrides {rank : Nat} (dims strides : Vector Nat rank) : Prop :=
  Function.Injective fun idx : TensorIndex dims => offset idx strides

/-- Flat offset rewritten through an explicit axis order. -/
def orderedOffset {rank : Nat} (order : AxisOrder rank)
    (strides idx : Vector Nat rank) : Nat :=
  ∑ i : Fin rank, idx[order i] * strides[order i]

theorem offsetOf_eq_orderedOffset {rank : Nat} (order : AxisOrder rank)
    (strides idx : Vector Nat rank) :
    offsetOf strides idx = orderedOffset order strides idx := by
  simpa [offsetOf, orderedOffset] using
    (Equiv.sum_comp order (fun i : Fin rank => idx[i] * strides[i])).symm

/-- The axis order used by row-major dense strides: axis `0` is most significant. -/
def rowMajorAxisOrder (rank : Nat) : AxisOrder rank :=
  Equiv.refl (Fin rank)

/-- The axis order used by column-major dense strides: axis `rank - 1` is most significant. -/
def colMajorAxisOrder (rank : Nat) : AxisOrder rank :=
  ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩

/-- Dense strides for an explicit axis order, with `order 0` most significant.

The stride of `order i` is the product of the dimensions of all less-significant axes. -/
def denseStridesForOrder (dims : Vector Nat rank) (order : AxisOrder rank) : Vector Nat rank :=
  Vector.ofFn fun axis : Fin rank =>
    ∏ j : Fin rank, if order.symm axis < j then dims[order j] else 1

/-- Row-major dense strides for a tensor shape.

For example, shape `[d₀, d₁, d₂]` has row-major strides `[d₁*d₂, d₂, 1]`. -/
def rowMajorStrides (dims : Vector Nat rank) : Vector Nat rank :=
  denseStridesForOrder dims (rowMajorAxisOrder rank)

/-- Column-major dense strides for a tensor shape.

For example, shape `[d₀, d₁, d₂]` has column-major strides `[1, d₀, d₀*d₁]`. -/
def colMajorStrides (dims : Vector Nat rank) : Vector Nat rank :=
  denseStridesForOrder dims (colMajorAxisOrder rank)

/-- Total number of entries in a dense tensor with shape `dims`. -/
def numel {r : Nat} (dims : Vector Nat r) : Nat :=
  ∏ i : Fin r, dims[i]

@[simp]
theorem offsetOf_nil (stride idx : Vector Nat 0) :
    offsetOf stride idx = 0 := by
  simp [offsetOf]

theorem offsetOf_eq_sum {r : Nat} (stride idx : Vector Nat r) :
    offsetOf stride idx =
      ∑ i : Fin r, idx[i] * stride[i] :=
  rfl

end TensorIndex

end NumLean
