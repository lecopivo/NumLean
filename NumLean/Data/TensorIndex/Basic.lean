import Mathlib.Data.Vector.Basic
import Mathlib.Tactic
import Init.Data.Iterators
import Init.Data.Iterators.Consumers.Monadic.Loop

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

instance {r} {dims : Vector Nat r} : CoeOut (TensorIndex dims) (Vector Nat r) := ⟨(·.val)⟩

/-- Flat offset for a raw tensor index and one flat stride per tensor axis. -/
def offsetOf {rank : Nat} (strides : Vector Int rank) (idx : Vector Nat rank) : Int :=
  ∑ i : Fin rank, idx[i] * strides[i]

/-- Flat offset for a bounded tensor index and one flat stride per tensor axis. -/
def offset (idx : TensorIndex dims) (strides : Vector Int rank) : Int :=
  offsetOf strides idx.val

/-- Valid strides are those whose offset map is injective on the bounded tensor index set. -/
def InjectiveStrides {rank : Nat} (dims : Vector Nat rank) (strides : Vector Int rank) : Prop :=
  Function.Injective fun idx : TensorIndex dims => offset idx strides

/-- In bounds strides produce offset values in the range `[lo, hi]`. -/
def InBoundsStrides {r} (dims : Vector Nat r) (strides : Vector Int r) (lo hi : Int) : Prop :=
  ∀ idx : TensorIndex dims, lo ≤ idx.offset strides ∧ idx.offset strides ≤ hi

structure IsLayoutStrides {r} (dims : Vector Nat r) (strides : Vector Int r) (n : Nat) : Prop where
  in_bounds : InBoundsStrides dims strides 0 (n-1)
  bijective : Function.Bijective (fun idx : TensorIndex dims =>
    Fin.mk (n:=n) (idx.offset strides).toNat (by have := in_bounds idx; grind))

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
theorem offsetOf_nil (strides : Vector Int 0) (idx : Vector Nat 0) :
    offsetOf strides idx = 0 := by
  simp [offsetOf]

theorem offsetOf_eq_sum {r : Nat} (strides : Vector Int r) (idx : Vector Nat r) :
    offsetOf strides idx =
      ∑ i : Fin r, idx[i] * strides[i] :=
  rfl

theorem numel_decomp_succ {n : Nat} (dims : Vector Nat (n + 1)) :
    numel dims = dims[0] * numel (Vector.ofFn fun j : Fin n => dims[j.succ]) := by
  unfold numel
  rw [Fin.prod_univ_succ]
  simp

/-- Add one leading coordinate to a tensor index. -/
def cons {rank : Nat} {dims : Vector Nat (rank + 1)}
    (i : Fin dims[0])
    (tail : TensorIndex (Vector.ofFn fun j : Fin rank => dims[j.succ])) :
    TensorIndex dims where
  val := Vector.ofFn fun axis : Fin (rank + 1) =>
    match axis with
    | ⟨0, _⟩ => i.1
    | ⟨k + 1, hk⟩ => tail.val.get ⟨k, by omega⟩
  valid := by
    intro axis
    cases axis with
    | mk axis haxis =>
      cases axis with
      | zero => simp [i.2]
      | succ k =>
          simpa using tail.valid ⟨k, by omega⟩

/-- Decode a dense row-major flat index into a tensor index. -/
def unflattenRowMajor : {rank : Nat} → (dims : Vector Nat rank) →
    Fin (numel dims) → TensorIndex dims
  | 0, dims, _ =>
      { val := Vector.ofFn fun i : Fin 0 => i.elim0
        valid := by intro i; exact i.elim0 }
  | rank + 1, dims, flat =>
      let tailDims := Vector.ofFn fun j : Fin rank => dims[j.succ]
      let tailNumel := numel tailDims
      have hflat : flat.1 < dims[0] * tailNumel := by
        change flat.1 < dims[0] * numel tailDims
        simpa [tailDims, numel_decomp_succ] using flat.2
      have htailPos : 0 < tailNumel := by
        exact Nat.pos_of_ne_zero fun hzero => by
          rw [hzero, Nat.mul_zero] at hflat
          exact Nat.not_lt_zero _ hflat
      let head : Fin dims[0] :=
        ⟨flat.1 / tailNumel, by
          rw [Nat.div_lt_iff_lt_mul htailPos]
          simpa only [Nat.mul_comm dims[0] tailNumel] using hflat⟩
      let tail : TensorIndex tailDims :=
        unflattenRowMajor tailDims ⟨flat.1 % tailNumel, Nat.mod_lt _ htailPos⟩
      cons head tail

/-- Decode a dense flat index into a tensor index using an explicit axis order.

Currently this shares the row-major decoder; `rangeForOrder` carries the order in its iterator state
so the public API is ready for an order-specialized decoder. -/
def unflattenForOrder {rank : Nat} (dims : Vector Nat rank)
    (_axis : AxisOrder rank) : Fin (numel dims) → TensorIndex dims :=
  unflattenRowMajor dims

namespace Iterator

open Std

/-- Internal state for iterating over tensor indices. -/
structure State {rank : Nat} (dims : Vector Nat rank) (axis : AxisOrder rank) where
  pos : Nat

@[always_inline, inline]
instance {rank : Nat} {dims : Vector Nat rank} {axis : AxisOrder rank} [Pure m] :
    Iterator (State dims axis) m (TensorIndex dims) where
  IsPlausibleStep _ _ := True
  step it := pure <| Std.Shrink.deflate <|
    if h : it.internalState.pos < numel dims then
      let idx := unflattenForOrder dims axis ⟨it.internalState.pos, h⟩
      ⟨.yield (⟨{ pos := it.internalState.pos + 1 }⟩ : IterM m (TensorIndex dims)) idx, trivial⟩
    else
      ⟨.done, trivial⟩

@[always_inline, inline]
instance {rank : Nat} {dims : Vector Nat rank} {axis : AxisOrder rank} [Monad m]
    {n : Type x → Type x'} [Monad n] :
    IteratorLoop (State dims axis) m n :=
  .defaultImplementation

end Iterator

/-- Iterate over all tensor indices for a shape using Lean's `Std.Iter` API. -/
@[always_inline, inline]
def range {rank : Nat} (dims : Vector Nat rank)
    (axis : AxisOrder rank := rowMajorAxisOrder rank) :
    Std.Iter (α := Iterator.State dims axis) (TensorIndex dims) :=
  (⟨{ pos := 0 }⟩ : Std.Iter (α := Iterator.State dims axis) (TensorIndex dims))

end TensorIndex

end NumLean
