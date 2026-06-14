import NumLean.Data.HTuple.Ops
import Lean

namespace NumLean

namespace TensorIndex

abbrev HRank := HTuple.Profile

abbrev Shape (p : HRank) := HTuple Nat p
abbrev TIndex (α : Type u) (p : HRank) := HTuple α p
abbrev Stride {p : HRank} (D : Type u) (_shape : Shape p) := HTuple D p

namespace Shape

/-- Number of coordinates in a hierarchical shape. -/
def size {p : HRank} : Shape p → Nat
  | .leaf dim => dim
  | .prod shape₀ shape₁ => size shape₀ * size shape₁

@[simp]
theorem size_leaf (dim : Nat) : size (.leaf dim) = dim := rfl

@[simp]
theorem size_prod {p q : HRank} (shape₀ : Shape p) (shape₁ : Shape q) :
    size (.prod shape₀ shape₁) = size shape₀ * size shape₁ := rfl

end Shape

namespace TIndex

/-- A natural hierarchical coordinate is in bounds for a positive hierarchical shape. -/
def InBounds {p : HRank} (shape : Shape p) (idx : TIndex Nat p) : Prop :=
  match shape, idx with
  | .leaf dim, .leaf i => i < dim
  | .prod shape₀ shape₁, .prod idx₀ idx₁ => InBounds shape₀ idx₀ ∧ InBounds shape₁ idx₁

theorem size_pos_of_inBounds {p : HRank} {shape : Shape p} {idx : TIndex Nat p}
    (h : InBounds shape idx) : 0 < shape.size := by
  induction p with
  | leaf =>
      cases shape with | leaf dim =>
      cases idx with | leaf i =>
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) h
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases idx with | prod idx₀ idx₁ =>
      exact Nat.mul_pos (hp h.1) (hq h.2)

theorem inBounds_get {p : HRank} {shape : Shape p} {idx : TIndex Nat p}
    (h : InBounds shape idx) (axis : HTuple.Index p) : idx.get axis < shape.get axis := by
  induction p with
  | leaf =>
      cases shape with | leaf dim =>
      cases idx with | leaf i =>
      cases axis
      exact h
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases idx with | prod idx₀ idx₁ =>
      rcases h with ⟨h₀, h₁⟩
      cases axis with
      | left axis => exact hp h₀ axis
      | right axis => exact hq h₁ axis

/-- Evaluate a hierarchical coordinate against a generalized stride. -/
def offset {α : Type u} {D : Type v} [Zero D] [Add D] [SMul α D]
    {p : HRank} (idx : TIndex α p) {shape : Shape p} (stride : Stride D shape) : D :=
  HTuple.inner idx stride

end TIndex

/-- A bounded hierarchical tensor index, analogous to `Fin n`. -/
structure FinIndex {p : HRank} (shape : Shape p) where
  val : TIndex Nat p
  isLt : TIndex.InBounds shape val

namespace FinIndex

/-- Bounded hierarchical indices are equal when their underlying coordinates are equal. -/
theorem ext {p : HRank} {shape : Shape p} {idx idx' : FinIndex shape}
    (h : idx.val = idx'.val) : idx = idx' := by
  cases idx
  cases idx'
  simp at h
  subst h
  rfl

instance {p : HRank} {shape : Shape p} : CoeOut (FinIndex shape) (TIndex Nat p) where
  coe idx := idx.val

end FinIndex

/-- A hierarchical tensor layout.

A layout pairs a hierarchical `shape` with a congruent hierarchical `stride`.  Once the
codomain `D` has enough structure to add stride contributions and scale them by natural
coordinates, it induces the map

`idx ↦ idx.offset stride : TIndex α p → D`.

For ordinary memory layouts one typically takes `D = Nat` or `D = Int`, so the result is a
linear offset into a backing buffer.  Keeping `D` generic is useful because CUTE layouts are
also used to compute things that are not memory offsets.  For example, with a coordinate-like
codomain one can represent an identity coordinate layout such as `(M, N) : (e₀, e₁)`, whose
evaluation returns logical coordinates rather than an address.  Other codomains can model
swizzled/shared-memory addressing or instruction metadata.

The base layout intentionally carries no injectivity or memory-validity requirement: broadcast,
padded, coordinate-valued, and other non-compact layouts are all valid layouts.  Properties such
as injectivity, compactness, or validity for a particular backing buffer are separate predicates.

Reference note: this abstraction is inspired by the layout representation in Cris Cecka,
"CUTE Layout Representation and Algebra", NVIDIA Research, arXiv:2603.02298v1 [cs.MS],
2 Mar 2026. -/
structure Layout {p : HRank} (shape : Shape p) (D : Type u) where
  offset : D
  stride : Stride D shape

namespace Layout

/-- Evaluate a layout on a hierarchical coordinate. -/
def eval {α : Type u} {D : Type v} [Zero D] [Add D] [SMul α D]
    {p : HRank} {shape : Shape p} (layout : Layout shape D) (idx : TIndex α p) : D :=
  layout.offset + idx.offset layout.stride

-- instance {D} [Zero D] [Add D] [SMul Nat D] {shape : Shape p} :
--     CoeFun (Layout shape D) (fun _ => FinIndex shape → D) :=
--   ⟨fun layout idx => layout.eval idx.1⟩

/-- Layout that evaluates each natural coordinate to the corresponding coordinate vector. -/
def identityNatCoord {p : HRank} (shape : Shape p) : Layout shape (TIndex Nat p) where
  offset := 0
  stride := HTuple.basisTuple p

/-- Layout that evaluates each natural coordinate to the corresponding integer coordinate vector. -/
def identityIntCoord {p : HRank} (shape : Shape p) : Layout shape (TIndex Int p) where
  offset := 0
  stride := HTuple.basisTuple p

/-- The layout has no collisions on its bounded coordinate domain. -/
def Injective {D : Type u} [Zero D] [Add D] [SMul Nat D]
    {p : HRank} {shape : Shape p} (layout : Layout shape D) : Prop :=
  Function.Injective fun idx : FinIndex shape =>
    (idx : TIndex Nat p).offset layout.stride

/-- A layout only produces values in the half-open interval `[lo, hi)` on bounded coordinates. -/
def BoundedBy {D : Type u} [Zero D] [Add D] [SMul Nat D] [LE D] [LT D]
    {p : HRank} {shape : Shape p} (layout : Layout shape D) (lo hi : D) : Prop :=
  ∀ idx : FinIndex shape,
    lo ≤ (idx : TIndex Nat p).offset layout.stride ∧
      (idx : TIndex Nat p).offset layout.stride < hi

open Function in
/-- An integer-offset layout is compact when it bijects bounded coordinates with dense offsets. -/
structure Compact {p : HRank} {shape : Shape p} (layout : Layout shape Int) : Prop where
  bounded : layout.BoundedBy 0 shape.size
  bijective : Bijective fun idx : FinIndex shape =>
      (⟨(idx.1.offset layout.stride).toNat, by have := bounded idx; simp_all only [Int.toNat_lt]⟩ : Fin shape.size)

end Layout

end TensorIndex

end NumLean
