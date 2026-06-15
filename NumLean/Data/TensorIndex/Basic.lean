import NumLean.Data.HTuple.Ops
import Mathlib.Logic.Equiv.Fin.Basic

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

@[simp]
theorem offset_leaf {I : Type u} {D : Type v} [Zero D] [Add D] [SMul I D]
    (n : Nat) (stride : D) (i : I) :
    TIndex.offset (shape := .leaf n) (.leaf i) (.leaf stride)
    =
    i • stride := rfl

@[simp]
theorem offset_prod {I : Type u} {D : Type v} [Zero D] [Add D] [SMul I D]
    (p q : HRank) (shape : Shape p) (shape' : Shape q)
    (stride : Stride D shape) (stride' : Stride D shape')
    (i : TIndex I p) (j : TIndex I q) :
    TIndex.offset (shape := .prod shape shape') (i.prod j) (stride.prod stride')
    =
    i.offset stride + j.offset stride' := by
  simp [TIndex.offset, HTuple.inner, HTuple.innerWith]

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

end TensorIndex

end NumLean
