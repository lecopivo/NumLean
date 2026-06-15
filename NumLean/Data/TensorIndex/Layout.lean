import NumLean.Data.TensorIndex.FinIndex
import Mathlib.Logic.Equiv.Fin.Basic

namespace NumLean

namespace TensorIndex

namespace TIndex

end TIndex

/-- A hierarchical tensor layout.

A layout pairs a hierarchical `shape` with a congruent hierarchical `stride`. Once the codomain
`D` has enough structure to add stride contributions and scale them by natural coordinates, it
induces the map `idx ↦ idx.offset stride : TIndex α p → D`.

For ordinary memory layouts one typically takes `D = Nat` or `D = Int`, so the result is a linear
offset into a backing buffer. Keeping `D` generic is useful because CUTE layouts are also used to
compute values that are not memory offsets.

The base layout intentionally carries no injectivity or memory-validity requirement: broadcast,
padded, coordinate-valued, and other non-compact layouts are all valid layouts. Properties such as
injectivity, compactness, or validity for a particular backing buffer are separate predicates. -/
structure Layout {p : HRank} (shape : Shape p) (D : Type u) where
  offset : D
  stride : Stride D shape

namespace Layout

/-- Evaluate a layout on a hierarchical coordinate. -/
def eval {α : Type u} {D : Type v} [Zero D] [Add D] [SMul α D]
    {p : HRank} {shape : Shape p} (layout : Layout shape D) (idx : TIndex α p) : D :=
  layout.offset + idx.offset layout.stride

@[simp]
theorem leaf_eval {I : Type u} {D : Type v} [Zero D] [Add D] [SMul I D]
    (n : Nat) (offset : D) (stride : D) (i : TIndex I .leaf) :
    (Layout.mk (shape := .leaf n) offset (.leaf stride)).eval i
    =
    offset + i.offset (shape := .leaf n) (.leaf stride) := rfl

@[simp]
theorem prod_eval {I : Type u} {D : Type v} [Zero D] [Add D] [SMul I D]
    (p q : HRank) (shape : Shape p) (shape' : Shape q)
    (offset : D) (stride : Stride D shape) (stride' : Stride D shape')
    (i : TIndex I p) (j : TIndex I q) :
    (Layout.mk (shape := shape.prod shape') offset (stride.prod stride')).eval (i.prod j)
    =
    offset + (i.offset stride + j.offset stride') := by simp [eval]

/-- The layout has no collisions on its bounded coordinate domain. -/
def Injective {D : Type u} [Zero D] [Add D] [SMul Nat D]
    {p : HRank} {shape : Shape p} (layout : Layout shape D) : Prop :=
  Function.Injective fun idx : FinIndex shape => layout.eval idx.val

/-- A layout only produces values in the half-open interval `[lo, hi)` on bounded coordinates. -/
@[grind =]
def BoundedBy {D : Type u} [Zero D] [Add D] [SMul Nat D] [LE D] [LT D]
    {p : HRank} {shape : Shape p} (layout : Layout shape D) (lo hi : D) : Prop :=
  ∀ idx : FinIndex shape, lo ≤ layout.eval idx.val ∧ layout.eval idx.val < hi

open Function in
/-- An integer-offset layout is compact when it bijects bounded coordinates with dense offsets. -/
structure Compact {p : HRank} {shape : Shape p} (layout : Layout shape Int) : Prop where
  bounded : layout.BoundedBy 0 shape.size
  bijective : Bijective fun idx : FinIndex shape =>
      (⟨(layout.eval idx.val).toNat, by have := bounded idx; simp_all only [Int.toNat_lt]⟩ : Fin shape.size)

def ofFin (n : Nat) : Layout (.leaf n) Int where
  offset := 0
  stride := .leaf 1

theorem injective_ofFin {n} : (ofFin n).Injective := by
  intro ⟨.leaf i, _⟩ ⟨.leaf j, _⟩ h
  simp_all [ofFin]

theorem compact_ofFin {n} : (ofFin n).Compact := by
  constructor
  · constructor
    · intro ⟨.leaf i, _⟩ ⟨.leaf j, _⟩ h
      simp_all [ofFin]
    · intro i
      use ⟨.leaf i.1, i.2⟩
      simp_all [ofFin]
  · intro ⟨.leaf i, h⟩
    unfold TIndex.InBounds at h
    simp_all [ofFin]

/-- Layout that evaluates each natural coordinate to the corresponding coordinate vector. -/
def identityCoord {p : HRank} (α : Type u) [Zero α] [One α] (shape : Shape p) :
    Layout shape (TIndex α p) where
  offset := 0
  stride := HTuple.basisTuple p

theorem injecitve_identityNatCoord {p : HRank} (α : Type u) [AddGroupWithOne α]
    (shape : Shape p) :
    (identityCoord α shape).Injective := sorry

variable {D} [Zero D] [Add D] [SMul Nat D]

/-- Row-major product of two integer-offset layouts.

The right layout is fastest-moving, so the left layout is scaled by the size of the right shape. -/
def rowMajorProd {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ D) (layout₁ : Layout shape₁ D) :
    Layout (HTuple.prod shape₀ shape₁) D where
  offset := shape₁.size • layout₀.offset + layout₁.offset
  stride := (shape₁.size • layout₀.stride).prod layout₁.stride

@[simp]
theorem rowMajorProd_eval
    {I} {D} [AddCommGroup D] [Semiring I] [Module I D]
    {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ D) (layout₁ : Layout shape₁ D)
    (idx₀ : TIndex I p) (idx₁ : TIndex I q) :
    (layout₀.rowMajorProd layout₁).eval (idx₀.prod idx₁) =
      layout₁.eval idx₁ + shape₁.size • layout₀.eval idx₀ := by
  simp [rowMajorProd, eval, TIndex.offset_smul]
  module

@[simp]
theorem injecitve_rowMajorProd {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ D) (layout₁ : Layout shape₁ D)
    (hlayout₀ : layout₀.Injective) (hlayout₁ : layout₁.Injective) :
    (layout₀.rowMajorProd layout₁).Injective := sorry

@[simp]
theorem compact_rowMajorProd {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ Int) (layout₁ : Layout shape₁ Int)
    (hlayout₀ : layout₀.Compact) (hlayout₁ : layout₁.Compact) :
    (layout₀.rowMajorProd layout₁).Compact := sorry


/-- Column-major product of two integer-offset layouts.

The left layout is fastest-moving, so the right layout is scaled by the size of the left shape. -/
def colMajorProd {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ D) (layout₁ : Layout shape₁ D) :
    Layout (HTuple.prod shape₀ shape₁) D where
  offset := layout₀.offset + shape₀.size • layout₁.offset
  stride := layout₀.stride.prod (shape₀.size • layout₁.stride)

@[simp]
theorem injecitve_colMajorProd {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ D) (layout₁ : Layout shape₁ D)
    (hlayout₀ : layout₀.Injective) (hlayout₁ : layout₁.Injective) :
    (layout₀.colMajorProd layout₁).Injective := sorry

@[simp]
theorem compact_colMajorProd {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ Int) (layout₁ : Layout shape₁ Int)
    (hlayout₀ : layout₀.Compact) (hlayout₁ : layout₁.Compact) :
    (layout₀.colMajorProd layout₁).Injective := sorry


end Layout

end TensorIndex

end NumLean
