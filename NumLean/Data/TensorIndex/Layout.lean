import NumLean.Data.TensorIndex.FinIndex
import NumLean.Data.HTuple.Algebra
import Mathlib.Logic.Equiv.Fin.Basic

namespace NumLean

namespace TensorIndex

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
theorem compact_rowMajorProd {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ Int) (layout₁ : Layout shape₁ Int)
    (hlayout₀ : layout₀.Compact) (hlayout₁ : layout₁.Compact) :
    (layout₀.rowMajorProd layout₁).Compact := by
  let layout := layout₀.rowMajorProd layout₁
  have bounded : layout.BoundedBy 0 (Shape.size (HTuple.prod shape₀ shape₁)) := by
    intro idx
    cases idx with
    | mk val hval =>
    cases val with
    | prod idx₀ idx₁ =>
    let left : FinIndex shape₀ := ⟨idx₀, hval.1⟩
    let right : FinIndex shape₁ := ⟨idx₁, hval.2⟩
    have hleft := hlayout₀.bounded left
    have hright := hlayout₁.bounded right
    constructor
    · simp [layout]
      nlinarith [mul_nonneg (Int.natCast_nonneg shape₁.size) hleft.1, hright.1]
    · simp [layout]
      have hsize₁pos : 0 < (shape₁.size : Int) := by
        exact_mod_cast TIndex.size_pos_of_inBounds right.isLt
      have hmul : (shape₁.size : Int) * layout₀.eval left.val <
          (shape₁.size : Int) * shape₀.size :=
        mul_lt_mul_of_pos_left hleft.2 hsize₁pos
      nlinarith [hright.1, hright.2]
  refine ⟨bounded, ?_⟩
  let f : FinIndex (HTuple.prod shape₀ shape₁) → Fin (Shape.size (HTuple.prod shape₀ shape₁)) := fun idx =>
    ⟨(layout.eval idx.val).toNat, by have := bounded idx; simp_all only [Int.toNat_lt]⟩
  let f₀ : FinIndex shape₀ → Fin shape₀.size := fun idx =>
    ⟨(layout₀.eval idx.val).toNat, by have := hlayout₀.bounded idx; simp_all only [Int.toNat_lt]⟩
  let f₁ : FinIndex shape₁ → Fin shape₁.size := fun idx =>
    ⟨(layout₁.eval idx.val).toNat, by have := hlayout₁.bounded idx; simp_all only [Int.toNat_lt]⟩
  let e₀ : FinIndex shape₀ ≃ Fin shape₀.size :=
    { toFun := f₀
      invFun := fun offset => Classical.choose (hlayout₀.bijective.2 offset)
      left_inv := by
        intro idx
        exact hlayout₀.bijective.1 (Classical.choose_spec (hlayout₀.bijective.2 (f₀ idx)))
      right_inv := by
        intro offset
        exact Classical.choose_spec (hlayout₀.bijective.2 offset) }
  let e₁ : FinIndex shape₁ ≃ Fin shape₁.size :=
    { toFun := f₁
      invFun := fun offset => Classical.choose (hlayout₁.bijective.2 offset)
      left_inv := by
        intro idx
        exact hlayout₁.bijective.1 (Classical.choose_spec (hlayout₁.bijective.2 (f₁ idx)))
      right_inv := by
        intro offset
        exact Classical.choose_spec (hlayout₁.bijective.2 offset) }
  have hbij : Function.Bijective fun idx : FinIndex (HTuple.prod shape₀ shape₁) =>
      (FinIndex.prodEquiv.trans ((Equiv.prodCongr e₀ e₁).trans finProdFinEquiv)) idx :=
    (FinIndex.prodEquiv.trans ((Equiv.prodCongr e₀ e₁).trans finProdFinEquiv)).bijective
  convert hbij using 1
  ext idx
  cases idx with
  | mk val hval =>
  cases val with
  | prod idx₀ idx₁ =>
  let left : FinIndex shape₀ := ⟨idx₀, hval.1⟩
  let right : FinIndex shape₁ := ⟨idx₁, hval.2⟩
  simp [f₀, f₁, e₀, e₁, FinIndex.prodEquiv, finProdFinEquiv]
  have hleft_nonneg : 0 ≤ layout₀.eval idx₀ := by
    simpa [left] using (hlayout₀.bounded left).1
  have hright_nonneg : 0 ≤ layout₁.eval idx₁ := by
    simpa [right] using (hlayout₁.bounded right).1
  have hmul_nonneg : 0 ≤ (shape₁.size : Int) * layout₀.eval idx₀ :=
    mul_nonneg (Int.natCast_nonneg shape₁.size) hleft_nonneg
  have hsum_nonneg : 0 ≤ layout₁.eval idx₁ + (shape₁.size : Int) * layout₀.eval idx₀ := by
    nlinarith
  apply Nat.cast_injective (R := Int)
  rw [Int.toNat_of_nonneg hsum_nonneg, Nat.cast_add, Nat.cast_mul,
    Int.toNat_of_nonneg hright_nonneg, Int.toNat_of_nonneg hleft_nonneg]

/-- Column-major product of two integer-offset layouts.

The left layout is fastest-moving, so the right layout is scaled by the size of the left shape. -/
def colMajorProd {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ D) (layout₁ : Layout shape₁ D) :
    Layout (HTuple.prod shape₀ shape₁) D where
  offset := layout₀.offset + shape₀.size • layout₁.offset
  stride := layout₀.stride.prod (shape₀.size • layout₁.stride)

@[simp]
theorem colMajorProd_eval
    {I} {D} [AddCommGroup D] [Semiring I] [Module I D]
    {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ D) (layout₁ : Layout shape₁ D)
    (idx₀ : TIndex I p) (idx₁ : TIndex I q) :
    (layout₀.colMajorProd layout₁).eval (idx₀.prod idx₁) =
      layout₀.eval idx₀ + shape₀.size • layout₁.eval idx₁ := by
  simp [colMajorProd, eval, TIndex.offset_smul]
  module

@[simp]
theorem compact_colMajorProd {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ Int) (layout₁ : Layout shape₁ Int)
    (hlayout₀ : layout₀.Compact) (hlayout₁ : layout₁.Compact) :
    (layout₀.colMajorProd layout₁).Compact := by
  let layout := layout₀.colMajorProd layout₁
  have bounded : layout.BoundedBy 0 (Shape.size (HTuple.prod shape₀ shape₁)) := by
    intro idx
    cases idx with
    | mk val hval =>
    cases val with
    | prod idx₀ idx₁ =>
    let left : FinIndex shape₀ := ⟨idx₀, hval.1⟩
    let right : FinIndex shape₁ := ⟨idx₁, hval.2⟩
    have hleft := hlayout₀.bounded left
    have hright := hlayout₁.bounded right
    constructor
    · simp [layout]
      nlinarith [mul_nonneg (Int.natCast_nonneg shape₀.size) hright.1, hleft.1]
    · simp [layout]
      have hsize₀pos : 0 < (shape₀.size : Int) := by
        exact_mod_cast TIndex.size_pos_of_inBounds left.isLt
      have hmul : (shape₀.size : Int) * layout₁.eval right.val <
          (shape₀.size : Int) * shape₁.size :=
        mul_lt_mul_of_pos_left hright.2 hsize₀pos
      nlinarith [hleft.1, hleft.2]
  refine ⟨bounded, ?_⟩
  let f : FinIndex (HTuple.prod shape₀ shape₁) → Fin (Shape.size (HTuple.prod shape₀ shape₁)) := fun idx =>
    ⟨(layout.eval idx.val).toNat, by have := bounded idx; simp_all only [Int.toNat_lt]⟩
  let f₀ : FinIndex shape₀ → Fin shape₀.size := fun idx =>
    ⟨(layout₀.eval idx.val).toNat, by have := hlayout₀.bounded idx; simp_all only [Int.toNat_lt]⟩
  let f₁ : FinIndex shape₁ → Fin shape₁.size := fun idx =>
    ⟨(layout₁.eval idx.val).toNat, by have := hlayout₁.bounded idx; simp_all only [Int.toNat_lt]⟩
  let e₀ : FinIndex shape₀ ≃ Fin shape₀.size :=
    { toFun := f₀
      invFun := fun offset => Classical.choose (hlayout₀.bijective.2 offset)
      left_inv := by
        intro idx
        exact hlayout₀.bijective.1 (Classical.choose_spec (hlayout₀.bijective.2 (f₀ idx)))
      right_inv := by
        intro offset
        exact Classical.choose_spec (hlayout₀.bijective.2 offset) }
  let e₁ : FinIndex shape₁ ≃ Fin shape₁.size :=
    { toFun := f₁
      invFun := fun offset => Classical.choose (hlayout₁.bijective.2 offset)
      left_inv := by
        intro idx
        exact hlayout₁.bijective.1 (Classical.choose_spec (hlayout₁.bijective.2 (f₁ idx)))
      right_inv := by
        intro offset
        exact Classical.choose_spec (hlayout₁.bijective.2 offset) }
  have hbij : Function.Bijective fun idx : FinIndex (HTuple.prod shape₀ shape₁) =>
      (FinIndex.prodEquiv.trans ((Equiv.prodCongr e₀ e₁).trans
        ((Equiv.prodComm (Fin shape₀.size) (Fin shape₁.size)).trans
          (finProdFinEquiv.trans (finCongr (Nat.mul_comm shape₁.size shape₀.size)))))) idx :=
    (FinIndex.prodEquiv.trans ((Equiv.prodCongr e₀ e₁).trans
      ((Equiv.prodComm (Fin shape₀.size) (Fin shape₁.size)).trans
        (finProdFinEquiv.trans (finCongr (Nat.mul_comm shape₁.size shape₀.size)))))).bijective
  convert hbij using 1
  ext idx
  cases idx with
  | mk val hval =>
  cases val with
  | prod idx₀ idx₁ =>
  let left : FinIndex shape₀ := ⟨idx₀, hval.1⟩
  let right : FinIndex shape₁ := ⟨idx₁, hval.2⟩
  simp [f₀, f₁, e₀, e₁, FinIndex.prodEquiv, finProdFinEquiv]
  have hleft_nonneg : 0 ≤ layout₀.eval idx₀ := by
    simpa [left] using (hlayout₀.bounded left).1
  have hright_nonneg : 0 ≤ layout₁.eval idx₁ := by
    simpa [right] using (hlayout₁.bounded right).1
  have hmul_nonneg : 0 ≤ (shape₀.size : Int) * layout₁.eval idx₁ :=
    mul_nonneg (Int.natCast_nonneg shape₀.size) hright_nonneg
  have hsum_nonneg : 0 ≤ layout₀.eval idx₀ + (shape₀.size : Int) * layout₁.eval idx₁ := by
    nlinarith
  apply Nat.cast_injective (R := Int)
  rw [Int.toNat_of_nonneg hsum_nonneg, Nat.cast_add, Nat.cast_mul,
    Int.toNat_of_nonneg hleft_nonneg, Int.toNat_of_nonneg hright_nonneg]

end Layout

end TensorIndex

end NumLean
