import NumLean.Data.TensorIndex.IntFinTIndex
-- import NumLean.Data.TensorIndex.AxisOrder
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
    offset + (i.offset stride + j.offset stride') := rfl

/-- The layout has no collisions on its bounded coordinate domain. -/
def Injective {D : Type u} [Zero D] [Add D] [SMul Nat D]
    {p : HRank} {shape : Shape p} (layout : Layout shape D) : Prop :=
  Function.Injective fun idx : FinTIndex shape => layout.eval idx.val

def InBoundsInt
    {p q : HRank} {shape : Shape p} (layout : Layout shape (TIndex Int q)) (shape' : Shape q) : Prop :=
  ∀ idx : FinTIndex shape, TIndex.InBoundsInt shape' (layout.eval idx.val)

def InBounds
    {p q : HRank} {shape : Shape p} (layout : Layout shape (TIndex Nat q)) (shape' : Shape q) : Prop :=
  ∀ idx : FinTIndex shape, TIndex.InBounds shape' (layout.eval idx.val)

def evalToFinTIndex {p q : HRank} {shape : Shape p} {shape' : Shape q}
    (layout : Layout shape (TIndex Nat q))
    (inBounds : layout.InBounds shape') :
    FinTIndex shape → FinTIndex shape' :=
  fun idx => { val := layout.eval idx.val, isLt := inBounds idx }

def evalToIntFinTIndex {p q : HRank} {shape : Shape p} {shape' : Shape q}
    (layout : Layout shape (TIndex Int q))
    (inBounds : layout.InBoundsInt shape') :
    FinTIndex shape → IntFinTIndex shape' :=
  fun idx => { val := layout.eval idx.val, isLt := inBounds idx }

/-- A layout only produces values in the half-open interval `[lo, hi)` on bounded coordinates. -/
@[grind =]
def BoundedBy {D : Type u} [Zero D] [Add D] [SMul Nat D] [LE D] [LT D]
    {p : HRank} {shape : Shape p} (layout : Layout shape D) (lo hi : D) : Prop :=
  ∀ idx : FinTIndex shape, lo ≤ layout.eval idx.val ∧ layout.eval idx.val < hi

def evalToFin {p : HRank} {shape : Shape p} {n : Nat}
    (layout : Layout shape Int)
    (inBounds : layout.BoundedBy 0 n) :
    FinTIndex shape → Fin n :=
  fun idx => { val := (layout.eval idx.val).toNat, isLt := by have := inBounds idx; grind }

open Function in
/-- An integer-offset layout is compact when it bijects bounded coordinates with dense offsets. -/
structure Compact {p : HRank} {shape : Shape p} (layout : Layout shape Int) : Prop where
  bounded : layout.BoundedBy 0 shape.size
  bijective : Bijective (layout.evalToFin bounded)

def ofFin (n : Nat) : Layout (.leaf n) Int where
  offset := 0
  stride := .leaf 1

theorem injective_ofFin {n} : (ofFin n).Injective := by
  intro ⟨.leaf i, _⟩ ⟨.leaf j, _⟩ h
  apply FinTIndex.ext
  simp [ofFin, eval, TIndex.offset, HTuple.inner, HTuple.innerWith] at h ⊢
  exact h

theorem compact_ofFin {n} : (ofFin n).Compact := by
  let layout := ofFin n
  have bounded : layout.BoundedBy 0 n := by
    intro idx
    cases idx with
    | mk val h =>
    cases val with
    | leaf i =>
      constructor
      · simp [layout, ofFin, eval, TIndex.offset, HTuple.inner, HTuple.innerWith]
      · simpa [layout, ofFin, eval, TIndex.offset, HTuple.inner, HTuple.innerWith] using h
  refine ⟨bounded, ?_⟩
  convert (FinTIndex.leafEquiv n).bijective using 1
  ext idx
  cases idx with
  | mk val h =>
  cases val with
  | leaf i =>
    simp [evalToFin, ofFin, TIndex.offset, HTuple.inner, HTuple.innerWith, FinTIndex.leafEquiv]

/-- Layout that evaluates each natural coordinate to the corresponding coordinate vector. -/
def identityCoord {p : HRank} (α : Type u) [Zero α] [One α] (shape : Shape p) :
    Layout shape (TIndex α p) where
  offset := 0
  stride := HTuple.basisTuple p

variable {D} [Zero D] [Add D] [SMul Nat D]

/-- Paper-style concatenation of two layouts into a product-shaped layout.

This is the algebraic operation `L = (L₀, L₁)`: evaluating the result on a product
coordinate adds the evaluations of the two sublayouts. It is intentionally different from
`rowMajorProd` and `colMajorProd`, which additionally scale strides to build dense flat orders. -/
def concat {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ D) (layout₁ : Layout shape₁ D) :
    Layout (HTuple.prod shape₀ shape₁) D where
  offset := layout₀.offset + layout₁.offset
  stride := layout₀.stride.prod layout₁.stride

@[simp]
theorem concat_eval
    {I} {D} [AddCommMonoid D] [SMul I D]
    {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ D) (layout₁ : Layout shape₁ D)
    (idx₀ : TIndex I p) (idx₁ : TIndex I q) :
    (layout₀.concat layout₁).eval (idx₀.prod idx₁) =
      layout₀.eval idx₀ + layout₁.eval idx₁ := by
  simp [concat, eval]
  ac_rfl

/-- Compose a layout with a coordinate-valued layout.

The inner layout computes coordinates for the outer layout. This is the direct, type-safe form of
layout composition; flat/integer composition should be a separate operation because it needs
additional admissibility/coalescing data. -/
def compose {p q : HRank} {outerShape : Shape p} {innerShape : Shape q}
    [SMul Int D]
    (outer : Layout outerShape D) (inner : Layout innerShape (TIndex Int p)) :
    Layout innerShape D where
  offset := outer.eval inner.offset
  stride := HTuple.map (fun coordStride => coordStride.offset outer.stride) inner.stride

@[simp]
theorem compose_eval
    {D} [AddCommMonoid D] [Module Int D]
    {p q : HRank} {outerShape : Shape p} {innerShape : Shape q}
    (outer : Layout outerShape D) (inner : Layout innerShape (TIndex Int p))
    (idx : TIndex Int q) :
    (outer.compose inner).eval idx = outer.eval (inner.eval idx) := by
  simp [compose, eval]
  rw [show idx.offset (HTuple.map (fun coordStride => coordStride.offset outer.stride) inner.stride) =
      (idx.offset inner.stride).offset outer.stride from
    TIndex.offset_map_offset (R := Int) idx inner.stride outer.stride]
  rw [TIndex.offset_add_left (R := Int) inner.offset (idx.offset inner.stride) outer.stride]
  ac_rfl

@[simp]
theorem compose_identityCoord
    {D} [AddCommMonoid D] [Module Int D]
    {p : HRank} {shape : Shape p} (layout : Layout shape D) :
    layout.compose (identityCoord Int shape) = layout := by
  cases layout with
  | mk offset stride =>
      simp [compose, identityCoord, eval]

-- /-- A bijective bounded coordinate-valued layout forces source and target domains to have the same size. -/
-- theorem domain_size_eq_of_bijective {p q : HRank} {targetShape : Shape p} {shape : Shape q}
--     (layout : Layout shape (TIndex Int p))
--     (inBounds : ∀ idx : FinTIndex shape, TIndex.InBoundsInt targetShape (layout.eval idx.val))
--     (hbij : Function.Bijective (layout.evalToFinTIndex inBounds)) :
--     shape.size = targetShape.size := by
--   have hcard := Fintype.card_congr
--     { toFun := layout.evalToFinTIndex inBounds
--       invFun := fun idx => Classical.choose (hbij.2 idx)
--       left_inv := by
--         intro idx
--         exact hbij.1 (Classical.choose_spec (hbij.2 (layout.evalToFinTIndex inBounds idx)))
--       right_inv := by
--         intro idx
--         exact Classical.choose_spec (hbij.2 idx) }
--   simpa [FinTIndex.card_eq_shape_size] using hcard

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
  sorry
  -- let layout := layout₀.rowMajorProd layout₁
  -- have bounded : layout.BoundedBy 0 (Shape.size (HTuple.prod shape₀ shape₁)) := by
  --   intro idx
  --   cases idx with
  --   | mk val hval =>
  --   cases val with
  --   | prod idx₀ idx₁ =>
  --   let left : FinTIndex shape₀ := ⟨idx₀, hval.1⟩
  --   let right : FinTIndex shape₁ := ⟨idx₁, hval.2⟩
  --   have hleft := hlayout₀.bounded left
  --   have hright := hlayout₁.bounded right
  --   constructor
  --   · simp [layout]
  --     nlinarith [mul_nonneg (Int.natCast_nonneg shape₁.size) hleft.1, hright.1]
  --   · simp [layout]
  --     have hsize₁pos : 0 < (shape₁.size : Int) := by
  --       exact_mod_cast TIndex.size_pos_of_inBounds right.isLt
  --     have hmul : (shape₁.size : Int) * layout₀.eval left.val <
  --         (shape₁.size : Int) * shape₀.size :=
  --       mul_lt_mul_of_pos_left hleft.2 hsize₁pos
  --     nlinarith [hright.1, hright.2]
  -- refine ⟨bounded, ?_⟩
  -- let f : FinTIndex (HTuple.prod shape₀ shape₁) → Fin (Shape.size (HTuple.prod shape₀ shape₁)) := fun idx =>
  --   ⟨(layout.eval idx.val).toNat, by have := bounded idx; simp_all only [Int.toNat_lt]⟩
  -- let f₀ : FinTIndex shape₀ → Fin shape₀.size := fun idx =>
  --   ⟨(layout₀.eval idx.val).toNat, by have := hlayout₀.bounded idx; simp_all only [Int.toNat_lt]⟩
  -- let f₁ : FinTIndex shape₁ → Fin shape₁.size := fun idx =>
  --   ⟨(layout₁.eval idx.val).toNat, by have := hlayout₁.bounded idx; simp_all only [Int.toNat_lt]⟩
  -- let e₀ : FinTIndex shape₀ ≃ Fin shape₀.size :=
  --   { toFun := f₀
  --     invFun := fun offset => Classical.choose (hlayout₀.bijective.2 offset)
  --     left_inv := by
  --       intro idx
  --       exact hlayout₀.bijective.1 (Classical.choose_spec (hlayout₀.bijective.2 (f₀ idx)))
  --     right_inv := by
  --       intro offset
  --       exact Classical.choose_spec (hlayout₀.bijective.2 offset) }
  -- let e₁ : FinTIndex shape₁ ≃ Fin shape₁.size :=
  --   { toFun := f₁
  --     invFun := fun offset => Classical.choose (hlayout₁.bijective.2 offset)
  --     left_inv := by
  --       intro idx
  --       exact hlayout₁.bijective.1 (Classical.choose_spec (hlayout₁.bijective.2 (f₁ idx)))
  --     right_inv := by
  --       intro offset
  --       exact Classical.choose_spec (hlayout₁.bijective.2 offset) }
  -- have hbij : Function.Bijective fun idx : FinTIndex (HTuple.prod shape₀ shape₁) =>
  --     (FinTIndex.prodEquiv.trans ((Equiv.prodCongr e₀ e₁).trans finProdFinEquiv)) idx :=
  --   (FinTIndex.prodEquiv.trans ((Equiv.prodCongr e₀ e₁).trans finProdFinEquiv)).bijective
  -- convert hbij using 1
  -- ext idx
  -- cases idx with
  -- | mk val hval =>
  -- cases val with
  -- | prod idx₀ idx₁ =>
  -- let left : FinTIndex shape₀ := ⟨idx₀, hval.1⟩
  -- let right : FinTIndex shape₁ := ⟨idx₁, hval.2⟩
  -- simp [evalToFin, f₀, f₁, e₀, e₁, FinTIndex.prodEquiv, finProdFinEquiv]
  -- have hleft_nonneg : 0 ≤ layout₀.eval idx₀ := by
  --   simpa [left] using (hlayout₀.bounded left).1
  -- have hright_nonneg : 0 ≤ layout₁.eval idx₁ := by
  --   simpa [right] using (hlayout₁.bounded right).1
  -- have hmul_nonneg : 0 ≤ (shape₁.size : Int) * layout₀.eval idx₀ :=
  --   mul_nonneg (Int.natCast_nonneg shape₁.size) hleft_nonneg
  -- have hsum_nonneg : 0 ≤ layout₁.eval idx₁ + (shape₁.size : Int) * layout₀.eval idx₀ := by
  --   nlinarith
  -- apply Nat.cast_injective (R := Int)
  -- rw [Int.toNat_of_nonneg hsum_nonneg, Nat.cast_add, Nat.cast_mul,
  --   Int.toNat_of_nonneg hright_nonneg, Int.toNat_of_nonneg hleft_nonneg]


/-- Row-major dense stride for a hierarchical shape. -/
def rowMajor {p : HRank} (shape : Shape p) : Layout shape Int :=
  { offset := 0
    stride := TIndex.rowMajorStride shape }

theorem ofFin_eq_rowMajor : ofFin n = rowMajor (.leaf n) := by rfl

@[simp]
theorem rowMajorProd_rowMajor {p q : HRank} {shape₀ : Shape p} {shape₁ : Shape q} :
    (rowMajor shape₀).rowMajorProd (rowMajor shape₁)
    =
    rowMajor (shape₀.prod shape₁) := rfl

@[simp]
theorem rowMajor_eval_leaf [SMul I Int] (i : I) :
    (rowMajor (.leaf n)).eval (.leaf i) = i • 1 := by
  simp [rowMajor, TIndex.rowMajorStride]

@[simp]
theorem rowMajor_eval_prod {I : Type u} [Semiring I] [Module I Int] {r₁ r₂}
    {shape₁ : Shape r₁} {shape₂ : Shape r₂}
    (idx₁ : TIndex I r₁) (idx₂ : TIndex I r₂) :
    (rowMajor (.prod shape₁ shape₂)).eval (.prod idx₁ idx₂) =
    shape₂.size • (rowMajor shape₁).eval idx₁ + (rowMajor shape₂).eval idx₂ := by
  simp [rowMajor, TIndex.rowMajorStride, eval, -nsmul_eq_mul, TIndex.offset_smul]

theorem compact_rowMajor {r} {shape : Shape r} : (rowMajor shape).Compact := by
  induction shape
  case leaf =>
    rw [← ofFin_eq_rowMajor]
    exact compact_ofFin
  case prod =>
    rw [← rowMajorProd_rowMajor]
    apply compact_rowMajorProd <;> assumption

end Layout

end TensorIndex

end NumLean
