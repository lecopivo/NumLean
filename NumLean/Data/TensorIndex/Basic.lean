import NumLean.Data.HTuple.Algebra
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

namespace NumLean

namespace TensorIndex

abbrev HRank := HTuple.Profile

abbrev Shape (p : HRank) := HTuple Nat p
abbrev TIndex (α : Type u) (p : HRank) := HTuple α p
abbrev Stride {p : HRank} (D : Type u) (_shape : Shape p) := HTuple D p

namespace Shape

/-- Number of coordinates in a hierarchical shape. -/
@[inline] def size {p : HRank} : Shape p → Nat
  | .leaf dim => dim
  | .prod shape₀ shape₁ => size shape₀ * size shape₁

@[simp]
theorem size_leaf (dim : Nat) : size (.leaf dim) = dim := rfl

@[simp]
theorem size_prod {p q : HRank} (shape₀ : Shape p) (shape₁ : Shape q) :
    size (.prod shape₀ shape₁) = size shape₀ * size shape₁ := rfl

end Shape

namespace TIndex

/-- A natural hierarchical coordinate is in bounds for a hierarchical shape. -/
@[inline] def InBounds {p : HRank} (shape : Shape p) (idx : TIndex Nat p) : Prop :=
  match shape, idx with
  | .leaf dim, .leaf i => i < dim
  | .prod shape₀ shape₁, .prod idx₀ idx₁ => InBounds shape₀ idx₀ ∧ InBounds shape₁ idx₁

/-- An integer hierarchical coordinate is in bounds for a positive hierarchical shape. -/
@[inline] def InBoundsInt {p : HRank} (shape : Shape p) (idx : TIndex Int p) : Prop :=
  match shape, idx with
  | .leaf dim, .leaf i => 0 ≤ i ∧ i < dim
  | .prod shape₀ shape₁, .prod idx₀ idx₁ => InBoundsInt shape₀ idx₀ ∧ InBoundsInt shape₁ idx₁

theorem size_pos_of_inBoundsInt {p : HRank} {shape : Shape p} {idx : TIndex Int p}
    (h : InBoundsInt shape idx) : 0 < shape.size := by
  induction p with
  | leaf =>
      cases shape with | leaf dim =>
      cases idx with | leaf i =>
      simp [InBoundsInt] at h
      by_contra hdim
      have hdim0 : dim = 0 := Nat.eq_zero_of_not_pos hdim
      have hdim0Int : (dim : Int) = 0 := by exact_mod_cast hdim0
      omega
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases idx with | prod idx₀ idx₁ =>
      exact Nat.mul_pos (hp h.1) (hq h.2)

theorem inBoundsInt_get {p : HRank} {shape : Shape p} {idx : TIndex Int p}
    (h : InBoundsInt shape idx) (axis : HTuple.Index p) : idx.get axis < shape.get axis := by
  induction p with
  | leaf =>
      cases shape with | leaf dim =>
      cases idx with | leaf i =>
      cases axis
      exact h.2
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases idx with | prod idx₀ idx₁ =>
      rcases h with ⟨h₀, h₁⟩
      cases axis with
      | left axis => exact hp h₀ axis
      | right axis => exact hq h₁ axis

theorem inBoundsInt_of_get {p : HRank} {shape : Shape p} {idx : TIndex Int p}
    (h : ∀ axis : HTuple.Index p, 0 ≤ idx.get axis ∧ idx.get axis < shape.get axis) :
    InBoundsInt shape idx := by
  induction p with
  | leaf =>
      cases shape with | leaf dim =>
      cases idx with | leaf i =>
      exact h HTuple.Index.leaf
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases idx with | prod idx₀ idx₁ =>
      constructor
      · exact hp (fun axis => h (.left axis))
      · exact hq (fun axis => h (.right axis))

theorem inBounds_of_get {p : HRank} {shape : Shape p} {idx : TIndex Nat p}
    (h : ∀ axis : HTuple.Index p, idx.get axis < shape.get axis) :
    InBounds shape idx := by
  induction p with
  | leaf =>
      cases shape with | leaf dim =>
      cases idx with | leaf i =>
      exact h HTuple.Index.leaf
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases idx with | prod idx₀ idx₁ =>
      constructor
      · exact hp (fun axis => h (.left axis))
      · exact hq (fun axis => h (.right axis))

/-- Evaluate a hierarchical coordinate against a generalized stride. -/
@[inline] def offset {α : Type u} {D : Type v} [Zero D] [Add D] [SMul α D]
    {p : HRank} (idx : TIndex α p) {shape : Shape p} (stride : Stride D shape) : D :=
  HTuple.inner idx stride

@[inline] def rowMajorStride {r} (shape : Shape r) : Stride Int shape :=
  match shape with
  | .leaf _ => .leaf 1
  | .prod shape₁ shape₂ =>
    let s₁ := rowMajorStride shape₁
    let s₂ := rowMajorStride shape₂
    .prod (Shape.size shape₂ • s₁) s₂

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

theorem offset_smul {I : Type u} {D : Type v} [AddCommGroup D] [Semiring I] [Module I D]
    (p : HRank) (shape : Shape p) (idx : TIndex I p) (stride : Stride D shape) (n : Nat) :
    idx.offset (n • stride) =
    n • idx.offset stride := by
  exact HTuple.inner_smul_right idx stride n

@[simp]
theorem offset_zero_left {R : Type u} {D : Type v} [Semiring R] [AddCommMonoid D] [Module R D]
    {p : HRank} {shape : Shape p} (stride : Stride D shape) :
    (0 : TIndex R p).offset stride = 0 := by
  exact HTuple.inner_zero_left stride

theorem offset_add_left {R : Type u} {D : Type v} [Semiring R] [AddCommMonoid D] [Module R D]
    {p : HRank} {shape : Shape p} (idx idx' : TIndex R p) (stride : Stride D shape) :
    (idx + idx').offset stride = idx.offset stride + idx'.offset stride := by
  exact HTuple.inner_add_left idx idx' stride

theorem offset_smul_left {R : Type u} {D : Type v} [Semiring R] [AddCommMonoid D] [Module R D]
    {p : HRank} {shape : Shape p} (n : R) (idx : TIndex R p) (stride : Stride D shape) :
    (n • idx).offset stride = n • idx.offset stride := by
  exact HTuple.inner_smul_left n idx stride

theorem offset_map_offset {R : Type u} {D : Type v} [Semiring R] [AddCommMonoid D] [Module R D]
    {p q : HRank} {shape : Shape p} {shape' : Shape q}
    (idx : TIndex R q) (strides : Stride (TIndex R p) shape')
    (stride : Stride D shape) :
    idx.offset (shape := shape') (HTuple.map (fun coord => coord.offset stride) strides) =
      (idx.offset (shape := shape') strides).offset stride := by
  exact HTuple.inner_map_inner idx strides stride

theorem offset_map_prod_left {R : Type u} [Semiring R] {p q r : HRank} {shape : Shape r}
    (idx : TIndex R r) (strides : Stride (TIndex R p) shape) :
    idx.offset (shape := shape)
        (HTuple.map (fun x => HTuple.prod x (0 : TIndex R q)) strides) =
      HTuple.prod (idx.offset (shape := shape) strides) 0 := by
  exact HTuple.inner_map_prod_left idx strides

theorem offset_map_prod_right {R : Type u} [Semiring R] {p q r : HRank} {shape : Shape r}
    (idx : TIndex R r) (strides : Stride (TIndex R q) shape) :
    idx.offset (shape := shape)
        (HTuple.map (fun x => HTuple.prod (0 : TIndex R p) x) strides) =
      HTuple.prod 0 (idx.offset (shape := shape) strides) := by
  exact HTuple.inner_map_prod_right idx strides

@[simp]
theorem offset_basisTuple {R : Type u} [Semiring R] {p : HRank} {shape : Shape p} (idx : TIndex R p) :
    idx.offset (shape := shape) (HTuple.basisTuple p) = idx := by
  exact HTuple.inner_basisTuple idx

@[simp]
theorem map_offset_basisTuple {R : Type u} {D : Type v} [Semiring R] [AddCommMonoid D] [Module R D]
    {p : HRank} {shape : Shape p} (stride : Stride D shape) :
    HTuple.map (fun coord : TIndex R p => coord.offset stride) (HTuple.basisTuple p) = stride := by
  exact HTuple.map_inner_basisTuple stride

end TIndex

/-- A bounded natural hierarchical tensor index, analogous to `Fin n`. -/
structure FinTIndex {p : HRank} (shape : Shape p) where
  val : TIndex Nat p
  isLt : TIndex.InBounds shape val

attribute [inline] FinTIndex.val

namespace FinTIndex

/-- Bounded hierarchical indices are equal when their underlying coordinates are equal. -/
theorem ext {p : HRank} {shape : Shape p} {idx idx' : FinTIndex shape}
    (h : idx.val = idx'.val) : idx = idx' := by
  cases idx
  cases idx'
  simp at h
  subst h
  rfl

instance {p : HRank} {shape : Shape p} : CoeOut (FinTIndex shape) (TIndex Nat p) where
  coe idx := idx.val

/-- Bounded indices of a leaf shape are ordinary finite indices. -/
@[inline, simps]
def leafEquiv (dim : Nat) : FinTIndex (.leaf dim) ≃ Fin dim where
  toFun idx := match idx with
    | ⟨HTuple.leaf i, h⟩ =>
        ⟨i, by
          simpa [TIndex.InBounds] using h⟩
  invFun i := ⟨HTuple.leaf i.1, by simp [TIndex.InBounds, i.2]⟩
  left_inv := by
    intro idx
    cases idx with
    | mk val h =>
      cases val with
      | leaf i =>
          apply FinTIndex.ext
          rfl
  right_inv := by intro i; rfl

/-- Bounded indices of a product shape are pairs of bounded indices. -/
@[inline, simps]
def prodEquiv {p q : HRank} (shape₀ : Shape p) (shape₁ : Shape q) :
    FinTIndex (HTuple.prod shape₀ shape₁) ≃ FinTIndex shape₀ × FinTIndex shape₁ where
  toFun idx :=
    match idx with
    | ⟨HTuple.prod idx₀ idx₁, h⟩ => (⟨idx₀, h.1⟩, ⟨idx₁, h.2⟩)
  invFun idx := ⟨HTuple.prod idx.1.val idx.2.val, ⟨idx.1.isLt, idx.2.isLt⟩⟩
  left_inv := by
    intro idx
    cases idx with
    | mk val h =>
    cases val with
    | prod idx₀ idx₁ => rfl
  right_inv := by
    intro idx
    cases idx with
    | mk left right => rfl

/-- Canonical dense row-major equivalence between bounded hierarchical indices and flat offsets. -/
@[inline] def equivFin : {p : HRank} → (shape : Shape p) → FinTIndex shape ≃ Fin shape.size
  | .leaf, .leaf dim => leafEquiv dim
  | .prod _ _, .prod shape₀ shape₁ =>
      let f := prodEquiv shape₀ shape₁
      let g := Equiv.prodCongr (equivFin shape₀) (equivFin shape₁)
      let h := finProdFinEquiv
      f.trans (g.trans h)

theorem offset_rowMajorEquiv_eq_equivFin {r} {shape : Shape r} (idx : FinTIndex shape) : --
    idx.val.offset (TIndex.rowMajorStride shape) = (equivFin shape idx) := by
  induction shape
  case leaf =>
    have ⟨.leaf idx, hidx⟩ := idx
    set_option backward.isDefEq.respectTransparency false in
    simp [TIndex.rowMajorStride, equivFin, leafEquiv]
  case prod shape₁ shape₂ h₁ h₂ =>
    have ⟨.prod idx₁ idx₂, hidx⟩ := idx
    set_option backward.isDefEq.respectTransparency false in
    simp [TIndex.rowMajorStride, equivFin, ← h₁, ← h₂, - nsmul_eq_mul, TIndex.offset_smul]
    rw[add_comm]


end FinTIndex

end TensorIndex

end NumLean
