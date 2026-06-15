import NumLean.Data.TensorIndex.AxisOrder
import NumLean.Data.TensorIndex.Layout
import NumLean.Data.HTuple.Algebra

open scoped BigOperators

namespace NumLean

namespace TensorIndex

namespace Shape

private def prodIndexEquiv (p q : HRank) : (HTuple.Index p ⊕ HTuple.Index q) ≃ HTuple.Index (.prod p q) where
  toFun
    | .inl i => .left i
    | .inr i => .right i
  invFun
    | .left i => .inl i
    | .right i => .inr i
  left_inv := by intro i; cases i <;> rfl
  right_inv := by intro i; cases i <;> rfl

theorem size_eq_prod_dim {p : HRank} (shape : Shape p) :
    shape.size = ∏ axis : HTuple.Index p, shape.dim axis := by
  induction shape with
  | leaf dim =>
      classical
      have huniv : (Finset.univ : Finset (HTuple.Index .leaf)) = {HTuple.Index.leaf} := by
        ext axis
        cases axis
        simp
      simp [Shape.size, Shape.dim, huniv]
  | prod shape₀ shape₁ h₀ h₁ =>
      rw [Shape.size_prod, h₀, h₁]
      calc
        (∏ axis, Shape.dim shape₀ axis) * ∏ axis, Shape.dim shape₁ axis
            = ∏ axis : HTuple.Index _ ⊕ HTuple.Index _,
                Sum.elim (Shape.dim shape₀) (Shape.dim shape₁) axis := by
              simp [Fintype.prod_sum_type]
        _ = ∏ axis : HTuple.Index (.prod _ _), Shape.dim (HTuple.prod shape₀ shape₁) axis := by
              exact Fintype.prod_equiv (prodIndexEquiv _ _)
                (fun axis => Sum.elim (Shape.dim shape₀) (Shape.dim shape₁) axis)
                (fun axis => Shape.dim (HTuple.prod shape₀ shape₁) axis)
                (by intro axis; cases axis <;> rfl)

/-- Dense stride for an explicit axis order.

The order is interpreted from least significant to most significant.  The stride of an axis is
the product of the dimensions of all less-significant axes, i.e. all axes appearing earlier in
the order. -/
def denseStrideForOrder {p : HRank} (shape : Shape p) (order : AxisOrder p) : Stride Nat shape :=
  HTuple.ofFn fun axis =>
    ∏ pos : Fin p.size, if pos < order.symm axis then shape.dim (order pos) else 1

/-- Integer-valued dense stride for an explicit axis order. -/
def denseIntStrideForOrder {p : HRank} (shape : Shape p) (order : AxisOrder p) : Stride Int shape :=
  HTuple.map Int.ofNat (shape.denseStrideForOrder order)

/-- Row-major dense stride for a hierarchical shape. -/
def rowMajorStride {p : HRank} (shape : Shape p) : Stride Nat shape :=
  shape.denseStrideForOrder (AxisOrder.rowMajor p)

/-- Internal recursive column-major/colexicographic dense stride used for proofs. -/
def colMajorStrideRec : {p : HRank} → (shape : Shape p) → Stride Nat shape
  | .leaf, .leaf _dim => .leaf 1
  | .prod _ _, .prod shape₀ shape₁ =>
      .prod (colMajorStrideRec shape₀) (Shape.size shape₀ • colMajorStrideRec shape₁)

/-- Column-major/colexicographic dense stride for a hierarchical shape. -/
def colMajorStride {p : HRank} (shape : Shape p) : Stride Nat shape :=
  shape.denseStrideForOrder (AxisOrder.colMajor p)

@[simp]
theorem get_denseStrideForOrder {p : HRank} (shape : Shape p) (order : AxisOrder p)
    (axis : HTuple.Index p) :
    (shape.denseStrideForOrder order).get axis =
      ∏ pos : Fin p.size, if pos < order.symm axis then shape.dim (order pos) else 1 := by
  simp [denseStrideForOrder]

/-- Row-major dense layout over integer offsets. -/
def rowMajorLayout {p : HRank} (shape : Shape p) : Layout shape Int where
  offset := 0
  stride := shape.denseIntStrideForOrder (AxisOrder.rowMajor p)

/-- Column-major dense layout over integer offsets. -/
def colMajorLayout {p : HRank} (shape : Shape p) : Layout shape Int where
  offset := 0
  stride := shape.denseIntStrideForOrder (AxisOrder.colMajor p)

/-- Dense layout over integer offsets for an explicit axis order. -/
def denseLayoutForOrder {p : HRank} (shape : Shape p) (order : AxisOrder p) : Layout shape Int where
  offset := 0
  stride := shape.denseIntStrideForOrder order

end Shape

namespace TIndex

theorem offset_eq_sum_get {p : HRank} (idx : TIndex Nat p) {shape : Shape p}
    (stride : Stride Nat shape) :
    idx.offset stride = ∑ axis : HTuple.Index p, idx.get axis * stride.get axis := by
  induction p with
  | leaf =>
      cases shape with
      | leaf _dim =>
      cases idx with
      | leaf i =>
      cases stride with
      | leaf s =>
      classical
      have huniv : (Finset.univ : Finset (HTuple.Index .leaf)) = {HTuple.Index.leaf} := by
        ext axis
        cases axis
        simp
      simp [TIndex.offset, HTuple.inner, HTuple.innerWith, huniv]
  | prod p q hp hq =>
      cases shape with
      | prod shape₀ shape₁ =>
      cases idx with
      | prod idx₀ idx₁ =>
      cases stride with
      | prod stride₀ stride₁ =>
      change TIndex.offset idx₀ (shape := shape₀) stride₀ +
          TIndex.offset idx₁ (shape := shape₁) stride₁ =
        ∑ axis : HTuple.Index (.prod p q), (HTuple.prod idx₀ idx₁).get axis * (HTuple.prod stride₀ stride₁).get axis
      rw [hp idx₀ (shape := shape₀) stride₀, hq idx₁ (shape := shape₁) stride₁]
      calc
        (∑ axis, idx₀.get axis * stride₀.get axis) + ∑ axis, idx₁.get axis * stride₁.get axis
            = ∑ axis : HTuple.Index _ ⊕ HTuple.Index _,
                Sum.elim (fun axis => idx₀.get axis * stride₀.get axis)
                  (fun axis => idx₁.get axis * stride₁.get axis) axis := by
              simp [Fintype.sum_sum_type]
        _ = ∑ axis : HTuple.Index (.prod p q),
              (HTuple.prod idx₀ idx₁).get axis * (HTuple.prod stride₀ stride₁).get axis := by
              exact Fintype.sum_equiv (Shape.prodIndexEquiv _ _)
                (fun axis => Sum.elim (fun axis => idx₀.get axis * stride₀.get axis)
                  (fun axis => idx₁.get axis * stride₁.get axis) axis)
                (fun axis => (HTuple.prod idx₀ idx₁).get axis * (HTuple.prod stride₀ stride₁).get axis)
                (by intro axis; cases axis <;> rfl)

/-- Scaling a stride scales the resulting natural offset. -/
theorem offset_smul_nat {p : HRank} (idx : TIndex Nat p) {shape : Shape p}
    (stride : Stride Nat shape) (k : Nat) :
    idx.offset (k • stride) = k * idx.offset stride := by
  induction p with
  | leaf =>
      cases shape with
      | leaf _dim =>
      cases idx with
      | leaf i =>
      cases stride with
      | leaf s =>
      simp [TIndex.offset, HTuple.inner, HTuple.innerWith]
      ring
  | prod p q hp hq =>
      cases shape with
      | prod shape₀ shape₁ =>
      cases idx with
      | prod idx₀ idx₁ =>
      cases stride with
      | prod stride₀ stride₁ =>
      have hleft : HTuple.innerWith (fun n d => n * d) idx₀ (k • stride₀) =
          k * HTuple.innerWith (fun n d => n * d) idx₀ stride₀ := by
        simpa [TIndex.offset, HTuple.inner] using hp idx₀ (shape := shape₀) stride₀
      have hright : HTuple.innerWith (fun n d => n * d) idx₁ (k • stride₁) =
          k * HTuple.innerWith (fun n d => n * d) idx₁ stride₁ := by
        simpa [TIndex.offset, HTuple.inner] using hq idx₁ (shape := shape₁) stride₁
      change HTuple.innerWith (fun n d => n * d) idx₀ (k • stride₀) +
          HTuple.innerWith (fun n d => n * d) idx₁ (k • stride₁) =
        k * (HTuple.innerWith (fun n d => n * d) idx₀ stride₀ +
          HTuple.innerWith (fun n d => n * d) idx₁ stride₁)
      rw [hleft, hright]
      ring_nf

/-- Offset computed with the dense stride for a chosen axis order. -/
def offsetForOrder {p : HRank} (idx : TIndex Nat p) (shape : Shape p) (order : AxisOrder p) : Nat :=
  idx.offset (shape.denseStrideForOrder order)

private theorem offset_map_natCast {p : HRank} (idx : TIndex Nat p) {shape : Shape p}
    (stride : Stride Nat shape) :
    idx.offset (shape := shape) (HTuple.map Int.ofNat stride) =
      Int.ofNat (idx.offset (shape := shape) stride) := by
  induction p with
  | leaf =>
      cases idx with
      | leaf i =>
      cases shape with
      | leaf _dim =>
      cases stride with
      | leaf s =>
      simp [TIndex.offset, HTuple.inner, HTuple.innerWith]
  | prod p q hp hq =>
      cases idx with
      | prod idx₀ idx₁ =>
      cases shape with
      | prod shape₀ shape₁ =>
      cases stride with
      | prod stride₀ stride₁ =>
      change TIndex.offset idx₀ (shape := shape₀) (HTuple.map Int.ofNat stride₀) +
          TIndex.offset idx₁ (shape := shape₁) (HTuple.map Int.ofNat stride₁) =
        Int.ofNat (TIndex.offset idx₀ (shape := shape₀) stride₀ +
          TIndex.offset idx₁ (shape := shape₁) stride₁)
      rw [hp idx₀ (shape := shape₀) stride₀, hq idx₁ (shape := shape₁) stride₁]
      norm_num

/-- Row-major dense offset. -/
def rowMajorOffset {p : HRank} (idx : TIndex Nat p) (shape : Shape p) : Nat :=
  idx.offsetForOrder shape (AxisOrder.rowMajor p)

/-- Column-major dense offset. -/
def colMajorOffset {p : HRank} (idx : TIndex Nat p) (shape : Shape p) : Nat :=
  idx.offset shape.colMajorStride

end TIndex

namespace FinTIndex

/-- Offset computed with the dense stride for a chosen axis order. -/
def offsetForOrder {p : HRank} {shape : Shape p} (idx : FinTIndex shape)
    (order : AxisOrder p) : Nat :=
  (idx : TIndex Nat p).offsetForOrder shape order

/-- Row-major dense offset. -/
def rowMajorOffset {p : HRank} {shape : Shape p} (idx : FinTIndex shape) : Nat :=
  idx.offsetForOrder (AxisOrder.rowMajor p)

/-- Column-major dense offset. -/
def colMajorOffset {p : HRank} {shape : Shape p} (idx : FinTIndex shape) : Nat :=
  (idx : TIndex Nat p).colMajorOffset shape

end FinTIndex

private def flatNumel {rank : Nat} (dims : Vector Nat rank) : Nat :=
  ∏ i : Fin rank, dims[i]

private def denseOffset {rank : Nat} (dims idx : Vector Nat rank) : Nat :=
  ∑ i : Fin rank, idx[i] * (∏ j : Fin rank, if j < i then dims[j] else 1)

private theorem denseOffset_decomp {n : Nat} (dims idx : Vector Nat (n + 1)) :
    denseOffset dims idx = idx[0] + dims[0] *
      denseOffset (Vector.ofFn fun j : Fin n => dims[j.succ])
        (Vector.ofFn fun j : Fin n => idx[j.succ]) := by
  unfold denseOffset
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.getElem_fin, Fin.val_succ, Vector.getElem_ofFn]
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero]
    rw [show (if 0 < i.succ then dims[0] else 1) = dims[0] by simp]
    have hprod : (∏ j : Fin n, if j.succ < i.succ then dims[↑j.succ] else 1) =
        ∏ j : Fin n, if j < i then dims[↑j + 1] else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases h : j < i
      · simp [h, Fin.succ_lt_succ_iff]
      · simp [h, Fin.succ_lt_succ_iff]
    conv_lhs =>
      arg 2
      arg 2
      change (∏ j : Fin n, if j.succ < i.succ then dims[j.succ] else 1)
      rw [hprod]
    ring

private theorem flatNumel_decomp {n : Nat} (dims : Vector Nat (n + 1)) :
    flatNumel dims = dims[0] * flatNumel (Vector.ofFn fun j : Fin n => dims[j.succ]) := by
  unfold flatNumel
  rw [Fin.prod_univ_succ]
  simp

private def VectorInBounds {rank : Nat} (idx dims : Vector Nat rank) : Prop :=
  ∀ i : Fin rank, idx[i] < dims[i]

private theorem vectorInBounds_tail {n : Nat} {dims idx : Vector Nat (n + 1)}
    (h : VectorInBounds idx dims) :
    VectorInBounds (Vector.ofFn fun j : Fin n => idx[j.succ])
      (Vector.ofFn fun j : Fin n => dims[j.succ]) := by
  intro j
  simpa using h j.succ

private theorem flatNumel_pos_of_inBounds {rank : Nat} {dims idx : Vector Nat rank}
    (h : VectorInBounds idx dims) : 0 < flatNumel dims := by
  induction rank with
  | zero => simp [flatNumel]
  | succ n ih =>
      rw [flatNumel_decomp]
      exact Nat.mul_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) (h 0))
        (ih (vectorInBounds_tail h))

private theorem denseOffset_lt_flatNumel {rank : Nat} {dims idx : Vector Nat rank}
    (h : VectorInBounds idx dims) : denseOffset dims idx < flatNumel dims := by
  induction rank with
  | zero => simp [denseOffset, flatNumel]
  | succ n ih =>
      rw [denseOffset_decomp, flatNumel_decomp]
      let tdims := Vector.ofFn fun j : Fin n => dims[j.succ]
      let tidx := Vector.ofFn fun j : Fin n => idx[j.succ]
      have ht : denseOffset tdims tidx < flatNumel tdims := ih (vectorInBounds_tail h)
      have h0 := h 0
      calc
        idx[0] + dims[0] * denseOffset tdims tidx
            < dims[0] + dims[0] * denseOffset tdims tidx :=
              Nat.add_lt_add_right h0 _
        _ = dims[0] * (denseOffset tdims tidx + 1) := by
              rw [Nat.mul_succ, Nat.add_comm]
        _ ≤ dims[0] * flatNumel tdims :=
              Nat.mul_le_mul_left _ (Nat.succ_le_of_lt ht)

private theorem denseOffset_inj {rank : Nat} {dims idx idx' : Vector Nat rank}
    (h : VectorInBounds idx dims) (h' : VectorInBounds idx' dims)
    (hoff : denseOffset dims idx = denseOffset dims idx') : idx = idx' := by
  induction rank with
  | zero =>
      apply Vector.ext
      intro i hi
      omega
  | succ n ih =>
      let tdims := Vector.ofFn fun j : Fin n => dims[j.succ]
      let tidx := Vector.ofFn fun j : Fin n => idx[j.succ]
      let tidx' := Vector.ofFn fun j : Fin n => idx'[j.succ]
      have hdecomp := denseOffset_decomp dims idx
      have hdecomp' := denseOffset_decomp dims idx'
      have ht : denseOffset tdims tidx < flatNumel tdims := denseOffset_lt_flatNumel (vectorInBounds_tail h)
      have ht' : denseOffset tdims tidx' < flatNumel tdims := denseOffset_lt_flatNumel (vectorInBounds_tail h')
      have hpos : 0 < flatNumel tdims := flatNumel_pos_of_inBounds (vectorInBounds_tail h)
      have heq : idx[0] + dims[0] * denseOffset tdims tidx =
          idx'[0] + dims[0] * denseOffset tdims tidx' := by
        rw [← hdecomp, ← hdecomp']
        exact hoff
      have hmod := congrArg (fun x => x % dims[0]) heq
      have h0pos : 0 < dims[0] := Nat.lt_of_le_of_lt (Nat.zero_le _) (h 0)
      have hhead : idx[0] = idx'[0] := by
        have lhs : (idx[0] + dims[0] * denseOffset tdims tidx) % dims[0] = idx[0] := by
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt (h 0)
        have rhs : (idx'[0] + dims[0] * denseOffset tdims tidx') % dims[0] = idx'[0] := by
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt (h' 0)
        simpa [lhs, rhs] using hmod
      have htailEq : denseOffset tdims tidx = denseOffset tdims tidx' := by
        rw [hhead] at heq
        exact Nat.eq_of_mul_eq_mul_left h0pos (Nat.add_left_cancel heq)
      have htailVec := ih (vectorInBounds_tail h) (vectorInBounds_tail h') htailEq
      apply Vector.ext
      intro k hk
      cases k with
      | zero => simpa using hhead
      | succ k =>
          have := congrArg (fun v : Vector Nat n => v[k]) htailVec
          simpa [tidx, tidx'] using this

private def orderedDims {p : HRank} (shape : Shape p) (order : AxisOrder p) : Vector Nat p.size :=
  Vector.ofFn fun i => shape.dim (order i)

private def orderedIndex {p : HRank} (idx : TIndex Nat p) (order : AxisOrder p) : Vector Nat p.size :=
  Vector.ofFn fun i => idx.get (order i)

private theorem flatNumel_orderedDims {p : HRank} (shape : Shape p) (order : AxisOrder p) :
    flatNumel (orderedDims shape order) = shape.size := by
  rw [Shape.size_eq_prod_dim]
  simpa [flatNumel, orderedDims] using
    (Equiv.prod_comp order (fun axis : HTuple.Index p => shape.dim axis))

private theorem orderedIndex_inBounds {p : HRank} {shape : Shape p} (idx : FinTIndex shape)
    (order : AxisOrder p) :
    VectorInBounds (orderedIndex idx.val order) (orderedDims shape order) := by
  intro i
  simpa [orderedIndex, orderedDims] using TIndex.inBounds_get idx.isLt (order i)

private theorem offset_denseStrideForOrder_eq_denseOffset {p : HRank} (shape : Shape p)
    (idx : TIndex Nat p) (order : AxisOrder p) :
    idx.offset (shape.denseStrideForOrder order) =
      denseOffset (orderedDims shape order) (orderedIndex idx order) := by
  calc
    idx.offset (shape.denseStrideForOrder order)
        = ∑ axis : HTuple.Index p, idx.get axis * (shape.denseStrideForOrder order).get axis :=
          TIndex.offset_eq_sum_get idx (shape.denseStrideForOrder order)
    _ = ∑ i : Fin p.size, idx.get (order i) * (shape.denseStrideForOrder order).get (order i) := by
          simpa using (Equiv.sum_comp order
            (fun axis : HTuple.Index p => idx.get axis * (shape.denseStrideForOrder order).get axis)).symm
    _ = denseOffset (orderedDims shape order) (orderedIndex idx order) := by
          unfold denseOffset orderedDims orderedIndex
          apply Finset.sum_congr rfl
          intro i _
          simp [Shape.denseStrideForOrder]

private theorem offset_denseStrideForOrder_lt_size {p : HRank} {shape : Shape p}
    (idx : FinTIndex shape) (order : AxisOrder p) :
    (idx : TIndex Nat p).offset (shape.denseStrideForOrder order) < shape.size := by
  rw [offset_denseStrideForOrder_eq_denseOffset]
  rw [← flatNumel_orderedDims shape order]
  exact denseOffset_lt_flatNumel (orderedIndex_inBounds idx order)

private theorem offset_denseStrideForOrder_injective {p : HRank} {shape : Shape p}
    (order : AxisOrder p) :
    Function.Injective fun idx : FinTIndex shape =>
      (idx : TIndex Nat p).offset (shape.denseStrideForOrder order) := by
  intro idx idx' hoff
  apply FinTIndex.ext
  apply HTuple.ext
  intro axis
  let i := order.symm axis
  have hordered := denseOffset_inj (orderedIndex_inBounds idx order)
    (orderedIndex_inBounds idx' order) (by
      rw [← offset_denseStrideForOrder_eq_denseOffset shape idx.val order]
      rw [← offset_denseStrideForOrder_eq_denseOffset shape idx'.val order]
      exact hoff)
  have hget := congrArg (fun v : Vector Nat p.size => v[i]) hordered
  simpa [orderedIndex, i] using hget

namespace Shape

/-- Decode a column-major/colexicographic flat index into a bounded hierarchical index. -/
def colMajorIndexOfFin : {p : HRank} → (shape : Shape p) → Fin shape.size → FinTIndex shape
  | .leaf, .leaf dim, flat =>
      { val := .leaf flat.1
        isLt := flat.2 }
  | .prod _ _, .prod shape₀ shape₁, flat =>
      let leftSize := Shape.size shape₀
      if hleft : 0 < leftSize then
        let leftFlat : Fin (Shape.size shape₀) :=
          ⟨flat.1 % leftSize, Nat.mod_lt _ hleft⟩
        let rightFlat : Fin (Shape.size shape₁) :=
          ⟨flat.1 / leftSize, by
            rw [Nat.div_lt_iff_lt_mul hleft]
            rw [Nat.mul_comm]
            exact flat.2⟩
        let leftIdx := colMajorIndexOfFin shape₀ leftFlat
        let rightIdx := colMajorIndexOfFin shape₁ rightFlat
        { val := .prod leftIdx.val rightIdx.val
          isLt := ⟨leftIdx.isLt, rightIdx.isLt⟩ }
      else
        False.elim <| by
          have hzero : leftSize = 0 := Nat.eq_zero_of_not_pos hleft
          have hflat : flat.1 < 0 := by simpa [Shape.size, leftSize, hzero] using flat.2
          exact Nat.not_lt_zero _ hflat

end Shape

namespace FinTIndex

/-- Encode a bounded hierarchical index as a column-major/colexicographic flat index. -/
def toColMajorFin : {p : HRank} → {shape : Shape p} → FinTIndex shape → Fin shape.size
  | .leaf, .leaf _dim, ⟨.leaf i, h⟩ => ⟨i, h⟩
  | .prod _ _, .prod shape₀ shape₁, ⟨.prod idx₀ idx₁, h⟩ =>
      let leftFlat := toColMajorFin (shape := shape₀) ⟨idx₀, h.1⟩
      let rightFlat := toColMajorFin (shape := shape₁) ⟨idx₁, h.2⟩
      ⟨leftFlat.1 + Shape.size shape₀ * rightFlat.1, by
        have hleft : leftFlat.1 < Shape.size shape₀ := leftFlat.2
        have hright : rightFlat.1 < Shape.size shape₁ := rightFlat.2
        calc
          leftFlat.1 + Shape.size shape₀ * rightFlat.1
              < Shape.size shape₀ + Shape.size shape₀ * rightFlat.1 :=
                Nat.add_lt_add_right hleft _
          _ = Shape.size shape₀ * (rightFlat.1 + 1) := by
                rw [Nat.mul_succ, Nat.add_comm]
          _ ≤ Shape.size shape₀ * Shape.size shape₁ :=
                Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hright)⟩

end FinTIndex

namespace Shape

/-- Dense layouts for any axis order are compact. -/
theorem denseLayoutForOrder_compact {p : HRank} (shape : Shape p) (order : AxisOrder p) :
    Layout.Compact (shape.denseLayoutForOrder order) := by
  let layout := shape.denseLayoutForOrder order
  have bounded : layout.BoundedBy 0 shape.size := by
    intro idx
    have hoff := TIndex.offset_map_natCast (idx : TIndex Nat p) (shape.denseStrideForOrder order)
    have hlt := offset_denseStrideForOrder_lt_size idx order
    constructor
    · have hnonneg : (0 : Int) ≤ Int.ofNat ((idx : TIndex Nat p).offset (shape.denseStrideForOrder order)) := by
        exact Int.natCast_nonneg _
      simpa [layout, denseLayoutForOrder, denseIntStrideForOrder, Layout.eval, hoff] using hnonneg
    · have hltInt : (((idx : TIndex Nat p).offset (shape.denseStrideForOrder order) : Nat) : Int) <
          (shape.size : Int) := by
        exact_mod_cast hlt
      simpa [layout, denseLayoutForOrder, denseIntStrideForOrder, Layout.eval, hoff] using hltInt
  refine ⟨bounded, ?_⟩
  let f : FinTIndex shape → Fin shape.size := fun idx =>
    (⟨(layout.eval idx.1).toNat, by
      have := bounded idx
      simp_all only [Int.toNat_lt]⟩ : Fin shape.size)
  have hcard : Fintype.card (FinTIndex shape) = Fintype.card (Fin shape.size) := by
    simpa using FinTIndex.card_eq_shape_size shape
  have hinj : Function.Injective f := by
    intro idx idx' h
    apply offset_denseStrideForOrder_injective order
    have hval := congrArg Fin.val h
    have hoff := TIndex.offset_map_natCast (idx : TIndex Nat p) (shape.denseStrideForOrder order)
    have hoff' := TIndex.offset_map_natCast (idx' : TIndex Nat p) (shape.denseStrideForOrder order)
    simp [f, layout, denseLayoutForOrder, denseIntStrideForOrder, Layout.eval, hoff, hoff'] at hval
    exact hval
  exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩

/-- The column-major dense layout is compact. -/
theorem colMajorLayout_compact {p : HRank} (shape : Shape p) :
    Layout.Compact shape.colMajorLayout := by
  simpa [colMajorLayout, denseLayoutForOrder, denseIntStrideForOrder, colMajorStride] using
    denseLayoutForOrder_compact shape (AxisOrder.colMajor p)

/-- The row-major dense layout is compact. -/
theorem rowMajorLayout_compact {p : HRank} (shape : Shape p) :
    Layout.Compact shape.rowMajorLayout := by
  simpa [rowMajorLayout, denseLayoutForOrder, denseIntStrideForOrder, rowMajorStride] using
    denseLayoutForOrder_compact shape (AxisOrder.rowMajor p)

@[simp]
theorem leafLayout_eval (n i : Nat) :
    (Layout.eval ({ offset := 0, stride := HTuple.leaf (1 : Int) } : Layout (HTuple.leaf n) Int)
      (HTuple.leaf i)) = i := by
  simp [Layout.eval, TIndex.offset, HTuple.inner, HTuple.innerWith]

end Shape

end TensorIndex

end NumLean
