import NumLean.Data.FlatVector.Basic

namespace NumLean

namespace FlatVector

-- open IndexType FinHTupleMap in
-- @[inline]
-- def swapSlice (xs : FlatVector X I) (len i j : Nat) : FlatVector X I := sorry
  --   (h : i + len < j ∨ j + len < i) : -- non-overlaping
  --   FlatVector X I :=
  -- if h : i = j then xs else
  --   let i := toFin i
  --   let j := toFin j
  --   let imap := (FinHTupleMap.point h(nI) i).pair (FinHTupleMap.id h(nX)) |>.linearize
  --   have hi : imap.Injective := by grind
  --   let jmap := (FinHTupleMap.point h(nI) j).pair (FinHTupleMap.id h(nX)) |>.linearize
  --   have hj : jmap.Injective := by grind
  --   have hij : i ≠ j := by sorry -- todo: set up IndexType with grind!
  --   have hdisjoint : Disjoint imap.range jmap.range := by grind
  --   { data := TensorArrayOps.swapSliceSelf xs.data imap jmap hi hj hdisjoint }

variable {X : Type u} {I : Type v}
    {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatVector X Ks nX] [IndexType I nI]

instance : FlatRepr (FlatVector X I) K (nI * nX) where
  toVector x := VectorType.toVector x.data
  fromVector x := { data := VectorType.fromVector (As := Ks) x }
  left_inv := by intros _; simp
  right_inv := by intros _; simp
  getComp xs i h := VectorType.get xs.data i h
  getComp_spec := by intros; simp [← VectorType.get_spec]
  setComp xs i x h := { data := VectorType.set xs.data i x h }
  setComp_spec := by intros; simp [← VectorType.set_spec]


instance [TensorArrayOps Ks K] : HasDefaultFlatVector (FlatVector X I) Ks (nI * nX) where
  get {n} xs i h :=
    let src := xs
    let srcMap : FinHTupleMap h(nI * nX) h(n) := sorry
    let dst : Ks 0 := VectorType.emptyWithCapacity (nI * nX)
    let dstMap : FinHTupleMap h(nI * nX) h(nI * nX) := .id h(nI * nX)
    let data := TensorArrayOps.extractSlice (nI * nX) src srcMap dst dstMap (by grind)
    { data }
  getComp_get_eq_vector_get := sorry
  set {n} xs i x h :=
    let src := x.data
    let srcMap : FinHTupleMap h(nI * nX) h(nI * nX) := .id h(nI * nX)
    let dst := xs
    let dstMap : FinHTupleMap h(nI * nX) h(n) := sorry
    let data := TensorArrayOps.copySlice src srcMap dst dstMap sorry
    data
  vector_get_set_eq := sorry
  vector_get_set_ne := sorry
  push := sorry
  vector_get_push_lt := sorry
  vector_get_push_eq := sorry
  toFlatVector := sorry
  get_toFlatVector_eq_getComp := sorry
  replicate := sorry
  get_replicate := sorry
