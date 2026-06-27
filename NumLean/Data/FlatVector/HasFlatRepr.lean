import NumLean.Data.FlatVector.Basic

namespace NumLean

namespace FlatVector

variable {X : Type u} {I : Type v}
    {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX] [IndexType I nI]

instance : HasDefaultFlatRepr (FlatVector X I) Ks (nI * nX) where
  toVector x := VectorType.toVector x.data
  fromVector x := { data := VectorType.fromVector (As := Ks) x }
  left_inv := by intros _; simp
  right_inv := by intros _; simp
  getComp xs i h := VectorType.get xs.data i h
  getComp_spec := by intros; simp [← VectorType.get_spec]
  setComp xs i x h := { data := VectorType.set xs.data i x h }
  setComp_spec := by intros; simp [← VectorType.set_spec]
  get {n} xs i h :=
    let src := xs
    let srcMap : FinHTupleMap h(nI * nX) h(n) := sorry
    let dst : Ks 0 := VectorType.emptyWithCapacity (nI * nX)
    let dstMap : FinHTupleMap h(nI * nX) h(nI * nX) := .id h(nI * nX)
    -- let data := extractSlice (nI * nX) src srcMap dst dstMap (by grind)
    -- { data }
    sorry
  getComp_get_eq_vector_get := sorry
  set {n} xs i x h :=
    let src := x.data
    let srcMap : FinHTupleMap h(nI * nX) h(nI * nX) := .id h(nI * nX)
    let dst := xs
    let dstMap : FinHTupleMap h(nI * nX) h(n) := sorry
    -- let data := copySlice src srcMap dst dstMap sorry
    -- data
    sorry
  vector_get_set_eq := sorry
  vector_get_set_ne := sorry
  push := sorry
  vector_get_push_lt := sorry
  vector_get_push_eq := sorry
  toFlatVector := sorry
  get_toFlatVector_eq_getComp := sorry
  replicate := sorry
  get_replicate := sorry

end FlatVector

end NumLean
