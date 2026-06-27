import NumLean.Data.FlatVector.Basic
import NumLean.Interfaces.TensorType

namespace NumLean

namespace FlatVector

variable {X : Type u} {I : Type v}
    {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX] [IndexType I nI] [TensorType Ks]

open TensorType Tensor in
instance [Inhabited K] : HasDefaultFlatRepr (FlatVector X I) Ks (nI * nX) where
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
    let srcMap : Layout h(nI * nX) h(n) := {
      offset := i
      stride := h(h(1))
      inBounds := sorry
    }
    -- todo: ideally we can copy to uninitialized memory
    let dst : Ks (nI * nX) := VectorType.replicate (As:=Ks) (nI * nX) default
    let dstMap := Layout.id h(nI * nX)
    { data := copySlice K src srcMap dst dstMap (by grind) }
  getComp_get_eq_vector_get := sorry
  set {n} xs i x h :=
    let src := x.data
    let srcMap := Layout.id h(nI * nX)
    let dst := xs
    let dstMap : Layout h(nI * nX) h(n) := {
      offset := i
      stride := h(h(1))
      inBounds := sorry
    }
    copySlice K src srcMap dst dstMap sorry
  vector_get_set_eq := sorry
  vector_get_set_ne := sorry
  push xs x := VectorType.append xs x.data
  vector_get_push_lt := sorry
  vector_get_push_eq := sorry
  toFlatVector xs := xs.data
  get_toFlatVector_eq_getComp := sorry
  replicate n x :=
    let src : Ks (nI * nX) := x.data
    let srcMap := Layout.id h(n, (nI * nX)) |>.snd
    -- todo: ideally we can copy to uninitialized memory
    let dst : Ks (n * (nI * nX)) := VectorType.replicate (As:=Ks) (n * (nI * nX)) default
    let dstMap := .rowMajor h(n, (nI * nX))
    copySlice K src srcMap dst dstMap (by sorry)
  get_replicate := sorry


end FlatVector

end NumLean
