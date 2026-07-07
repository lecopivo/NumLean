module

public import NumLean.Data.Tensor.Basic
public import NumLean.Interfaces.TensorType

@[expose] public section

namespace NumLean

namespace Tensor

variable {X : Type u} {I : Type v}
    {Ks K nX nI} [HasDefaultFlatRepr X Ks] [VectorType Ks K] [HasFlatRepr X Ks nX] [IndexType I nI] [TensorType Ks]

instance : HasDefaultFlatRepr (Tensor X I) Ks where

open TensorType Tensor in
instance [Inhabited K] : HasFlatRepr (Tensor X I) Ks (nI * nX) where
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
    let srcMap := Layout.contiguous1D (len := nI * nX) (n := n) i h
    -- todo: ideally we can copy to uninitialized memory
    let dst : Ks (nI * nX) := VectorType.replicate (As:=Ks) (nI * nX) default
    let dstMap := Layout.id h(nI * nX)
    { data := copySlice K src srcMap dst dstMap (by grind) }
  getComp_get_eq_vector_get := by
    intro n xs off i hoff hi
    simp only
    rw [TensorType.get_copySlice]
    split
    · rename_i hmem
      have hinv := (Layout.id h(nI * nX)).eval_rangeNatInv i hmem
      simp only [FinHTupleMap.id_eval] at hinv
      simp [FinHTupleMap.eval_contiguous1D, hinv]
    · rename_i hmem
      exfalso
      exact hmem ⟨⟨h(i), hi⟩, by simp⟩
  set {n} xs off x h :=
    let src := x.data
    let srcMap := Layout.id h(nI * nX)
    let dst := xs
    let dstMap := Layout.contiguous1D (len := nI * nX) (n := n) off h
    copySlice K src srcMap dst dstMap (by grind)
  vector_get_set_eq := by
    intro n xs off i x hoff hi
    simp only
    rw [TensorType.get_copySlice]
    simp only [FinHTupleMap.id_eval]
    split
    · rename_i hmem
      have hinv := (Layout.contiguous1D (len := nI * nX) (n := n) off hoff).eval_rangeNatInv i hmem
      simp [FinHTupleMap.eval_contiguous1D] at hinv
      have hidx : ((Layout.contiguous1D (len := nI * nX) (n := n) off hoff).rangeNatInv i hmem).val.toScalar = i - off := by
        omega
      simp [hidx]
    · rename_i hmem
      exfalso
      exact hmem ⟨⟨h(i - off), by grind⟩, by simp [FinHTupleMap.eval_contiguous1D]; omega⟩
  vector_get_set_ne := by
    intro n xs off i x hoff hi hi'
    simp only
    rw [TensorType.get_copySlice]
    simp only [FinHTupleMap.id_eval]
    split
    · rename_i hmem
      have hinv := (Layout.contiguous1D (len := nI * nX) (n := n) off hoff).eval_rangeNatInv i hmem
      simp [FinHTupleMap.eval_contiguous1D] at hinv
      have hlt : ((Layout.contiguous1D (len := nI * nX) (n := n) off hoff).rangeNatInv i hmem).val.toScalar < nI * nX := by
        simpa using
          (Layout.contiguous1D (len := nI * nX) (n := n) off hoff).rangeNatInv_lt_src i hmem
      omega
    · rfl
  push xs x := VectorType.append xs x.data
  vector_get_push_lt := by
    intro n xs x i hi
    rw [VectorType.get_eq_getElem, VectorType.append_spec, VectorType.get_eq_getElem]
    exact Vector.getElem_append_left hi
  vector_get_push_eq := by
    intro n xs x i hi
    rw [VectorType.get_eq_getElem, VectorType.append_spec, VectorType.get_eq_getElem]
    simpa [Nat.add_sub_cancel_left] using
      Vector.getElem_append_right (xs := VectorType.toVector xs) (ys := VectorType.toVector x.data)
        (i := n + i) (by omega) (Nat.le_add_right n i)
  toTensor xs := xs.data
  get_toTensor_eq_getComp := by
    intros
    rfl
  replicate n x :=
    let src : Ks (nI * nX) := x.data
    let srcMap := Layout.id h(n, (nI * nX)) |>.snd
    -- todo: ideally we can copy to uninitialized memory
    let dst : Ks (n * (nI * nX)) := VectorType.replicate (As:=Ks) (n * (nI * nX)) default
    let dstMap := .rowMajor h(n, (nI * nX))
    copySlice K src srcMap dst dstMap (FinHTupleMap.injective_rowMajorMap h(n, (nI * nX)))
  get_replicate := by
    intro n x i j hi hj
    simp only
    rw [TensorType.get_copySlice]
    split
    · rename_i hmem
      have hidx : (h(i, j) : HTuple Nat (.prod .leaf .leaf)).rowMajorIndex h(n, (nI * nX)) =
          i * (nI * nX) + j := by
        simp
        rw [Nat.mul_comm (nI * nX) i, Nat.add_comm]
      have hinv : (Layout.rowMajor h(n, (nI * nX))).rangeNatInv (i * (nI * nX) + j) hmem =
          (⟨h(i, j), by get_elem_tactic⟩ : FinHTuple h(n, (nI * nX))) := by
        exact FinHTupleMap.rangeNatInv_rowMajorIndex_of_eq h(n, (nI * nX)) h(i, j)
          (by get_elem_tactic) hidx.symm hmem
      have hval := congrArg FinHTuple.val hinv
      simp at hval
      simp [hval]
    · rename_i hmem
      exfalso
      have hidx : (h(i, j) : HTuple Nat (.prod .leaf .leaf)).rowMajorIndex h(n, (nI * nX)) =
          i * (nI * nX) + j := by
        simp
        rw [Nat.mul_comm (nI * nX) i, Nat.add_comm]
      exact hmem (hidx ▸
        FinHTupleMap.mem_rangeNat_rowMajorIndex h(n, (nI * nX)) h(i, j) (by get_elem_tactic))


end Tensor

end NumLean
