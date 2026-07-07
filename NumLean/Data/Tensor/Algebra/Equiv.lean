module

public import NumLean.Data.Tensor.Algebra.Lawful
public import NumLean.Data.Tensor.Algebra.VMul

@[expose] public section

namespace NumLean.Tensor

private theorem mem_rangeNat_cast_id_leaf (n : Nat) (i : Fin n) :
    (i : Nat) ∈ ((Layout.id h(n)).cast h(n) h(n * 1)).rangeNat := by
  refine ⟨⟨h(i.1), by exact i.2⟩, ?_⟩
  simp [Layout.id, FinHTupleMap.cast, FinHTupleMap.id, HTuple.toScalar]

private theorem rangeNatInv_cast_id_leaf (n : Nat) (i : Fin n)
    (hmem : (i : Nat) ∈ ((Layout.id h(n)).cast h(n) h(n * 1)).rangeNat) :
    ((Layout.id h(n)).cast h(n) h(n * 1)).rangeNatInv (i : Nat) hmem =
      (⟨h(i.1), by exact i.2⟩ : FinHTuple h(n)) := by
  apply FinHTuple.ext
  apply HTuple.toScalar_injective
  have heval := ((Layout.id h(n)).cast h(n) h(n * 1)).eval_rangeNatInv (i : Nat) hmem
  simpa [Layout.id, FinHTupleMap.cast, FinHTupleMap.id, HTuple.toScalar] using heval

private abbrev rowMajorCast2D (m n : Nat) : Layout h(m, n) h(m * n * 1) :=
  FinHTupleMap.cast (Layout.rowMajor h(m, n)) h(m, n) h(m * n * 1) (by simp) (by simp)

private theorem rowMajorCast2D_mem_toFin {I J m n} [IndexType I m] [IndexType J n]
    (i : Fin m) (j : Fin n) :
    (IndexType.toFin (I := I × J) (fromFin (I := I) i, fromFin (I := J) j)).1 * 1 ∈
      (rowMajorCast2D m n).rangeNat := by
  have hidx : (IndexType.toFin (I := I × J) (fromFin (I := I) i, fromFin (I := J) j)).1 =
      (h(i.1, j.1) : HTuple Nat (.prod .leaf .leaf)).rowMajorIndex h(m, n) := by
    simp [toFin, IndexType.toFin_fromFin, finProdFinEquiv_apply_val]
  have hmem : (h(i.1, j.1) : HTuple Nat (.prod .leaf .leaf)).rowMajorIndex h(m, n) ∈
      (rowMajorCast2D m n).rangeNat := ⟨⟨h(i.1, j.1), by simp [i.2, j.2]⟩, by
    simp [rowMajorCast2D, Layout.rowMajor, FinHTupleMap.cast, FinHTupleMap.rowMajorMap,
      HTupleMap.eval_rowMajorMap]⟩
  simpa [Nat.mul_one, hidx] using hmem

private theorem rowMajorCast2D_rangeNatInv_toFin {I J m n} [IndexType I m] [IndexType J n]
    (i : Fin m) (j : Fin n)
    (hmem : (IndexType.toFin (I := I × J) (fromFin (I := I) i, fromFin (I := J) j)).1 ∈
      (rowMajorCast2D m n).rangeNat) :
    (rowMajorCast2D m n).rangeNatInv
        ((IndexType.toFin (I := I × J) (fromFin (I := I) i, fromFin (I := J) j)).1) hmem =
      (⟨h(i.1, j.1), by simp [i.2, j.2]⟩ : FinHTuple h(m, n)) := by
  have hdst : (rowMajorCast2D m n).Injective := by
    intro a b hab
    apply FinHTupleMap.injective_rowMajorMap h(m, n)
    apply FinHTuple.ext
    have hval := congrArg FinHTuple.val hab
    simpa [rowMajorCast2D, FinHTupleMap.cast, FinHTupleMap.evalFin] using hval
  apply hdst
  apply FinHTuple.ext
  apply HTuple.toScalar_injective
  have hidx : (IndexType.toFin (I := I × J) (fromFin (I := I) i, fromFin (I := J) j)).1 =
      (h(i.1, j.1) : HTuple Nat (.prod .leaf .leaf)).rowMajorIndex h(m, n) := by
    simp [toFin, IndexType.toFin_fromFin, finProdFinEquiv_apply_val]
  have hlhs := (rowMajorCast2D m n).eval_rangeNatInv
    ((IndexType.toFin (I := I × J) (fromFin (I := I) i, fromFin (I := J) j)).1) hmem
  have hrhs : (((rowMajorCast2D m n) (h(i.1, j.1)) : HTuple Nat .leaf).toScalar) =
      ↑(IndexType.toFin (I := I × J) (fromFin (I := I) i, fromFin (I := J) j)) := by
    rw [hidx]
    simp [rowMajorCast2D, Layout.rowMajor, FinHTupleMap.cast, FinHTupleMap.rowMajorMap]
  simpa [FinHTupleMap.evalFin] using hlhs.trans hrhs.symm

private theorem rowMajorCast2D_left_offset {I J m n} [IndexType I m] [IndexType J n]
    (i : Fin m) (j : Fin n) :
    (((rowMajorCast2D m n)
        (h(i.1).prod (fromFin (I := FinHTuple h(n)) j).val) : HTuple Nat .leaf).toScalar) =
      offset (nX := 1) (fromFin (I := I) i, fromFin (I := J) j) := by
  have hjidx : (fromFin (I := FinHTuple h(n)) j).val.rowMajorIndex h(n) = j.1 := by
    have hfin := FinHTuple.equivFin_val_eq_linearIndex_zero h(n)
      ((FinHTuple.equivFin h(n)).symm j)
    simpa [fromFin, HTuple.Range.linearIndex_zero] using hfin.symm
  rw [FinHTupleMap.eval_cast, FinHTupleMap.eval_rowMajorMap]
  change (h(i.1).prod (fromFin (I := FinHTuple h(n)) j).val).rowMajorIndex h(m, n) =
    offset (nX := 1) (fromFin (I := I) i, fromFin (I := J) j)
  simp [offset, toFin, IndexType.toFin_fromFin, finProdFinEquiv_apply_val,
    HTuple.rowMajorIndex]
  exact hjidx

private theorem rowMajorCast2D_right_offset {I J m n} [IndexType I m] [IndexType J n]
    (i : Fin m) (j : Fin n) :
    (((rowMajorCast2D m n)
        ((fromFin (I := FinHTuple h(m)) i).val.prod h(j.1)) : HTuple Nat .leaf).toScalar) =
      offset (nX := 1) (fromFin (I := I) i, fromFin (I := J) j) := by
  have hiidx : (fromFin (I := FinHTuple h(m)) i).val.rowMajorIndex h(m) = i.1 := by
    have hfin := FinHTuple.equivFin_val_eq_linearIndex_zero h(m)
      ((FinHTuple.equivFin h(m)).symm i)
    simpa [fromFin, HTuple.Range.linearIndex_zero] using hfin.symm
  rw [FinHTupleMap.eval_cast, FinHTupleMap.eval_rowMajorMap]
  change ((fromFin (I := FinHTuple h(m)) i).val.prod h(j.1)).rowMajorIndex h(m, n) =
    offset (nX := 1) (fromFin (I := I) i, fromFin (I := J) j)
  simp [offset, toFin, IndexType.toFin_fromFin, finProdFinEquiv_apply_val,
    HTuple.rowMajorIndex]
  exact Or.inl hiidx


section FinvecEquiv

variable
    {K Ks} [VectorType Ks K]
    [CommRing K] [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
    [AddCommGroup X] [Module K X] [HasDefaultFlatRepr X Ks] [HasFlatRepr X Ks nX]
    [HasFlatRepr.LawfulAddGroupOps (nX := nX) X Ks]

    {I nI} [IndexType I nI]
    {J nJ} [IndexType J nJ]

def finvecEquiv : Tensor X I ≃ₗ[K] (Fin nI → X) where
  toFun x := (fun i => x[fromFin (I:=I) i])
  invFun x :=
    have : Inhabited X := ⟨0⟩
    .ofFn (fun i => x (toFin i))
  left_inv := by intros x; ext i; simp
  right_inv := by intros x; ext i; simp
  map_add' := by intro x y; funext i; simp
  map_smul' := by intro s x; funext i; simp

@[simp]
theorem finvecEquiv_zero :
    finvecEquiv (K := K) (I := I) (X := X) (0 : Tensor X I) = 0 := by
  ext i
  simp [finvecEquiv]

@[simp]
theorem finvecEquiv_add (x y : Tensor X I) :
    finvecEquiv (x + y) = finvecEquiv x + finvecEquiv y := by ext i; simp

@[simp]
theorem finvecEquiv_neg (x : Tensor X I) :
    finvecEquiv (-x) = -finvecEquiv x := by
  ext i
  simp [finvecEquiv]

@[simp]
theorem finvecEquiv_sub (x y : Tensor X I) :
    finvecEquiv (x - y) = finvecEquiv x - finvecEquiv y := by
  ext i
  simp [finvecEquiv]

@[simp]
theorem finvecEquiv_smul (k : K) (x : Tensor X I) :
    finvecEquiv (k • x) = k • finvecEquiv x := by
  ext i
  simp [finvecEquiv]

end FinvecEquiv


section MatrixEquiv

variable
    {R : Type} {Rs : Nat → Type} [HasDefaultFlatRepr R Rs] [VectorType Rs R]
    [CommRing R] [TensorRingOps Rs R] [LawfulTensorRingOps Rs R]

    {I nI} [IndexType I nI]
    {J nJ} [IndexType J nJ]
    {K nK} [IndexType K nK]

open Classical in
theorem getElem_matVecMul_fin (A : Tensor R (I × J)) (x : Tensor R J) (i : Fin nI) :
    (A *ᵥ x)[fromFin (I:=I) i] =
      ∑ j : Fin nJ, A[fromFin (I:=I) i, fromFin (I:=J) j] * x[fromFin (I:=J) j] := by
  simp [VMul.vmul, matVecMul, HasFlatRepr.get]
  have h : i.1 ∈ (FinHTupleMap.cast (Layout.id (h(nI))) (h(nI)) (h(nI * 1)) (by simp) (by simp)).rangeNat := by
    exact mem_rangeNat_cast_id_leaf nI i
  rw [dif_pos h]
  have h' : (FinHTupleMap.cast (Layout.id (h(nI))) (h(nI)) (h(nI * 1)) (by simp) (by simp)).rangeNatInv i.1 h
            =
            ⟨i.1, by get_elem_tactic⟩ := by
    exact rangeNatInv_cast_id_leaf nI i h
  simp [h']
  change (∑ x_1 ∈ (entries ((0 : HTuple Nat .leaf)...h(nJ))).toFinset, _) = _
  rw [FinHTuple.sum_zeroRange_eq_fin]
  apply Finset.sum_congr rfl
  intro j _
  simp [HTuple.numel_leaf, getElem, get, HasFlatRepr.get,
        offset, mul_one, IndexType.toFin_fromFin, Layout.rowMajor, FinHTupleMap.rowMajorMap,
        HTuple.numel_prod, FinHTupleMap.eval_mk, HTupleMap.eval_rowMajorMap,
        HTuple.rowMajorIndex, HTuple.leaf_toScalar, toFin, finProdFinEquiv_apply_val,
        FinHTuple.equivFin, FinHTuple.leafEquiv]
  rfl


theorem getElem_vecMatMul_fin (x : Tensor R I) (A : Tensor R (I × J)) (j : Fin nJ) :
    (x *ᵥ A)[fromFin (I:=J) j] =
      ∑ i : Fin nI, x[fromFin (I:=I) i] * A[fromFin (I:=I) i, fromFin (I:=J) j] := by
  classical
  simp [VMul.vmul, vecMatMul, HasFlatRepr.get]
  have h : j.1 ∈ (FinHTupleMap.cast (Layout.id (h(nJ))) (h(nJ)) (h(nJ * 1)) (by simp) (by simp)).rangeNat := by
    exact mem_rangeNat_cast_id_leaf nJ j
  rw [dif_pos h]
  have h' : (FinHTupleMap.cast (Layout.id (h(nJ))) (h(nJ)) (h(nJ * 1)) (by simp) (by simp)).rangeNatInv j.1 h
            =
            ⟨j.1, by get_elem_tactic⟩ := by
    exact rangeNatInv_cast_id_leaf nJ j h
  simp [h']
  change (∑ x_1 ∈ (entries ((0 : HTuple Nat .leaf)...h(nI))).toFinset, _) = _
  rw [FinHTuple.sum_zeroRange_eq_fin]
  apply Finset.sum_congr rfl
  intro i _
  simp [HTuple.numel_leaf, getElem, get, HasFlatRepr.get,
        offset, mul_one, IndexType.toFin_fromFin, Layout.colMajor, FinHTupleMap.colMajorMap,
        HTuple.numel_prod, FinHTupleMap.eval_mk, HTupleMap.eval_colMajorMap,
        HTuple.colMajorIndex, HTuple.leaf_toScalar, toFin, finProdFinEquiv_apply_val,
        FinHTuple.equivFin, FinHTuple.leafEquiv]
  rw [mul_comm]
  rfl

theorem getElem_matMul_fin (A : Tensor R (I × J)) (B : Tensor R (J × K))
    (i : Fin nI) (k : Fin nK) :
    (A *ᵥ B)[fromFin (I:=I) i, fromFin (I:=K) k] =
      ∑ j : Fin nJ, A[fromFin (I:=I) i, fromFin (I:=J) j] *
        B[fromFin (I:=J) j, fromFin (I:=K) k] := by
  simp only [VMul.vmul, matMul]
  simp only [getElem_mk]
  simp only [HasFlatRepr.get]
  rw [TensorRingOps.get_tensorGemm']
  simp only [Nat.mul_one, one_mul, zero_mul, add_zero]
  have hmem := rowMajorCast2D_mem_toFin (I := I) (J := K) i k
  rw [dif_pos hmem]
  have hinv : (rowMajorCast2D nI nK).rangeNatInv
      ((IndexType.toFin (I := I × K) (fromFin (I := I) i, fromFin (I := K) k)).1)
      (by simpa [Nat.mul_one] using hmem) =
      (⟨h(i.1, k.1), by simp [i.2, k.2]⟩ : FinHTuple h(nI, nK)) := by
    exact rowMajorCast2D_rangeNatInv_toFin (I := I) (J := K) i k
      (by simpa [Nat.mul_one] using hmem)
  rw [hinv]
  apply Finset.sum_congr rfl
  intro j _hj
  congr
  · exact rowMajorCast2D_left_offset (I := I) (J := J) i j
  · exact rowMajorCast2D_right_offset (I := J) (J := K) j k

@[simp]
theorem finvecEquiv_vecMatMul (A : Tensor R (I × J)) (x : Tensor R J) :
  finvecEquiv (A *ᵥ x) = (matrixEquiv A).mulVec (finvecEquiv x) := by
  ext i
  change (A *ᵥ x)[fromFin (I:=I) i] = (matrixEquiv A).mulVec (finvecEquiv x) i
  rw [getElem_matVecMul_fin]
  simp [finvecEquiv, matrixEquiv, Matrix.mulVec, dotProduct]

@[simp]
theorem finvecEquiv_matVecMul (A : Tensor R (I × J)) (x : Tensor R I) :
  finvecEquiv (x *ᵥ A) = (matrixEquiv A).vecMul (finvecEquiv x) := by
  ext j
  change (x *ᵥ A)[fromFin (I:=J) j] = (matrixEquiv A).vecMul (finvecEquiv x) j
  rw [getElem_vecMatMul_fin]
  simp [finvecEquiv, matrixEquiv, Matrix.vecMul, dotProduct]

@[simp]
theorem finvecEquiv_matMul (A : Tensor R (I × J)) (B : Tensor R (J × K)) :
  matrixEquiv (A *ᵥ B) = (matrixEquiv A) * (matrixEquiv B) := by
  ext i k
  change (A *ᵥ B)[fromFin (I:=I) i, fromFin (I:=K) k] =
    ((matrixEquiv A) * (matrixEquiv B)) i k
  rw [getElem_matMul_fin]
  simp [matrixEquiv, Matrix.mul_apply]

end MatrixEquiv
