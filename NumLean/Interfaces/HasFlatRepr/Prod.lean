module

public import NumLean.Data.Prod
public import NumLean.Interfaces.HasFlatRepr.Basic
public import NumLean.Interfaces.TensorType

@[expose] public section

namespace NumLean

namespace HasFlatRepr

variable {X : Type u} {Y : Type v} {Ks : Nat → Type} {K : Type} {nX nY : Nat}
  [VectorType Ks K] [TensorType Ks (K := K)] [HasFlatRepr X Ks nX] [HasFlatRepr Y Ks nY]

def prodToVector (xy : X × Y) : Vector K (nX + nY) :=
  HasFlatRepr.toVector (Ks := Ks) xy.1 ++ HasFlatRepr.toVector (Ks := Ks) xy.2

def prodFromVector (xy : Vector K (nX + nY)) : X × Y :=
  (HasFlatRepr.fromVector (Ks := Ks) (X := X) (Vector.ofFn fun i : Fin nX => xy[i.1]),
   HasFlatRepr.fromVector (Ks := Ks) (X := Y) (Vector.ofFn fun i : Fin nY => xy[nX + i.1]))

def prodGetComp (xy : X × Y) (i : Nat) (h : i < nX + nY) : K :=
  if hi : i < nX then
    HasFlatRepr.getComp (Ks := Ks) xy.1 i hi
  else
    HasFlatRepr.getComp (Ks := Ks) xy.2 (i - nX) (by omega)

omit [TensorType Ks] in
theorem prod_getComp_left (xy : X × Y) (i : Nat) (h : i < nX + nY) (hi : i < nX) :
    prodGetComp (Ks := Ks) xy i h = HasFlatRepr.getComp (Ks := Ks) xy.1 i hi := by
  simp [prodGetComp, hi]

omit [TensorType Ks] in
theorem prod_getComp_right (xy : X × Y) (i : Nat) (h : i < nX + nY) (hi : ¬ i < nX) :
    prodGetComp (Ks := Ks) xy i h = HasFlatRepr.getComp (Ks := Ks) xy.2 (i - nX) (by omega) := by
  simp [prodGetComp, hi]

def prodSetComp (xy : X × Y) (i : Nat) (k : K) (h : i < nX + nY) : X × Y :=
  if hi : i < nX then
    (HasFlatRepr.setComp (Ks := Ks) xy.1 i k hi, xy.2)
  else
    (xy.1, HasFlatRepr.setComp (Ks := Ks) xy.2 (i - nX) k (by omega))

def prodGet {n : Nat} (ks : Ks n) (off : Nat) (h : off + (nX + nY) ≤ n) : X × Y :=
  (HasFlatRepr.get (X := X) ks off (by omega),
   HasFlatRepr.get (X := Y) ks (off + nX) (by omega))

def prodSet {n : Nat} (ks : Ks n) (off : Nat) (xy : X × Y) (h : off + (nX + nY) ≤ n) : Ks n :=
  let ks := HasFlatRepr.set (X := X) ks off xy.1 (by omega)
  HasFlatRepr.set (X := Y) ks (off + nX) xy.2 (by omega)

def prodToTensor (xy : X × Y) : Ks (nX + nY) :=
  VectorType.append (HasFlatRepr.toTensor (Ks := Ks) xy.1) (HasFlatRepr.toTensor (Ks := Ks) xy.2)

omit [TensorType Ks] in
theorem prod_get_toTensor_eq_getComp (xy : X × Y) (i : Nat) (hi : i < nX + nY) :
    VectorType.get (prodToTensor (Ks := Ks) xy) i hi = prodGetComp (Ks := Ks) xy i hi := by
  rcases xy with ⟨x, y⟩
  by_cases hleft : i < nX
  · rw [prod_getComp_left (Ks := Ks) (x, y) i hi hleft]
    dsimp [prodToTensor]
    rw [VectorType.get_append_left]
    rw [HasFlatRepr.get_toTensor_eq_getComp]
  · rw [prod_getComp_right (Ks := Ks) (x, y) i hi hleft]
    dsimp [prodToTensor]
    rw [VectorType.get_append_right]
    · rw [HasFlatRepr.get_toTensor_eq_getComp]
    · omega

-- todo: this could be improved, I think   `(kx ++ x) ++ y` is better than `ks ++ (x ++ y)`
def prodPush {n : Nat} (ks : Ks n) (xy : X × Y) : Ks (n + (nX + nY)) :=
  VectorType.append ks (prodToTensor (Ks := Ks) xy)

def prodReplicate (n : Nat) (xy : X × Y) : Ks (n * (nX + nY)) :=
  let src : Ks (nX + nY) := prodToTensor (Ks := Ks) xy
  let srcMap : Tensor.Layout h(n, nX + nY) h(nX + nY) :=
    FinHTupleMap.sndMap h(n) h(nX + nY)
  let dst : Ks (n * (nX + nY)) :=
    if hzero : nX + nY = 0 then
      cast (by simp [hzero]) (VectorType.emptyWithCapacity (As := Ks) 0)
    else
      VectorType.replicate (As := Ks) (n * (nX + nY))
        (prodGetComp (Ks := Ks) xy 0 (Nat.pos_of_ne_zero hzero))
  let dstMap : Tensor.Layout h(n, nX + nY) h(n * (nX + nY)) :=
    Tensor.Layout.rowMajor h(n, nX + nY)
  TensorType.copySlice (Ks := Ks) (K := K) src srcMap dst dstMap
    (FinHTupleMap.injective_rowMajorMap h(n, nX + nY))

instance : HasFlatRepr (X × Y) Ks (nX + nY) where
  toVector := prodToVector (Ks := Ks)
  fromVector := prodFromVector (Ks := Ks)
  left_inv := by
    intro xy
    rcases xy with ⟨x, y⟩
    apply Prod.ext
    · change HasFlatRepr.fromVector (Ks := Ks) (X := X)
        (Vector.ofFn fun i : Fin nX => (prodToVector (Ks := Ks) (x, y))[i.1]) = x
      rw [← HasFlatRepr.fromVector_toVector (Ks := Ks) x]
      congr 1
      apply Vector.ext
      intro i hi
      simp [prodToVector]
    · change HasFlatRepr.fromVector (Ks := Ks) (X := Y)
        (Vector.ofFn fun i : Fin nY => (prodToVector (Ks := Ks) (x, y))[nX + i.1]) = y
      rw [← HasFlatRepr.fromVector_toVector (Ks := Ks) y]
      congr 1
      apply Vector.ext
      intro i hi
      simp [prodToVector]
  right_inv := by
    intro xy
    ext i ih
    by_cases h : i < nX
    · change (prodToVector (Ks := Ks) (prodFromVector (Ks := Ks) xy))[i] = xy[i]
      simp [prodToVector, prodFromVector, h]
    · change (prodToVector (Ks := Ks) (prodFromVector (Ks := Ks) xy))[i] = xy[i]
      rw [prodToVector, Vector.getElem_append_right ih (by omega)]
      simp [prodFromVector]
      have hidx : nX + (i - nX) = i := Nat.add_sub_of_le (Nat.le_of_not_gt h)
      exact getElem_congr rfl hidx (by omega)
  getComp := prodGetComp (Ks := Ks)
  getComp_spec := by
    intro xy i h
    rcases xy with ⟨x, y⟩
    by_cases hi : i < nX
    · simp [prodGetComp, prodToVector, hi, HasFlatRepr.getComp_spec, Vector.getElem_append_left hi]
    · simp [prodGetComp, prodToVector, hi, HasFlatRepr.getComp_spec]
      rw [Vector.getElem_append_right h (by omega)]
  setComp := prodSetComp (Ks := Ks)
  setComp_spec := by
    intro xy i k h
    rcases xy with ⟨x, y⟩
    apply Prod.ext
    · by_cases hi : i < nX
      · dsimp [prodSetComp, prodFromVector]
        simp [hi]
        let v : Vector K nX := Vector.ofFn fun j : Fin nX => ((prodToVector (Ks := Ks) (x, y)).set i k h)[j.1]
        change HasFlatRepr.setComp (Ks := Ks) x i k hi = HasFlatRepr.fromVector (Ks := Ks) v
        apply HasFlatRepr.ext (Ks := Ks)
        intro j hj
        rw [HasFlatRepr.getComp_spec, HasFlatRepr.getComp_spec,
          HasFlatRepr.setComp_spec, HasFlatRepr.toVector_fromVector]
        rw [HasFlatRepr.toVector_fromVector]
        by_cases hji : j = i
        · subst hji
          simp [v]
        · rw [Vector.getElem_set]
          simp [show i ≠ j by omega, v, prodToVector,
            Vector.getElem_append_left hj]
      · dsimp [prodSetComp, prodFromVector]
        simp [hi]
        rw [← HasFlatRepr.fromVector_toVector (Ks := Ks) x]
        congr 1
        apply Vector.ext
        intro j hj
        rw [Vector.getElem_ofFn]
        rw [Vector.getElem_set]
        simp [show i ≠ j by omega]
        simp [prodToVector, Vector.getElem_append_left hj]
    · by_cases hi : i < nX
      · dsimp [prodSetComp, prodFromVector]
        simp [hi]
        rw [← HasFlatRepr.fromVector_toVector (Ks := Ks) y]
        congr 1
        apply Vector.ext
        intro j hj
        rw [Vector.getElem_ofFn]
        rw [Vector.getElem_set]
        simp [show i ≠ nX + j by omega]
        simp [prodToVector]
      · dsimp [prodSetComp, prodFromVector]
        simp [hi]
        let v : Vector K nY :=
          Vector.ofFn fun j : Fin nY => ((prodToVector (Ks := Ks) (x, y)).set i k h)[nX + j.1]
        change HasFlatRepr.setComp (Ks := Ks) y (i - nX) k (by omega) =
          HasFlatRepr.fromVector (Ks := Ks) v
        apply HasFlatRepr.ext (Ks := Ks)
        intro j hj
        rw [HasFlatRepr.getComp_spec, HasFlatRepr.getComp_spec,
          HasFlatRepr.setComp_spec, HasFlatRepr.toVector_fromVector]
        rw [HasFlatRepr.toVector_fromVector]
        change ((HasFlatRepr.toVector (Ks := Ks) y).set (i - nX) k (by omega))[j] = v[j]
        by_cases hji : j = i - nX
        · subst hji
          rw [Vector.getElem_set_self]
          simp [v, prodToVector, show nX + (i - nX) = i by omega]
        · rw [Vector.getElem_set]
          simp [show i - nX ≠ j by omega, v, prodToVector]
          rw [Vector.getElem_set]
          simp [show i ≠ nX + j by omega]
  get := prodGet (Ks := Ks)
  getComp_get_eq_vector_get := by
    intro n ks off i hoff hi
    by_cases hleft : i < nX
    · rw [prod_getComp_left (Ks := Ks) (prodGet (Ks := Ks) ks off hoff) i hi hleft]
      change HasFlatRepr.getComp (Ks := Ks) (HasFlatRepr.get (X := X) ks off (by omega)) i hleft =
        VectorType.get ks (off + i) (by grind)
      rw [HasFlatRepr.getComp_get_eq_vector_get]
    · rw [prod_getComp_right (Ks := Ks) (prodGet (Ks := Ks) ks off hoff) i hi hleft]
      change HasFlatRepr.getComp (Ks := Ks) (HasFlatRepr.get (X := Y) ks (off + nX) (by omega))
          (i - nX) (by omega) = VectorType.get ks (off + i) (by grind)
      rw [HasFlatRepr.getComp_get_eq_vector_get]
      congr 1
      omega
  set := prodSet (Ks := Ks)
  vector_get_set_eq := by
    intro n ks off i xy hoff hi
    rcases xy with ⟨x, y⟩
    dsimp [prodSet]
    by_cases hleft : i < off + nX
    · rw [HasFlatRepr.vector_get_set_ne (X := Y)]
      · rw [HasFlatRepr.vector_get_set_eq (X := X)]
        rotate_left
        · exact And.intro (by omega) (by omega)
        rw [prod_getComp_left (Ks := Ks) (x, y) (i - off) (by omega) (by omega)]
      · omega
      · omega
    · rw [HasFlatRepr.vector_get_set_eq (X := Y)]
      rotate_left
      · exact And.intro (by omega) (by omega)
      rw [prod_getComp_right (Ks := Ks) (x, y) (i - off) (by omega) (by omega)]
      congr 1
      omega
  vector_get_set_ne := by
    intro n ks off i xy hoff hi hi'
    rcases xy with ⟨x, y⟩
    dsimp [prodSet]
    rw [HasFlatRepr.vector_get_set_ne (X := Y)]
    · rw [HasFlatRepr.vector_get_set_ne (X := X)]
      · grind
    · grind
    · exact hi'
  push := prodPush (Ks := Ks)
  vector_get_push_lt := by
    intro n ks xy i hi
    dsimp [prodPush]
    rw [VectorType.get_append_left]
  vector_get_push_eq := by
    intro n ks xy i hi
    dsimp [prodPush]
    rw [VectorType.get_append_right]
    · simpa [Nat.add_sub_cancel_left] using prod_get_toTensor_eq_getComp (Ks := Ks) xy i hi
    · omega
  toTensor := prodToTensor (Ks := Ks)
  get_toTensor_eq_getComp := by
    intro xy i hi
    exact prod_get_toTensor_eq_getComp (Ks := Ks) xy i hi
  replicate := prodReplicate (Ks := Ks)
  get_replicate := by
    intro n xy i j hi hj
    rw [prodReplicate]
    rw [TensorType.get_copySlice]
    split
    · rename_i hmem
      have hidx : (h(i, j) : HTuple Nat (.prod .leaf .leaf)).rowMajorIndex h(n, nX + nY) =
          i * (nX + nY) + j := by
        simp
        rw [Nat.mul_comm (nX + nY) i, Nat.add_comm]
      have hinv : (Tensor.Layout.rowMajor h(n, nX + nY)).rangeNatInv
            (i * (nX + nY) + j) hmem =
          (⟨h(i, j), by get_elem_tactic⟩ : FinHTuple h(n, nX + nY)) := by
        exact FinHTupleMap.rangeNatInv_rowMajorIndex_of_eq h(n, nX + nY) h(i, j)
          (by get_elem_tactic) hidx.symm hmem
      have hval := congrArg FinHTuple.val hinv
      simp at hval
      simp [hval, prod_get_toTensor_eq_getComp]
    · rename_i hmem
      exfalso
      have hidx : (h(i, j) : HTuple Nat (.prod .leaf .leaf)).rowMajorIndex h(n, nX + nY) =
          i * (nX + nY) + j := by
        simp
        rw [Nat.mul_comm (nX + nY) i, Nat.add_comm]
      exact hmem (hidx ▸
        FinHTupleMap.mem_rangeNat_rowMajorIndex h(n, nX + nY) h(i, j) (by get_elem_tactic))

end HasFlatRepr

end NumLean
