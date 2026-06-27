import NumLean.Data.Prod
import NumLean.Interfaces.HasFlatRepr.Basic

namespace NumLean

namespace HasFlatRepr

variable {X : Type u} {Y : Type v} {Ks : Nat → Type w} {K : Type z} {nX nY : Nat}
  [VectorType Ks K] [HasFlatRepr X Ks nX] [HasFlatRepr Y Ks nY]

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

theorem prod_getComp_left (xy : X × Y) (i : Nat) (h : i < nX + nY) (hi : i < nX) :
    prodGetComp (Ks := Ks) xy i h = HasFlatRepr.getComp (Ks := Ks) xy.1 i hi := by
  simp [prodGetComp, hi]

theorem prod_getComp_right (xy : X × Y) (i : Nat) (h : i < nX + nY) (hi : ¬ i < nX) :
    prodGetComp (Ks := Ks) xy i h = HasFlatRepr.getComp (Ks := Ks) xy.2 (i - nX) (by omega) := by
  simp [prodGetComp, hi]

-- todo: this is not a good implementation
def prodSetComp (xy : X × Y) (i : Nat) (k : K) (h : i < nX + nY) : X × Y :=
  let xy' := (prodToVector (Ks := Ks) xy).set i k h
  (HasFlatRepr.fromVector (Ks := Ks) (X := X) (Vector.ofFn fun j : Fin nX => xy'[j.1]'(by omega)),
   HasFlatRepr.fromVector (Ks := Ks) (X := Y) (Vector.ofFn fun j : Fin nY => xy'[nX + j.1]'(by omega)))

def prodGet {n : Nat} (ks : Ks n) (off : Nat) (h : off + (nX + nY) ≤ n) : X × Y :=
  (HasFlatRepr.get (X := X) ks off (by omega),
   HasFlatRepr.get (X := Y) ks (off + nX) (by omega))

def prodSet {n : Nat} (ks : Ks n) (off : Nat) (xy : X × Y) (h : off + (nX + nY) ≤ n) : Ks n :=
  let ks := HasFlatRepr.set (X := X) ks off xy.1 (by omega)
  HasFlatRepr.set (X := Y) ks (off + nX) xy.2 (by omega)

def prodToFlatVector (xy : X × Y) : Ks (nX + nY) :=
  VectorType.append (HasFlatRepr.toFlatVector (Ks := Ks) xy.1) (HasFlatRepr.toFlatVector (Ks := Ks) xy.2)

theorem prod_get_toFlatVector_eq_getComp (xy : X × Y) (i : Nat) (hi : i < nX + nY) :
    VectorType.get (prodToFlatVector (Ks := Ks) xy) i hi = prodGetComp (Ks := Ks) xy i hi := by
  rcases xy with ⟨x, y⟩
  by_cases hleft : i < nX
  · rw [prod_getComp_left (Ks := Ks) (x, y) i hi hleft]
    dsimp [prodToFlatVector]
    rw [VectorType.get_append_left]
    rw [HasFlatRepr.get_toFlatVector_eq_getComp]
  · rw [prod_getComp_right (Ks := Ks) (x, y) i hi hleft]
    dsimp [prodToFlatVector]
    rw [VectorType.get_append_right]
    · rw [HasFlatRepr.get_toFlatVector_eq_getComp]
    · omega

-- todo: this could be improved, I think   `(kx ++ x) ++ y` is better than `ks ++ (x ++ y)`
def prodPush {n : Nat} (ks : Ks n) (xy : X × Y) : Ks (n + (nX + nY)) :=
  VectorType.append ks (prodToFlatVector (Ks := Ks) xy)

-- todo: this is bad, don't use fromVector/Vector.ofFn etc
-- do we need TensorType to do this efficiently? we can just convert `x` and `y` to `Ks` and
-- blast it with broadcasting copySlice
def prodReplicate (n : Nat) (xy : X × Y) : Ks (n * (nX + nY)) :=
  VectorType.fromVector (As := Ks) <| Vector.ofFn fun ij : Fin (n * (nX + nY)) =>
    prodGetComp (Ks := Ks) xy (ij.1 % (nX + nY)) (by
      by_cases h : nX + nY = 0
      · have := ij.2
        simp [h] at this
      · exact Nat.mod_lt _ (Nat.pos_of_ne_zero h))

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
    rfl
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
    · simpa [Nat.add_sub_cancel_left] using prod_get_toFlatVector_eq_getComp (Ks := Ks) xy i hi
    · omega
  toFlatVector := prodToFlatVector (Ks := Ks)
  get_toFlatVector_eq_getComp := by
    intro xy i hi
    exact prod_get_toFlatVector_eq_getComp (Ks := Ks) xy i hi
  replicate := prodReplicate (Ks := Ks)
  get_replicate := by
    intro n xy i j hi hj
    rw [prodReplicate]
    rw [VectorType.get_spec, VectorType.toVector_fromVector]
    rw [Vector.getElem_ofFn]
    have hmod : (i * (nX + nY) + j) % (nX + nY) = j := by
      rw [Nat.mul_add_mod_self_right]
      exact Nat.mod_eq_of_lt hj
    simp [hmod]

end HasFlatRepr

end NumLean
