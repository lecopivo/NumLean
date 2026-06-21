import NumLean.Data.Prod
import NumLean.Interfaces.HasFlatRepr.Basic

namespace NumLean

namespace HasFlatRepr

variable {X : Type u} {Y : Type v} {Ks : Nat → Type w} {K : Type z} {nX nY : Nat}
  [VectorType Ks K] [HasFlatRepr X Ks nX] [HasFlatRepr Y Ks nY]

private def prodToVector (xy : X × Y) : Vector K (nX + nY) :=
  HasFlatRepr.toVector (Ks := Ks) xy.1 ++ HasFlatRepr.toVector (Ks := Ks) xy.2

private def prodFromVector (xy : Vector K (nX + nY)) : X × Y :=
  (HasFlatRepr.fromVector (Ks := Ks) (X := X) (Vector.ofFn fun i : Fin nX => xy[i.1]),
   HasFlatRepr.fromVector (Ks := Ks) (X := Y) (Vector.ofFn fun i : Fin nY => xy[nX + i.1]))

private def prodGetComp (xy : X × Y) (i : Nat) (h : i < nX + nY) : K :=
  if hi : i < nX then
    HasFlatRepr.getComp (Ks := Ks) xy.1 i hi
  else
    HasFlatRepr.getComp (Ks := Ks) xy.2 (i - nX) (by omega)

private theorem prod_getComp_left (xy : X × Y) (i : Nat) (h : i < nX + nY) (hi : i < nX) :
    prodGetComp (Ks := Ks) xy i h = HasFlatRepr.getComp (Ks := Ks) xy.1 i hi := by
  simp [prodGetComp, hi]

private theorem prod_getComp_right (xy : X × Y) (i : Nat) (h : i < nX + nY) (hi : ¬ i < nX) :
    prodGetComp (Ks := Ks) xy i h = HasFlatRepr.getComp (Ks := Ks) xy.2 (i - nX) (by omega) := by
  simp [prodGetComp, hi]

private def prodSetComp (xy : X × Y) (i : Nat) (k : K) (h : i < nX + nY) : X × Y :=
  let xy' := (prodToVector (Ks := Ks) xy).set i k h
  (HasFlatRepr.fromVector (Ks := Ks) (X := X) (Vector.ofFn fun j : Fin nX => xy'[j.1]'(by omega)),
   HasFlatRepr.fromVector (Ks := Ks) (X := Y) (Vector.ofFn fun j : Fin nY => xy'[nX + j.1]'(by omega)))

private def prodGet {n : Nat} (ks : Ks n) (off : Nat) (h : off + (nX + nY) ≤ n) : X × Y :=
  (HasFlatRepr.get (X := X) ks off (by omega),
   HasFlatRepr.get (X := Y) ks (off + nX) (by omega))

private def prodSet {n : Nat} (ks : Ks n) (off : Nat) (xy : X × Y) (h : off + (nX + nY) ≤ n) : Ks n :=
  let ks := HasFlatRepr.set (X := X) ks off xy.1 (by omega)
  HasFlatRepr.set (X := Y) ks (off + nX) xy.2 (by omega)

private def prodPush {n : Nat} (ks : Ks n) (xy : X × Y) : Ks (n + (nX + nY)) :=
  have h : n + nX + nY = n + (nX + nY) := by omega
  h ▸ HasFlatRepr.push (X := Y) (HasFlatRepr.push (X := X) ks xy.1) xy.2

private def prodToFlatVector (xy : X × Y) : Ks (nX + nY) :=
  VectorType.append (HasFlatRepr.toFlatVector (Ks := Ks) xy.1) (HasFlatRepr.toFlatVector (Ks := Ks) xy.2)

private def prodReplicate (n : Nat) (xy : X × Y) : Ks (n * (nX + nY)) :=
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
    sorry
  right_inv := by
    sorry
  getComp := prodGetComp (Ks := Ks)
  getComp_spec := by
    sorry
  setComp := prodSetComp (Ks := Ks)
  setComp_spec := by
    intro xy i k h
    rcases xy with ⟨x, y⟩
    rfl
  get := prodGet (Ks := Ks)
  getComp_get_eq_vector_get := by
    sorry
  set := prodSet (Ks := Ks)
  vector_get_set_eq := by
    sorry
  vector_get_set_ne := by
    sorry
  push := prodPush (Ks := Ks)
  vector_get_push_lt := by
    sorry
  vector_get_push_eq := by
    sorry
  toFlatVector := prodToFlatVector (Ks := Ks)
  get_toFlatVector_eq_getComp := by
    sorry
  replicate := prodReplicate (Ks := Ks)
  get_replicate := by
    sorry

end HasFlatRepr

end NumLean
