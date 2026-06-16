import NumLean.Data.TensorIndex.TensorIndexType


namespace NumLean

namespace TensorIndex

#exit
/-- Multiply every stride by a scalar. -/
def scaleStrides {rank : Nat} (c : Nat) (strides : Vector Nat rank) : Vector Nat rank :=
  Vector.ofFn fun i => c * strides[i]

theorem offset_scaleStrides {rank : Nat} {dims : Vector Nat rank}
    (idx : TensorIndex dims) (c : Nat) (strides : Vector Nat rank) :
    idx.offset (scaleStrides c strides) = c * idx.offset strides := by
  unfold offset offsetOf scaleStrides
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

/-- Positive scalar multiplication preserves valid strides. -/
theorem ValidStrides.scale {rank : Nat} {dims strides : Vector Nat rank}
    {c : Nat} (hc : 0 < c) (h : ValidStrides dims strides) :
    ValidStrides dims (scaleStrides c strides) := by
  intro idx idx' hoff
  apply h
  dsimp only at hoff
  rw [offset_scaleStrides idx c strides, offset_scaleStrides idx' c strides] at hoff
  exact (Nat.mul_left_cancel_iff hc).mp hoff

end TensorIndex

/-- All offsets produced by `ioffset` and `istrides` land inside a flat target of size `nI`. -/
def TensorSliceInBounds {rank : Nat} (dims : Vector Nat rank)
    (ioffset : Nat) (istrides : Vector Nat rank) (nI : Nat) : Prop :=
  ∀ jt : TensorIndex dims, ioffset + jt.offset istrides < nI

-- this does not fix any particular linear order but guarantees injectivity
structure TensorSliceMap (J I : Type*) {nJ nI : Nat} {jrank : Nat}
    {jdims : Vector Nat jrank} {jaxis : TensorIndex.AxisOrder jrank}
    [TensorIndexType J nJ jrank jdims jaxis] [IndexType I nI] where
  /-- Efficient implementation of this slice map. -/
  map : J → I

  /-- Base flat offset in the target index space. -/
  ioffset : Nat

  /-- Source tensor strides interpreted in the target flat index space. -/
  istrides : Vector Nat jrank

  /-- Target strides faithfully embed the source tensor index space. -/
  istrides_valid : TensorIndex.ValidStrides jdims istrides

  /-- Every produced target offset is valid for `I`. -/
  in_bounds : TensorSliceInBounds jdims ioffset istrides nI

  /-- The efficient implementation agrees with the canonical offset-based map. -/
  map_eq_toFun :
    map = fun j =>
      let jt := TensorIndexType.toTensorIndex j
      fromFin ⟨ioffset + jt.offset istrides, in_bounds jt⟩

namespace TensorSliceMap

variable {J I : Type u} {nJ nI jrank : Nat} {jdims : Vector Nat jrank}
    {jaxis : TensorIndex.AxisOrder jrank}
    [TensorIndexType J nJ jrank jdims jaxis] [IndexType I nI]

/-- The map induced by a base offset and target strides. -/
def toFun (m : TensorSliceMap J I) : J → I :=
  m.map

instance : CoeFun (TensorSliceMap J I) (fun _ => J → I) where
  coe := toFun

def mkFinRange (start count : Nat) (h : start + count ≤ nI) : TensorSliceMap (Fin count) I where
  map idx :=
    let i : Fin nI := ⟨start + idx.1, by grind⟩
    IndexType.fromFin i
  ioffset := start
  istrides := #v[1]
  istrides_valid := sorry
  in_bounds := sorry
  map_eq_toFun := sorry


/-- The canonical offset-based definition that `map` must implement. -/
def specFun (m : TensorSliceMap J I) : J → I :=
  fun j =>
    let jt := TensorIndexType.toTensorIndex j
    fromFin ⟨m.ioffset + jt.offset m.istrides, m.in_bounds jt⟩

theorem map_eq_specFun (m : TensorSliceMap J I) : m.map = m.specFun :=
  m.map_eq_toFun

/-- Adding a fixed base offset preserves stride injectivity. -/
theorem offset_injective_with_base {rank : Nat} {dims : Vector Nat rank}
    {strides : Vector Nat rank} (base : Nat)
    (h : TensorIndex.ValidStrides dims strides) :
    Function.Injective (fun idx : TensorIndex dims => base + idx.offset strides) := by
  intro idx idx' hoff
  apply h
  exact Nat.add_left_cancel hoff

/-- A tensor slice map is injective. -/
theorem injective (m : TensorSliceMap J I) : Function.Injective m.toFun := by
  intro j j' hmap
  rw [toFun] at hmap
  rw [m.map_eq_specFun] at hmap
  have hfin := congrArg (fun i : I => toFin i) hmap
  have hoff :
      m.ioffset + (TensorIndexType.toTensorIndex j).offset m.istrides =
        m.ioffset + (TensorIndexType.toTensorIndex j').offset m.istrides := by
    simpa [specFun] using congrArg Fin.val hfin
  have hidx : TensorIndexType.toTensorIndex j = TensorIndexType.toTensorIndex j' :=
    offset_injective_with_base m.ioffset m.istrides_valid hoff
  exact TensorIndexTypeOfRank.tensorEquiv.injective hidx

/-- Low-level constructor from explicit tensor strides and bounds. -/
def box (I : Type u) {nI rank : Nat} {dims : Vector Nat rank}
    {axis : TensorIndex.AxisOrder rank}
    [TensorIndexType J nJ rank dims axis] [IndexType I nI]
    (ioffset : Nat) (istrides : Vector Nat rank)
    (hvalid : TensorIndex.ValidStrides dims istrides)
    (hbounds : TensorSliceInBounds dims ioffset istrides nI) :
    TensorSliceMap J I :=
  { map := fun j =>
      let jt := TensorIndexType.toTensorIndex j
      fromFin ⟨ioffset + jt.offset istrides, hbounds jt⟩
    ioffset := ioffset
    istrides := istrides
    istrides_valid := hvalid
    in_bounds := hbounds
    map_eq_toFun := rfl }

/-- The identity slice map for a tensor index type. -/
def id (I : Type u) {n rank : Nat} {dims : Vector Nat rank}
    {axis : TensorIndex.AxisOrder rank} [TensorIndexType I n rank dims axis] :
    TensorSliceMap I I :=
  { map := fun i => i
    ioffset := 0
    istrides := TensorIndex.denseStridesForOrder dims axis
    istrides_valid := TensorIndex.validStrides_denseStridesForOrder dims axis
    in_bounds := by
      intro idx
      have hlt := TensorIndex.offset_denseStridesForOrder_lt_numel axis idx
      have hn : n = TensorIndex.numel dims :=
        TensorIndexTypeOfRank.n_eq_numel (I := I) (n := n) (rank := rank)
          (dims := dims) (axis := axis)
      have hlt' : 0 + idx.offset (TensorIndex.denseStridesForOrder dims axis) <
          TensorIndex.numel dims := by
        simpa using hlt
      exact hn.symm ▸ hlt'
    map_eq_toFun := by
      funext i
      rw [← IndexType.fromFin_toFin i]
      apply congrArg (fromFin (I := I))
      apply Fin.ext
      simp [TensorIndexTypeOfRank.toFin_eq_offset (I := I) (n := n) (rank := rank)
        (dims := dims) (axis := axis) i, TensorIndexType.toTensorIndex] }

/-- Embed the left factor into a product by fixing the right factor at `j`. -/
def prodLeft (I J : Type u)
    {nI nJ irank : Nat} {idims : Vector Nat irank}
    {iaxis : TensorIndex.AxisOrder irank}
    [TensorIndexType I nI irank idims iaxis] [IndexType J nJ]
    (j : J) : TensorSliceMap I (I × J) :=
  have hnJ : 0 < nJ := Nat.lt_of_le_of_lt (Nat.zero_le _) (toFin j).2
  { map := fun i => (i, j)
    ioffset := (toFin j).1
    istrides := TensorIndex.scaleStrides nJ (TensorIndex.denseStridesForOrder idims iaxis)
    istrides_valid :=
      TensorIndex.ValidStrides.scale hnJ
        (TensorIndex.validStrides_denseStridesForOrder idims iaxis)
    in_bounds := by
      intro idx
      have hlt := TensorIndex.offset_denseStridesForOrder_lt_numel iaxis idx
      have hnI : nI = TensorIndex.numel idims :=
        TensorIndexTypeOfRank.n_eq_numel (I := I) (n := nI) (rank := irank)
          (dims := idims) (axis := iaxis)
      rw [TensorIndex.offset_scaleStrides]
      have hltI : idx.offset (TensorIndex.denseStridesForOrder idims iaxis) < nI :=
        hnI.symm ▸ hlt
      calc
        (toFin j).1 + nJ * idx.offset (TensorIndex.denseStridesForOrder idims iaxis)
            < nJ + nJ * idx.offset (TensorIndex.denseStridesForOrder idims iaxis) := by
              exact Nat.add_lt_add_right (toFin j).2 _
        _ = (idx.offset (TensorIndex.denseStridesForOrder idims iaxis) + 1) * nJ := by ring
        _ ≤ nI * nJ := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hltI)
    map_eq_toFun := by
      funext i
      rw [← IndexType.fromFin_toFin (I := I × J) (i, j)]
      apply congrArg (fromFin (I := I × J))
      apply Fin.ext
      have hi := TensorIndexTypeOfRank.toFin_eq_offset (I := I) (n := nI)
        (rank := irank) (dims := idims) (axis := iaxis) i
      calc
        ↑(toFin ((i, j) : I × J))
            = ↑(toFin j) + nJ * ↑(toFin i) := rfl
        _ = ↑(toFin j) + nJ * (TensorIndexType.toTensorIndex i).offset
              (TensorIndex.denseStridesForOrder idims iaxis) := by
              rw [hi]
              rfl
        _ = ↑(toFin j) + (TensorIndexType.toTensorIndex i).offset
              (TensorIndex.scaleStrides nJ (TensorIndex.denseStridesForOrder idims iaxis)) := by
              rw [TensorIndex.offset_scaleStrides] }

/-- Embed the right factor into a product by fixing the left factor at `i`. -/
def prodRight (I J : Type u)
    {nI nJ jrank : Nat} {jdims : Vector Nat jrank}
    {jaxis : TensorIndex.AxisOrder jrank}
    [IndexType I nI] [TensorIndexType J nJ jrank jdims jaxis]
    (i : I) : TensorSliceMap J (I × J) :=
  { map := fun j => (i, j)
    ioffset := nJ * (toFin i).1
    istrides := TensorIndex.denseStridesForOrder jdims jaxis
    istrides_valid := TensorIndex.validStrides_denseStridesForOrder jdims jaxis
    in_bounds := by
      intro idx
      have hlt := TensorIndex.offset_denseStridesForOrder_lt_numel jaxis idx
      have hnJ : nJ = TensorIndex.numel jdims :=
        TensorIndexTypeOfRank.n_eq_numel (I := J) (n := nJ) (rank := jrank)
          (dims := jdims) (axis := jaxis)
      have hltJ : idx.offset (TensorIndex.denseStridesForOrder jdims jaxis) < nJ :=
        hnJ.symm ▸ hlt
      calc
        nJ * (toFin i).1 + idx.offset (TensorIndex.denseStridesForOrder jdims jaxis)
            < nJ * (toFin i).1 + nJ := Nat.add_lt_add_left hltJ _
        _ = ((toFin i).1 + 1) * nJ := by ring
        _ ≤ nI * nJ := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (toFin i).2)
    map_eq_toFun := by
      funext j
      rw [← IndexType.fromFin_toFin (I := I × J) (i, j)]
      apply congrArg (fromFin (I := I × J))
      apply Fin.ext
      have hj := TensorIndexTypeOfRank.toFin_eq_offset (I := J) (n := nJ)
        (rank := jrank) (dims := jdims) (axis := jaxis) j
      calc
        ↑(toFin ((i, j) : I × J))
            = ↑(toFin j) + nJ * ↑(toFin i) := rfl
        _ = nJ * ↑(toFin i) + (TensorIndexType.toTensorIndex j).offset
              (TensorIndex.denseStridesForOrder jdims jaxis) := by
              rw [hj]
              rw [TensorIndexType.toTensorIndex]
              exact Nat.add_comm _ _ }

/-- Alias for embedding `I` into the right side of `J × I`. -/
def prodLeftSwap (I J : Type u)
    {nI nJ irank : Nat} {idims : Vector Nat irank}
    {iaxis : TensorIndex.AxisOrder irank}
    [TensorIndexType I nI irank idims iaxis] [IndexType J nJ]
    (j : J) : TensorSliceMap I (J × I) :=
  prodRight J I j

/-- Alias for embedding `J` into the left side of `J × I`. -/
def prodRightSwap (I J : Type u)
    {nI nJ jrank : Nat} {jdims : Vector Nat jrank}
    {jaxis : TensorIndex.AxisOrder jrank}
    [IndexType I nI] [TensorIndexType J nJ jrank jdims jaxis]
    (i : I) : TensorSliceMap J (J × I) :=
  prodLeft J I i

/-- Lift a slice map into the left factor of a product target. -/
def prodMapLeft {I I' J : Type u}
    {nI nI' nJ irank : Nat} {idims : Vector Nat irank}
    {iaxis : TensorIndex.AxisOrder irank}
    [TensorIndexType I nI irank idims iaxis] [IndexType I' nI'] [IndexType J nJ]
    (s : TensorSliceMap I I') (j : J) : TensorSliceMap I (I' × J) :=
  have hnJ : 0 < nJ := Nat.lt_of_le_of_lt (Nat.zero_le _) (toFin j).2
  { map := fun i => (s.map i, j)
    ioffset := nJ * s.ioffset + (toFin j).1
    istrides := TensorIndex.scaleStrides nJ s.istrides
    istrides_valid := TensorIndex.ValidStrides.scale hnJ s.istrides_valid
    in_bounds := by
      intro idx
      rw [TensorIndex.offset_scaleStrides]
      have hs := s.in_bounds idx
      calc
        nJ * s.ioffset + (toFin j).1 + nJ * idx.offset s.istrides
            = (toFin j).1 + nJ * (s.ioffset + idx.offset s.istrides) := by ring
        _ < nJ + nJ * (s.ioffset + idx.offset s.istrides) := by
          exact Nat.add_lt_add_right (toFin j).2 _
        _ = (s.ioffset + idx.offset s.istrides + 1) * nJ := by ring
        _ ≤ nI' * nJ := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hs)
    map_eq_toFun := by
      funext i
      rw [← IndexType.fromFin_toFin (I := I' × J) (s.map i, j)]
      apply congrArg (fromFin (I := I' × J))
      apply Fin.ext
      have hsmap := congrFun s.map_eq_specFun i
      have hfin := congrArg (fun x : I' => toFin x) hsmap
      have hoff : ↑(toFin (s.map i)) =
          s.ioffset + (TensorIndexType.toTensorIndex i).offset s.istrides := by
        simpa [specFun] using congrArg Fin.val hfin
      calc
        ↑(toFin ((s.map i, j) : I' × J))
            = ↑(toFin j) + nJ * ↑(toFin (s.map i)) := rfl
        _ = ↑(toFin j) +
              nJ * (s.ioffset + (TensorIndexType.toTensorIndex i).offset s.istrides) := by
              rw [hoff]
        _ = nJ * s.ioffset + ↑(toFin j) + (TensorIndexType.toTensorIndex i).offset
              (TensorIndex.scaleStrides nJ s.istrides) := by
              rw [TensorIndex.offset_scaleStrides]
              ring }

/-- Lift a slice map into the right factor of a product target. -/
def prodMapRight {I I' J : Type u}
    {nI nI' nJ irank : Nat} {idims : Vector Nat irank}
    {iaxis : TensorIndex.AxisOrder irank}
    [TensorIndexType I nI irank idims iaxis] [IndexType I' nI'] [IndexType J nJ]
    (j : J) (s : TensorSliceMap I I') : TensorSliceMap I (J × I') :=
  { map := fun i => (j, s.map i)
    ioffset := s.ioffset + nI' * (toFin j).1
    istrides := s.istrides
    istrides_valid := s.istrides_valid
    in_bounds := by
      intro idx
      have hs := s.in_bounds idx
      calc
        s.ioffset + nI' * (toFin j).1 + idx.offset s.istrides
            = (s.ioffset + idx.offset s.istrides) + nI' * (toFin j).1 := by ring
        _ < nI' + nI' * (toFin j).1 := Nat.add_lt_add_right hs _
        _ = ((toFin j).1 + 1) * nI' := by ring
        _ ≤ nJ * nI' := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (toFin j).2)
    map_eq_toFun := by
      funext i
      rw [← IndexType.fromFin_toFin (I := J × I') (j, s.map i)]
      apply congrArg (fromFin (I := J × I'))
      apply Fin.ext
      have hsmap := congrFun s.map_eq_specFun i
      have hfin := congrArg (fun x : I' => toFin x) hsmap
      have hoff : ↑(toFin (s.map i)) =
          s.ioffset + (TensorIndexType.toTensorIndex i).offset s.istrides := by
        simpa [specFun] using congrArg Fin.val hfin
      calc
        ↑(toFin ((j, s.map i) : J × I'))
            = ↑(toFin (s.map i)) + nI' * ↑(toFin j) := rfl
        _ = s.ioffset + (TensorIndexType.toTensorIndex i).offset s.istrides +
              nI' * ↑(toFin j) := by
              rw [hoff]
        _ = s.ioffset + nI' * ↑(toFin j) +
              (TensorIndexType.toTensorIndex i).offset s.istrides := by
              ring }

end TensorSliceMap








end NumLean
