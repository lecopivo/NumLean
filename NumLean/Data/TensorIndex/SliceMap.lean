import NumLean.Data.TensorIndex.Basic
import NumLean.Interfaces.IndexType


namespace NumLean

/-- `I` is tensor index type of given rank `rank` -/
class TensorIndexTypeOfRank (I : Type u) (n : outParam Nat)
    (rank : Nat) (dims : outParam (Vector Nat rank))
    (axis : outParam (TensorIndex.AxisOrder rank))
  extends IndexType I n
  where

  -- nI_numelem : nI = TensorIndex.
  toTensorIndex : I → TensorIndex dims
  fromTensorIndex : TensorIndex dims → I

  offset_toTensorIndex_toFin (i : I) :
    (toTensorIndex i).offset (TensorIndex.denseStridesForOrder dims axis)
    =
    (toFin i).1

  fromTensorIndex_fromFin_offset (idx : TensorIndex dims) :
    fromTensorIndex idx
    =
    fromFin ⟨idx.offset (TensorIndex.denseStridesForOrder dims axis), sorry⟩


/-- `I` is tensor index type of canonical rank `rank`. -/
class TensorIndexType (I : Type u) (n : outParam Nat)
    (rank : outParam Nat) (dims : outParam (Vector Nat rank))
    (axis : outParam (TensorIndex.AxisOrder rank))
  extends TensorIndexTypeOfRank I n rank dims axis


-- this does not fix any particular linear order but guarantees injectivity
structure TensorSliceMap (J I : Type u) {nJ nI} [IndexType J nJ] [IndexType I nI] where
  /-- Efficient map from `J` to `I`. It is fully determined by `istrides` but
  its computation might be too slow. -/
  map : J → I

  jrank : Nat
  jdims : Vector Nat jrank
  -- these should be dense strides!
  jstrides : Vector Nat jrank

  -- `istrides` is *the* main data defining the `TensorSliceMap`!!!
  -- strides to accest I
  -- we need to make sure that we generate valid `Fin nI` with offset map
  istrides : Vector Nat jrank

  -- strides need to be valid to faithfully embedd `J` in `I`
  istrides_valid : TensorIndex.ValidStrides jdims istrides

  --
  map_valid :
    let indexMap := fun j : J =>
      let ji : Fin nJ := toFin j
      -- recover from linear index `ji`
      let jt : TensorIndex jdims := sorry
      -- reintepred J's tensor index under I's strides
      let ii : Fin nI := ⟨jt.offset istrides, sorry⟩
      fromFin ii
    indexMap = map








end NumLean
