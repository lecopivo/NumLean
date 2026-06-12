import NumLean.Data.Vector

namespace NumLean

variable (X : Type u)


-- structure Subvector (X : Type u) {I J} (ι : J → I)
--     {nI nJ} [IndexType I nI] [IndexType J nJ]
--     {Ks : Type v} {K : Type w} [ScalarArray Ks K] [ScalarType X Ks]
--   where
--   data : Vector X I

-- variable
--   {X : Type u} {I J} {ι : J → I}
--   {nI nJ} [IndexType I nI] [IndexType J nJ]
--   {Ks : Type v} {K : Type w} [ScalarArray Ks K] [ScalarType X Ks]

-- instance : GetElem (Subvector X ι) J X (fun _ _ => True) where
--   getElem xs j _ := xs.data[ι j]




structure Slice (J I : Type _) {nI} [Size I nI] where
  (count off inc : Nat)
  inbounds : (off + inc * (count - 1)) ≤ nI
  nontrivial : inc ≠ 0

instance {I nI} [IndexType I nI] {J nJ} [IndexType J nJ] :
    CoeFun (Slice J I) (fun _ => J → I) where
  coe s := fun j =>
    let jdx := toIdx j
    let idx : Idx nI := ⟨s.off.toUInt64 + s.inc.toUInt64 * jdx.val, sorry⟩
    fromIdx idx


end NumLean
