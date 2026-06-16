import NumLean.Data.TensorIndex.FinTIndex
import NumLean.Data.TensorIndex.IntFinTIndex
import NumLean.Data.TensorIndex.TensorIndexType
import Init.Data.Nat.Lemmas
import Std.Data.Iterators.Consumers

namespace NumLean

namespace TensorIndex

namespace FinTIndex

open Std Std.Iterators Std.Iterators.Types

namespace RowMajor

/-- Validity facts for a raw row-major iterator output.

The iterator itself yields only a flat natural index and raw structured coordinates.  This predicate
packages the bounds proofs and the coherence proof connecting the raw coordinates to the flat index.
-/
structure Valid {p : HRank} (shape : Shape p) (out : Nat × TIndex Nat p) : Prop where
  linear_lt : out.1 < shape.size
  idx_inBounds : TIndex.InBounds shape out.2
  toFin_eq :
    IndexType.toFin ({ val := out.2, isLt := idx_inBounds } : FinTIndex shape) =
      ⟨out.1, linear_lt⟩

end RowMajor

/-- Compatibility wrapper used by the standalone row-major fold API. -/
structure RowMajorItem {p : HRank} (shape : Shape p) where
  linearIdx : Fin shape.size
  idx : FinTIndex shape
  toFin_eq : IndexType.toFin idx = linearIdx

/-- Internal state for row-major tensor-index iteration. -/
@[unbox]
structure RowMajorIterator {p : HRank} (shape : Shape p) where
  pos : Nat

namespace RowMajorIterator

variable {p : HRank} {shape : Shape p}

@[always_inline, inline]
instance instIterator : Iterator (RowMajorIterator shape) Id (Nat × TIndex Nat p) where
  IsPlausibleStep it
    | .yield it' out =>
        RowMajor.Valid shape out ∧ out.1 = it.internalState.pos ∧
          it'.internalState.pos = it.internalState.pos + 1
    | .skip _ => False
    | .done => it.internalState.pos ≥ shape.size
  step it :=
    pure <| .deflate <|
      if h : it.internalState.pos < shape.size then
        let linearIdx : Fin shape.size := ⟨it.internalState.pos, h⟩
        let idx : FinTIndex shape := IndexType.fromFin linearIdx
        let out : Nat × TIndex Nat p := (it.internalState.pos, idx.val)
        let valid : RowMajor.Valid shape out :=
          { linear_lt := h
            idx_inBounds := idx.isLt
            toFin_eq := by
              change IndexType.toFin idx = linearIdx
              exact IndexType.toFin_fromFin linearIdx }
        .yield ⟨⟨it.internalState.pos + 1⟩⟩ out ⟨valid, rfl, rfl⟩
      else
        .done (Nat.not_lt.mp h)

private def instFinitenessRelation : FinitenessRelation (RowMajorIterator shape) Id where
  Rel := InvImage WellFoundedRelation.rel (fun it => shape.size - it.internalState.pos)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, hsucc, hplausible⟩ := h
    cases step with
    | yield itNext out =>
        cases hsucc
        rcases hplausible with ⟨hvalid, hout, hpos⟩
        have hlt : it.internalState.pos < shape.size := by
          simpa [hout] using hvalid.linear_lt
        rw [hpos]
        omega
    | skip itNext =>
        cases hplausible
    | done =>
        cases hsucc

instance instFinite : Finite (RowMajorIterator shape) Id := by
  exact Finite.of_finitenessRelation instFinitenessRelation

theorem valid_of_isPlausibleIndirectOutput
    {it : Iter (α := RowMajorIterator shape) (Nat × TIndex Nat p)} {out : Nat × TIndex Nat p}
    (h : it.IsPlausibleIndirectOutput out) : RowMajor.Valid shape out := by
  induction h with
  | direct hdirect =>
      rcases hdirect with ⟨it', hstep⟩
      exact hstep.1
  | indirect _ _ ih =>
      exact ih

end RowMajorIterator

/-- Row-major iterator over raw tensor coordinates.

The iterator yields `(linearIdx, idx)`, where `linearIdx` is a flat natural offset and `idx` is the
matching raw structured coordinate.  In proof-aware `for h : (linearIdx, idx) in ... do` syntax,
`h` is `RowMajor.Valid shape (linearIdx, idx)`.
-/
@[always_inline, inline]
def rowMajorIter {p : HRank} (shape : Shape p) :
    Iter (α := RowMajorIterator shape) (Nat × TIndex Nat p) :=
  ⟨⟨0⟩⟩

instance instMembershipRowMajorIter {p : HRank} {shape : Shape p} :
    Membership (Nat × TIndex Nat p) (Iter (α := RowMajorIterator shape) (Nat × TIndex Nat p)) where
  mem _ out := RowMajor.Valid shape out

theorem rowMajorIter_valid_of_mem {p : HRank} {shape : Shape p} {out : Nat × TIndex Nat p}
    (h : out ∈ rowMajorIter shape) : RowMajor.Valid shape out :=
  h

end FinTIndex

end TensorIndex

end NumLean
