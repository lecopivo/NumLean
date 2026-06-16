import NumLean.Data.TensorIndex.FinTIndexLoop
import NumLean.Data.TensorIndex.TensorIndexType
import Init.Data.Iterators.Lemmas.Consumers.Loop

namespace NumLean

namespace TensorIndex

namespace FinTIndex

open Std Std.Iterators Std.Iterators.Types
open scoped BigOperators


def mkIndices {r} (shape : Shape r) : Array (FinTIndex shape) := Id.run do
  let mut a : Array (FinTIndex shape) := #[]
  for h : (_linear, i) in rowMajorIter shape do
    a := a.push { val := i, isLt := h.idx_inBounds }
  return a

theorem mkIndices_size {r : HRank} (shape : Shape r) :
    (mkIndices shape).size = shape.size := by
  sorry

def tensorMap {α r} (shape : Shape r) (data : Vector α shape.size) (f : FinTIndex shape → α → α) := Id.run do
  let mut data := data
  for h : (_linear, i) in rowMajorIter shape do
    let idx : FinTIndex shape := { val := i, isLt := h.idx_inBounds }
    data := data.set (toFin idx) (f idx data[toFin idx])
  return data

theorem tensorMap_eq_map (shape : Shape r) (data : Vector α shape.size) (f : FinTIndex shape → α → α) :
    tensorMap shape data f = data.mapFinIdx (fun i x h => f (fromFin ⟨i,h⟩) x) := by
  sorry


end FinTIndex

end TensorIndex

end NumLean
