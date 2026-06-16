import Std.Data.Iterators.Producers.Range
import Std.Data.Iterators.Consumers
import NumLean.Data.TensorIndex.FinTIndexLoop

open NumLean TensorIndex

namespace Tests

abbrev MatrixShape (rows cols : Nat) : Shape (.prod .leaf .leaf) :=
  HTuple.prod (HTuple.leaf rows) (HTuple.leaf cols)

def matrixCoord (idx : TIndex Nat (.prod .leaf .leaf)) : Nat × Nat :=
  match idx with
  | .prod (.leaf row) (.leaf col) => (row, col)

/-- Coordinates visited by nested Std range iterators over a rectangular matrix tile.

This exercises the `Std.Rco.iter` range API directly: `(lo...hi).iter` streams the half-open range
`[lo, hi)` without constructing an intermediate collection. -/
def matrixTileCoordsByRanges (rowLo rowHi colLo colHi : Nat) : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  for row in (rowLo...rowHi).iter do
    for col in (colLo...colHi).iter do
      out := out.push (row, col)
  return out

/-- Coordinates in a rectangular tile, selected while streaming all matrix indices with `FinTIndex`.

The range API defines the tile bounds; `FinTIndex.rowMajorIter` supplies the matrix index stream. -/
def matrixTileCoordsByFinTIndex (rows cols rowLo rowHi colLo colHi : Nat) : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  for (_linear, idx) in FinTIndex.rowMajorIter (MatrixShape rows cols) do
    let (row, col) := matrixCoord idx
    if rowLo ≤ row ∧ row < rowHi ∧ colLo ≤ col ∧ col < colHi then
      out := out.push (row, col)
  return out

/-- Sum a matrix tile while streaming matrix indices with `FinTIndex`. -/
def matrixTileSumByFinTIndex (matrix : Nat → Nat → Nat)
    (rows cols rowLo rowHi colLo colHi : Nat) : Nat := Id.run do
  let mut acc := 0
  for (_linear, idx) in FinTIndex.rowMajorIter (MatrixShape rows cols) do
    let (row, col) := matrixCoord idx
    if rowLo ≤ row ∧ row < rowHi ∧ colLo ≤ col ∧ col < colHi then
      acc := acc + matrix row col
  return acc

def sampleMatrix (row col : Nat) : Nat :=
  10 * row + col

example :
    matrixTileCoordsByRanges 1 3 2 5 = #[(1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4)] := by
  native_decide

example :
    matrixTileCoordsByFinTIndex 4 5 1 3 2 5 = matrixTileCoordsByRanges 1 3 2 5 := by
  native_decide

example : matrixTileSumByFinTIndex sampleMatrix 4 5 1 3 2 5 = 108 := by
  native_decide

example : matrixTileCoordsByFinTIndex 4 5 0 4 1 1 = #[] := by
  native_decide

example : matrixTileSumByFinTIndex sampleMatrix 4 5 2 2 0 4 = 0 := by
  native_decide

example :
    Id.run (do
      let mut ok := true
      for h : (linearIdx, idx) in FinTIndex.rowMajorIter (MatrixShape 2 3) do
        let finIdx : FinTIndex (MatrixShape 2 3) := { val := idx, isLt := h.idx_inBounds }
        ok := ok && ((IndexType.toFin finIdx).1 == linearIdx)
      return ok) = true := by
  native_decide

end Tests
