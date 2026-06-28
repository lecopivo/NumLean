module

public import NumLean.Experimental.Data.BTuple
import all NumLean.Experimental.Data.BTuple.Range
public meta import NumLean.Experimental.Data.BTuple.Range

@[expose] public section

namespace NumLean

namespace Tests

namespace BTupleFold

open BTuple

abbrev Sum2Profile := Profile.sum .leaf .leaf
abbrev MatrixProfile := Profile.prod Sum2Profile Sum2Profile

def loSum : Shape Sum2Profile := Shape.sum (.leaf 0) (.leaf 0)
def hiRows : Shape Sum2Profile := Shape.sum (.leaf 3) (.leaf 2)
def hiCols : Shape Sum2Profile := Shape.sum (.leaf 2) (.leaf 4)

/-- Shape `(3 + 2) × (2 + 4)`: rows are a direct sum of sizes `3` and `2`, columns are a
direct sum of sizes `2` and `4`, and the outer product is matrix-like. -/
def matrixShape : Shape MatrixProfile := Shape.prod hiRows hiCols

def matrixLo : Shape MatrixProfile := Shape.prod loSum loSum

/-- Encode an index as `(rowTag, rowIndex, colTag, colIndex, linearIndex)`.

Tags are `0` for the left summand and `1` for the right summand. -/
def describeIndex (idx : BTuple Nat MatrixProfile) : Nat × Nat × Nat × Nat × Nat :=
  match idx with
  | .prod (.sumLeft (.leaf row) _) (.sumLeft (.leaf col) _) =>
      (0, row, 0, col, Range.linearIndex matrixLo matrixShape idx)
  | .prod (.sumLeft (.leaf row) _) (.sumRight _ (.leaf col)) =>
      (0, row, 1, col, Range.linearIndex matrixLo matrixShape idx)
  | .prod (.sumRight _ (.leaf row)) (.sumLeft (.leaf col) _) =>
      (1, row, 0, col, Range.linearIndex matrixLo matrixShape idx)
  | .prod (.sumRight _ (.leaf row)) (.sumRight _ (.leaf col)) =>
      (1, row, 1, col, Range.linearIndex matrixLo matrixShape idx)

def foldedMatrixEntries : Array (Nat × Nat × Nat × Nat × Nat) :=
  Fold.fold (matrixLo...matrixShape : Std.Rco (Shape MatrixProfile)) #[] fun idx _ acc =>
    acc.push (describeIndex idx)

example : foldedMatrixEntries.size = 30 := by
  native_decide

example :
    foldedMatrixEntries = #[
      (0, 0, 0, 0, 0), (0, 0, 0, 1, 1), (0, 0, 1, 0, 2),
      (0, 0, 1, 1, 3), (0, 0, 1, 2, 4), (0, 0, 1, 3, 5),
      (0, 1, 0, 0, 6), (0, 1, 0, 1, 7), (0, 1, 1, 0, 8),
      (0, 1, 1, 1, 9), (0, 1, 1, 2, 10), (0, 1, 1, 3, 11),
      (0, 2, 0, 0, 12), (0, 2, 0, 1, 13), (0, 2, 1, 0, 14),
      (0, 2, 1, 1, 15), (0, 2, 1, 2, 16), (0, 2, 1, 3, 17),
      (1, 0, 0, 0, 18), (1, 0, 0, 1, 19), (1, 0, 1, 0, 20),
      (1, 0, 1, 1, 21), (1, 0, 1, 2, 22), (1, 0, 1, 3, 23),
      (1, 1, 0, 0, 24), (1, 1, 0, 1, 25), (1, 1, 1, 0, 26),
      (1, 1, 1, 1, 27), (1, 1, 1, 2, 28), (1, 1, 1, 3, 29)] := by
  native_decide

end BTupleFold

end Tests

end NumLean
