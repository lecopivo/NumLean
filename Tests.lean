import Tests.BTupleFold
import Tests.AlgebraDeriving
import Tests.CCompiler
import Tests.CCompilerIRSemantics
import Tests.DyadicInterval
import Tests.ExternIn
import Tests.Float32ArrayEval
import Tests.FoldEmbedding
import Tests.ForAllNotation
import Tests.GaussianPivotEval
import Tests.HTupleCoercions
import Tests.HTupleGetElemTactic
import Tests.HTupleProfileRefines
import Tests.HTupleRangeIterators
import Tests.HVector
import Tests.HasFlatReprDeriving
import Tests.OrderInstances
import Tests.ScalarArrays
import Tests.TBounds
import Tests.TupleOrderNotation
import Tests.TypeclassPerformance
import Tests.VectorRangeIterators
import Tests.Visualize

def main : IO Unit := do
  IO.println "tests done!"
