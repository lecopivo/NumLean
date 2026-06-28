module

public import Tests.AlgebraDeriving
public import Tests.BTupleFold
public import Tests.CCompiler
public import Tests.CCompilerIRSemantics
public import Tests.DyadicInterval
public import Tests.ExternIn
public import Tests.FlatVectorNotation
public import Tests.Float32ArrayEval
public import Tests.FloatTensor
public import Tests.FoldEmbedding
public import Tests.ForAllNotation
public import Tests.GaussianPivotEval
public import Tests.HTupleCoercions
public import Tests.HTupleGetElemTactic
public import Tests.HTupleProfileRefines
public import Tests.HTupleRangeIterators
public import Tests.HVector
public import Tests.HasFlatReprDeriving
public import Tests.HierarchyGraph
public import Tests.OrderInstances
public import Tests.ScalarArrays
public import Tests.TBounds
public import Tests.TupleOrderNotation
public import Tests.TypeclassPerformance
public import Tests.VectorRangeIterators
public import Tests.Visualize

@[expose] public section

def main : IO Unit := do
  IO.println "tests done!"
