module

public import Tests.CCompiler
public meta import Tests.CCompiler

@[expose] public section

open NumLean

namespace Tests.GaussianPivotEval

def a0 : FloatArray :=
  [0.0, 2.0,
   1.0, 3.0].toFloatArray

def b0 : FloatArray :=
  [4.0, 5.0].toFloatArray

/-- info: ([1.000000, 3.000000, 0.000000, 2.000000], [5.000000, 4.000000]) -/
#guard_msgs in
#eval Tests.CCompiler.gaussianElimPartialPivot 2 a0 b0

end Tests.GaussianPivotEval
