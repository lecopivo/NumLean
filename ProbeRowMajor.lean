import Tests.FloatArrayTensorBenchmark

open NumLean TensorIndex

namespace ProbeRowMajor

def count2 (n : Nat) : Nat := Id.run do
  let shape : Shape (.prod .leaf .leaf) := .prod (.leaf n) (.leaf n)
  let mut acc := 0
  for (_linear, _idx) in FinTIndex.rowMajorIter shape do
    acc := acc + 1
  return acc

def count3 (d0 d1 d2 : Nat) : Nat := Id.run do
  let shape : Shape (.prod (.prod .leaf .leaf) .leaf) :=
    .prod (.prod (.leaf d0) (.leaf d1)) (.leaf d2)
  let mut acc := 0
  for (_linear, _idx) in FinTIndex.rowMajorIter shape do
    acc := acc + 1
  return acc

#eval! count2 4
#eval! count2 192
#eval! count3 4 3 2
#eval! count3 96 64 32

end ProbeRowMajor
