import NumLean.Data.TensorIndex.FinTIndexIterator

open NumLean TensorIndex

namespace Tests.TensorIndexIteratorCompiler

set_option trace.Compiler.result true

abbrev Rank1Shape : Shape .leaf :=
  .leaf 8

abbrev Rank2Shape : Shape (.prod .leaf .leaf) :=
  .prod (.leaf 4) (.leaf 5)

abbrev Rank3Shape : Shape (.prod (.prod .leaf .leaf) .leaf) :=
  .prod (.prod (.leaf 2) (.leaf 3)) (.leaf 4)

abbrev NestedShape : Shape (.prod (.prod .leaf .leaf) (.prod .leaf .leaf)) :=
  .prod (.prod (.leaf 2) (.leaf 2)) (.prod (.leaf 2) (.leaf 2))

@[inline] def refRank1Sum : Nat := Id.run do
  let mut acc := 0
  for i in [0:8] do
    acc := acc + i
  return acc

@[inline] def iterRank1Sum : Nat := Id.run do
  let mut acc := 0
  for item in FinTIndex.rowMajorFinIter Rank1Shape do
    acc := acc + item.linearIdx.1
  return acc

@[inline] def refRank2Sum : Nat := Id.run do
  let mut acc := 0
  let mut lin := 0
  for _i in [0:4] do
    for _j in [0:5] do
      acc := acc + lin
      lin := lin + 1
  return acc

@[inline] def iterRank2Sum : Nat := Id.run do
  let mut acc := 0
  for item in FinTIndex.rowMajorFinIter Rank2Shape do
    acc := acc + item.linearIdx.1
  return acc

@[inline] def refRank3Sum : Nat := Id.run do
  let mut acc := 0
  let mut lin := 0
  for _i in [0:2] do
    for _j in [0:3] do
      for _k in [0:4] do
        acc := acc + lin
        lin := lin + 1
  return acc

@[inline] def iterRank3Sum : Nat := Id.run do
  let mut acc := 0
  for item in FinTIndex.rowMajorFinIter Rank3Shape do
    acc := acc + item.linearIdx.1
  return acc

@[inline] def refNestedSum : Nat := Id.run do
  let mut acc := 0
  let mut lin := 0
  for _i in [0:2] do
    for _j in [0:2] do
      for _k in [0:2] do
        for _l in [0:2] do
          acc := acc + lin
          lin := lin + 1
  return acc

@[inline] def iterNestedSum : Nat := Id.run do
  let mut acc := 0
  for item in FinTIndex.rowMajorFinIter NestedShape do
    acc := acc + item.linearIdx.1
  return acc

example : iterRank1Sum = refRank1Sum := by native_decide
example : iterRank2Sum = refRank2Sum := by native_decide
example : iterRank3Sum = refRank3Sum := by native_decide
example : iterNestedSum = refNestedSum := by native_decide

#eval! iterRank1Sum
#eval! iterRank2Sum
#eval! iterRank3Sum
#eval! iterNestedSum

end Tests.TensorIndexIteratorCompiler
