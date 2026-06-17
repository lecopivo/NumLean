import NumLean.Meta.ForAll

set_option backward.do.legacy false

open NumLean TensorIndex

namespace Tests.ForAllNotation

def sum2 : Nat := Id.run do
  let shape : Shape _ := h(2, 3)
  let mut acc := 0
  for_all h(i, j) in 0...shape do
    acc := acc + i * 10 + j
  return acc

example : sum2 = 36 := by native_decide

def sum2WithProof : Nat := Id.run do
  let shape : Shape _ := h(2, 3)
  let mut acc := 0
  for_all hmem : h(i, j) in 0...shape do
    have _hmem := hmem
    acc := acc + i * 10 + j
  return acc

example : sum2WithProof = 36 := by native_decide

def sum2TwoAcc : Nat × Nat := Id.run do
  let shape : Shape _ := h(2, 3)
  let mut sum : Nat := 0
  let mut count : Nat := 0
  for_all h(i, j) in 0...shape do
    sum := sum + i * 10 + j
    count := count + 1
  return (sum, count)

example : sum2TwoAcc = (36, 6) := by native_decide

def sumUInt64 : Nat := Id.run do
  let mut acc := 0
  for_all _h : i in ((0 : UInt64)...(4 : UInt64)) do
    acc := acc + i.toNat
  return acc

example : sumUInt64 = 6 := by native_decide

def sumUInt64TwoAcc : Nat × Nat := Id.run do
  let mut sum : Nat := 0
  let mut count : Nat := 0
  for_all _h : i in ((0 : UInt64)...(4 : UInt64)) do
    sum := sum + i.toNat
    count := count + 1
  return (sum, count)

example : sumUInt64TwoAcc = (6, 4) := by native_decide

namespace NestedInstanceCheck

example :
    NumLean.Meta.ForAll.ForAllIn' (Std.Rco Nat) Nat Nat inferInstance :=
  inferInstance

example :
    NumLean.Meta.ForAll.ForAllIn' (Std.Rco Nat) Nat
      (MProd Nat (MProd Nat (MProd Nat Nat))) inferInstance := by
  infer_instance

example :
    NumLean.Meta.ForAll.LawfulForAllIn' (Std.Rco Nat) Nat
      (MProd Nat (MProd Nat (MProd Nat Nat))) inferInstance := by
  infer_instance

example :
    NumLean.Meta.ForAll.LawfulForAllIn'
      (Std.Rco (HTuple Nat (.prod .leaf .leaf)))
      (HTuple Nat (.prod .leaf .leaf)) (MProd Nat Nat) inferInstance := by
  infer_instance

example :
    NumLean.Meta.ForAll.ForAllIn' (Std.Rco UInt64) UInt64
      (MProd Nat Nat) inferInstance := by
  infer_instance

example :
    NumLean.Meta.ForAll.LawfulForAllIn' (Std.Rco UInt64) UInt64
      (MProd Nat Nat) inferInstance := by
  infer_instance

end NestedInstanceCheck

end Tests.ForAllNotation
