import NumLean.Data.HTuple.Order
import NumLean.Experimental.Data.HList.Ops

open NumLean
open NumLean.HList

namespace Tests.TupleOrderNotation

open NumLean

example : (HTuple.leaf 0 : HTuple Nat .leaf) <ˡ HTuple.leaf 1 := by
  sorry

example : (HTuple.leaf 0 : HTuple Nat .leaf) ≤ˡ HTuple.leaf 0 := by
  left
  rfl

example : (HTuple.prod (HTuple.leaf 0) (HTuple.leaf 1) : HTuple Nat (HTuple.Profile.prod .leaf .leaf)) <ₗ
    HTuple.prod (HTuple.leaf 0) (HTuple.leaf 2) := by
  sorry

example : (HTuple.prod (HTuple.leaf 0) (HTuple.leaf 1) : HTuple Nat (HTuple.Profile.prod .leaf .leaf)) ≤ₗ
    HTuple.prod (HTuple.leaf 0) (HTuple.leaf 1) := by
  left
  rfl

example : (HTuple.prod (HTuple.leaf 0) (HTuple.leaf 1) : HTuple Nat (HTuple.Profile.prod .leaf .leaf)) <ₑ
    HTuple.prod (HTuple.leaf 1) (HTuple.leaf 2) := by
  sorry

example : (HTuple.prod (HTuple.leaf 0) (HTuple.leaf 1) : HTuple Nat (HTuple.Profile.prod .leaf .leaf)) ≤ₑ
    HTuple.prod (HTuple.leaf 0) (HTuple.leaf 2) := by
  sorry

example : (hl(0, 1) : HPTuple Nat hlp(•, •)) <ˡ hl(0, 2) := by
  sorry

example : (hl(0, 1) : HPTuple Nat hlp(•, •)) ≤ˡ hl(0, 1) := by
  left
  rfl

example : (hl(0, 1) : HPTuple Nat hlp(•, •)) <ₗ hl(0, 2) := by
  sorry

example : (hl(0, 1) : HPTuple Nat hlp(•, •)) ≤ₗ hl(0, 1) := by
  left
  rfl

example : (hl(0, 1) : HPTuple Nat hlp(•, •)) <ₑ hl(1, 2) := by
  show NumLean.List.elementwiseLT ((hl(0, 1) : HPTuple Nat hlp(•, •)).toList) ((hl(1, 2) : HPTuple Nat hlp(•, •)).toList)
  simpa using (NumLean.List.elementwiseLT.cons (by decide) (NumLean.List.elementwiseLT.cons (by decide) NumLean.List.elementwiseLT.nil) :
    NumLean.List.elementwiseLT [0, 1] [1, 2])

example : (hl(0, 1) : HPTuple Nat hlp(•, •)) ≤ₑ hl(0, 2) := by
  show NumLean.List.elementwiseLE ((hl(0, 1) : HPTuple Nat hlp(•, •)).toList) ((hl(0, 2) : HPTuple Nat hlp(•, •)).toList)
  simpa using (NumLean.List.elementwiseLE.cons (by decide) (NumLean.List.elementwiseLE.cons (by decide) NumLean.List.elementwiseLE.nil) :
    NumLean.List.elementwiseLE [0, 1] [0, 2])

end Tests.TupleOrderNotation
