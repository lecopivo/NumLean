import NumLean.Meta.ForAll
import NumLean.Data.FinHTuple.FinHTupleMap

set_option backward.do.legacy false

open NumLean

namespace Tests.ForAllNotation

def sum2 : Nat := Id.run do
  let shape := h((2:Nat), 3)
  let mut acc := 0
  for_all h(i, j) in 0...shape do
    acc := acc + i * 10 + j
  return acc

example : sum2 = 36 := by native_decide

def sum2WithProof : Nat := Id.run do
  let shape := h((2:Nat), 3)
  let mut acc := 0
  for_all hmem : h(i, j) in 0...shape do
    have _hmem := hmem
    acc := acc + i * 10 + j
  return acc

example : sum2WithProof = 36 := by native_decide

def sum2TwoAcc : Nat × Nat := Id.run do
  let shape := h((2:Nat), 3)
  let mut sum : Nat := 0
  let mut count : Nat := 0
  for_all h(i, j) in 0...shape do
    sum := sum + i * 10 + j
    count := count + 1
  return (sum, count)

example : sum2TwoAcc = (36, 6) := by native_decide

def sumMapIndexWithoutNamedProof : Nat := Id.run do
  let shape := h((2:Nat), 3)
  let idxMap := FinHTupleMap.id shape
  let mut acc := 0
  for_all i in 0...shape do
    let idx := idxMap i
    acc := acc + idx.rowMajorIndex shape
  return acc

example : sumMapIndexWithoutNamedProof = 15 := by native_decide

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

def sumUInt64Fast : Nat := Id.run do
  let mut acc := 0
  for_all_fast _h : i in ((0 : UInt64)...(4 : UInt64)) do
    acc := acc + i.toNat
  return acc

example : sumUInt64Fast = 6 := by native_decide

def sumContinue : Nat := Id.run do
  let mut acc := 0
  for_all i in (0 : Nat)...5 do
    acc := acc + 1
    if i % 2 = 0 then
      continue
    acc := acc + 10
  return acc

example : sumContinue = 25 := by native_decide

def sumContinueTwoAcc : Nat × Nat := Id.run do
  let mut sum : Nat := 0
  let mut count : Nat := 0
  for_all i in (0 : Nat)...5 do
    if i % 2 = 0 then
      continue
    sum := sum + i
    count := count + 1
  return (sum, count)

example : sumContinueTwoAcc = (4, 2) := by native_decide

def sumContinueFast : Nat := Id.run do
  let mut acc := 0
  for_all_fast i in (0 : Nat)...5 do
    if i % 2 = 0 then
      continue
    acc := acc + i
  return acc

example : sumContinueFast = 4 := by native_decide

def sumInt : Int := Id.run do
  let mut acc := 0
  for_all _h : i in ((-2 : Int)...(3 : Int)) do
    acc := acc + i
  return acc

example : sumInt = 0 := by native_decide

/--
info: (let acc := 0;
  do
  let __s ←
    Fold.fold (0...3) acc fun i __h __s =>
        (let acc := __s;
          let acc := acc + i;
          pure acc).run
  let acc : ℕ := __s
  pure acc).run : ℕ
-/
#guard_msgs in
#check Id.run do
  let mut acc := 0
  for_all i in (0 : Nat)...3 do
    acc := acc + i
  return acc

/--
info: (let acc := 0;
  do
  let __s ←
    Fold.fold (0...2) acc fun i __h __s =>
        (let acc := __s;
          do
          let __s ←
            Fold.fold (0...3) acc fun j __h __s =>
                (let acc := __s;
                  let acc := acc + i + j;
                  pure acc).run
          let acc : ℕ := __s
          pure acc).run
  let acc : ℕ := __s
  pure acc).run : ℕ
-/
#guard_msgs in
#check Id.run do
  let mut acc := 0
  for_all i in (0 : Nat)...2 do
    for_all j in (0 : Nat)...3 do
      acc := acc + i + j
  return acc

/--
info: (let sum := 0;
  let count := 0;
  do
  let __s ←
    Fold.fold (0...3) ⟨sum, count⟩ fun i __h __s =>
        (let sum := __s.fst;
          let __s := __s.snd;
          let count := __s;
          let sum := sum + i;
          let count := count + 1;
          pure ⟨sum, count⟩).run
  let sum : ℕ := __s.fst
  let __s : ℕ := __s.snd
  let count : ℕ := __s
  pure (sum, count)).run : ℕ × ℕ
-/
#guard_msgs in
#check Id.run do
  let mut sum := 0
  let mut count := 0
  for_all i in (0 : Nat)...3 do
    sum := sum + i
    count := count + 1
  return (sum, count)

/--
info: (let sum := 0;
  let count := 0;
  do
  let __s ←
    Fold.fold (0...2) ⟨sum, count⟩ fun i __h __s =>
        (let sum := __s.fst;
          let __s := __s.snd;
          let count := __s;
          do
          let __s ←
            Fold.fold (0...3) ⟨sum, count⟩ fun j __h __s =>
                (let sum := __s.fst;
                  let __s := __s.snd;
                  let count := __s;
                  let sum := sum + i + j;
                  let count := count + 1;
                  pure ⟨sum, count⟩).run
          let sum : ℕ := __s.fst
          let __s : ℕ := __s.snd
          let count : ℕ := __s
          pure ⟨sum, count⟩).run
  let sum : ℕ := __s.fst
  let __s : ℕ := __s.snd
  let count : ℕ := __s
  pure (sum, count)).run : ℕ × ℕ
-/
#guard_msgs in
#check Id.run do
  let mut sum := 0
  let mut count := 0
  for_all i in (0 : Nat)...2 do
    for_all j in (0 : Nat)...3 do
      sum := sum + i + j
      count := count + 1
  return (sum, count)

namespace NestedInstanceCheck

example :
    NumLean.Meta.ForAll.ForAllIn' (Std.Rco Nat) Nat Nat inferInstance :=
  inferInstance

example :
    NumLean.Fold (Std.Rco Nat) Nat inferInstance := by
  infer_instance

example :
    NumLean.Fold (Std.Rco UInt64) UInt64 inferInstance := by
  infer_instance

example :
    NumLean.Fold (Std.Rco Int) Int inferInstance := by
  infer_instance

example :
    NumLean.LawfulFold (Std.Rco Nat) Nat inferInstance := by
  infer_instance

example :
    NumLean.LawfulFold (Std.Rco Int) Int inferInstance := by
  infer_instance

example :
    NumLean.LawfulFold (Std.Rco UInt64) UInt64 inferInstance := by
  infer_instance

example {α : Type} [LE α] [LT α] [DecidableLT α]
    [NumLean.RcoNativeStep α]
    [NumLean.LawfulRcoNativeStep α] :
    NumLean.LawfulFold (Std.Rco α) α inferInstance := by
  infer_instance

example :
    NumLean.Fold
      (Std.Rco (HTuple Nat (.prod .leaf .leaf)))
      (HTuple Nat (.prod .leaf .leaf)) HTuple.Range.instMembershipRcoHTuple := by
  infer_instance

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
