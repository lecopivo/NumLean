module

public import NumLean.Data.HTuple.RangeIterator
public meta import NumLean.Data.HTuple.Basic
public meta import NumLean.Data.HTuple.RangeIterator

@[expose] public section

open NumLean

namespace Tests.HTupleRangeIterators

abbrev Rank2 := HTuple.Profile.prod .leaf .leaf

def coords2D (lo hi : HTuple Nat Rank2) : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  for idx in lo...hi do
    match idx with
    | h(i, j) => out := out.push (i, j)
  return out

def enum2D (lo hi : HTuple Nat Rank2) : Array (Nat × Nat × Nat) := Id.run do
  let mut out := #[]
  for (lin, idx) in (lo...hi).enum do
    match idx with
    | h(i, j) => out := out.push (lin, i, j)
  return out

example :
    coords2D h(1, 2) h(3, 5) = #[(1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4)] := by
  native_decide

example :
    enum2D h(1, 2) h(3, 5) = #[(0, 1, 2), (1, 1, 3), (2, 1, 4), (3, 2, 2), (4, 2, 3), (5, 2, 4)] := by
  native_decide

def a := 0...1
def b := h(0)
def c := h(0)...h(3)
def d := h(0,0)...h(3,5)

example :
    Id.run (do
      let mut ok := true
      for hmem : h(i,j) in 0...h((2:Nat), 3) do
        ok := ok && (i < 2) && (j < 3)
      return ok) = true := by
  native_decide

example :
    Id.run (do
      let mut ok := true
      for _hmem : h(i,j) in h((-1:ℤ),2)...h(2, 5) do
        ok := ok && (-1 ≤ i ∧ i < 2) && (2 ≤ j ∧ j < 5)
      return ok) = true := by
  native_decide

example : (HTuple.Range.toList (0 : HTuple Nat Rank2) h(2, 3)).length = 6 := by
  native_decide


end Tests.HTupleRangeIterators
