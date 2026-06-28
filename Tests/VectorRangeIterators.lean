module

public import NumLean.Data.Vector
public meta import NumLean.Data.Vector.RangeIterator

@[expose] public section

open NumLean

namespace Tests.VectorRangeIterators

def v0 : Vector Nat 3 := Vector.ofFn fun _ => 0
def v2 : Vector Nat 3 := Vector.ofFn fun _ => 2

example : (Id.run do
    let mut acc := []
    for i in v0...v2 do
      acc := i.toList :: acc
    pure acc.reverse).length = 8 := by
  native_decide

example : (Id.run do
    let mut acc := []
    for out in (v0...v2).enum do
      acc := (out.1, out.2.toList) :: acc
    pure acc.reverse).length = 8 := by
  native_decide

example : (Vector.ofFn (fun _ : Fin 3 => 0) : Vector Nat 3) ≤ₑ Vector.ofFn (fun _ : Fin 3 => 1) := by
  intro i
  simp

example : (Vector.ofFn (fun _ : Fin 2 => 0) : Vector Nat 2) <ₑ Vector.ofFn (fun _ : Fin 2 => 1) := by
  intro i
  simp

example : (Vector.ofFn (fun i : Fin 2 => i.1) : Vector Nat 2) ≤ˡ Vector.ofFn (fun i : Fin 2 => i.1) := by
  left
  rfl

example : (Vector.ofFn (fun i : Fin 2 => i.1) : Vector Nat 2) ≤ₗ Vector.ofFn (fun i : Fin 2 => i.1) := by
  left
  rfl

end Tests.VectorRangeIterators
