import NumLean.Data.Vector.Basic
import NumLean.Data.Vector.TensorAlgebra.Basic
import NumLean.Interfaces.Fold.Lemmas
import NumLean.Meta.ForAll

set_option backward.do.legacy false

namespace NumLean
namespace Vector

open Tensor

def tensorScal [Mul K] {n : Nat} {r : Rank} {shape : Shape r}
    (a : K) (xs : Vector K n) (xmap : Layout shape h(n))
    (_hxmap : xmap.Injective) : Vector K n := Id.run do
  let mut xs := xs
  for_all i in 0...shape do
    xs[xmap i] := a * xs[xmap i]
  return xs

open Classical in
theorem tensorScal_eq_map [Mul K] {n : Nat} {r : Rank} {shape : Shape r}
    (a : K) (xs : Vector K n) (xmap : Layout shape h(n)) (hxmap : xmap.Injective) :
    tensorScal a xs xmap hxmap =
      xs.mapFinIdx fun j xj _ =>
        if _h : ∃ i, ∃ _hi : i ∈ ((0 : Shape r)...shape),
            (xmap i).toScalar = j then
          a * xj
        else
          xj := by
  simpa [tensorScal] using
    (Fold.fold_eq_vector_map
      (range := ((0 : Shape r)...shape))
      (imap := fun i _ => (xmap i).toScalar)
      (f := fun _ _ xj => a * xj)
      (init := xs)
      (himap := map_toScalar_lt xmap)
      (himap' := map_toScalar_injective xmap hxmap))

def tensorMul [Mul K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (_hymap : ymap.Injective) : Vector K m := Id.run do
  let mut ys := ys
  for_all i in 0...shape do
    ys[ymap i] := ys[ymap i] * xs[xmap i]
  return ys

open Classical in
theorem tensorMul_eq_map [Mul K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) :
    tensorMul xs xmap ys ymap hymap =
      ys.mapFinIdx fun j yj _ =>
        if h : ∃ i, ∃ _hi : i ∈ ((0 : Shape r)...shape),
            (ymap i).toScalar = j then
          let i := choose h
          let hi := choose (choose_spec h)
          yj * xs[xmap i]'(map_toScalar_lt xmap i hi)
        else
          yj := by
  simpa [tensorMul] using
    (Fold.fold_eq_vector_map
      (range := ((0 : Shape r)...shape))
      (imap := fun i _ => (ymap i).toScalar)
      (f := fun i _ yj => yj * xs[xmap i])
      (init := ys)
      (himap := map_toScalar_lt ymap)
      (himap' := map_toScalar_injective ymap hymap))

def tensorProd [Mul K] [One K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n)) : K := Id.run do
  let mut acc := 1
  for_all i in 0...shape do
    acc := acc * xs[xmap i]
  return acc

end Vector
end NumLean
