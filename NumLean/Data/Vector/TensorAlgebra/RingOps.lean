import NumLean.Data.Vector.TensorAlgebra.SemiringOps

set_option backward.do.legacy false

namespace NumLean
namespace Vector

open Tensor

def tensorNeg [Neg K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (_hxmap : xmap.Injective) : Vector K n := Id.run do
  let mut xs := xs
  for_all i in 0...shape do
    xs[xmap i] := -xs[xmap i]
  return xs

open Classical in
theorem tensorNeg_eq_map [Neg K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n)) (hxmap : xmap.Injective) :
    tensorNeg xs xmap hxmap =
      xs.mapFinIdx fun j xj _ =>
        if _h : ∃ i, ∃ _hi : i ∈ ((0 : Shape r)...shape),
            (xmap i).toScalar = j then
          -xj
        else
          xj := by
  simpa [tensorNeg] using
    (Fold.fold_eq_vector_map
      (range := ((0 : Shape r)...shape))
      (imap := fun i _ => (xmap i).toScalar)
      (f := fun _ _ xj => -xj)
      (init := xs)
      (himap := map_toScalar_lt xmap)
      (himap' := map_toScalar_injective xmap hxmap))

def tensorSub [Sub K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (_hymap : ymap.Injective) : Vector K m := Id.run do
  let mut ys := ys
  for_all i in 0...shape do
    ys[ymap i] := ys[ymap i] - xs[xmap i]
  return ys

open Classical in
theorem tensorSub_eq_map [Sub K] {m n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) :
    tensorSub xs xmap ys ymap hymap =
      ys.mapFinIdx fun j yj _ =>
        if h : ∃ i, ∃ _hi : i ∈ ((0 : Shape r)...shape),
            (ymap i).toScalar = j then
          let i := choose h
          let hi := choose (choose_spec h)
          yj - xs[xmap i]'(map_toScalar_lt xmap i hi)
        else
          yj := by
  simpa [tensorSub] using
    (Fold.fold_eq_vector_map
      (range := ((0 : Shape r)...shape))
      (imap := fun i _ => (ymap i).toScalar)
      (f := fun i _ yj => yj - xs[xmap i])
      (init := ys)
      (himap := map_toScalar_lt ymap)
      (himap' := map_toScalar_injective ymap hymap))

end Vector
end NumLean
