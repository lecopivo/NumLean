import NumLean.Data.Vector.Basic
import NumLean.Data.Vector.TensorAlgebra.Basic
import NumLean.Interfaces.Fold.Lemmas
import NumLean.Meta.ForAll

set_option backward.do.legacy false

namespace NumLean
namespace Vector

open Tensor

def tensorSum [Add K] [Zero K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n)) : K := Id.run do
  let mut acc := 0
  for_all i in 0...shape do
    acc := acc + xs[xmap i]
  return acc

open Classical in
theorem tensorSum_eq_sum [AddCommMonoid K] {n : Nat} {r : Rank} {shape : Shape r}
    (xs : Vector K n) (xmap : Layout shape h(n)) :
    tensorSum xs xmap =
      0 + ∑ i ∈ (NumLean.entries (ρ := Std.Rco (Shape r)) (α := HTuple Nat r)
          ((0 : Shape r)...shape)).toFinset,
        xs[xmap i.1]'(map_toScalar_lt xmap i.1 i.2) := by
  simpa [tensorSum] using
    (Fold.fold_eq_sum
      (range := ((0 : Shape r)...shape))
      (f := fun i hi => xs[xmap i]'(map_toScalar_lt xmap i hi))
      (init := (0 : K)))

end Vector
end NumLean
