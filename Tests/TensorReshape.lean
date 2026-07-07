module

public import NumLean.Data.Tensor.Reshape

@[expose] public section

open NumLean

namespace Tests.TensorReshape

instance : HasDefaultFlatRepr Float (Vector Float) where

example (x : Tensor Float (Fin 6)) : Tensor Float (Fin 2 × Fin 3) :=
  x.reindex (J := Fin 2 × Fin 3)

example (x : Tensor Float (Fin 6)) : Tensor Float (Fin 2 × Fin 3) :=
  x.reshape h(2, 3)

example (x : Tensor Float (Fin 2 × Fin 3)) : Tensor (Tensor Float (Fin 3)) (Fin 2) :=
  x.curry

example (x : Tensor (Tensor Float (Fin 3)) (Fin 2)) : Tensor Float (Fin 2 × Fin 3) :=
  x.uncurry

example (x : Tensor Float (Fin 2 × Fin 3)) : x.curry.uncurry = x := by
  rfl

example (x : Tensor (Tensor Float (Fin 3)) (Fin 2)) : x.uncurry.curry = x := by
  rfl

end Tests.TensorReshape
