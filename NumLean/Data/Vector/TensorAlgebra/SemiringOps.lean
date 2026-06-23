import NumLean.Data.Vector.TensorAlgebra.AddOps
import NumLean.Data.Vector.TensorAlgebra.MulOps
import NumLean.Interfaces.Fold.Lemmas

set_option backward.do.legacy false

namespace NumLean
namespace Vector

open Tensor

def tensorAxpy [Add K] [Mul K] {m n : Nat} {r : Rank} {shape : Shape r}
    (a : K) (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (_hymap : ymap.Injective) : Vector K m := Id.run do
  let mut ys := ys
  for_all i in 0...shape do
    ys[ymap i] := ys[ymap i] + a * xs[xmap i]
  return ys

open Classical in
theorem tensorAxpy_eq_map [Add K] [Mul K] {m n : Nat} {r : Rank} {shape : Shape r}
    (a : K) (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) :
    tensorAxpy a xs xmap ys ymap hymap =
      ys.mapFinIdx fun j yj _ =>
        if h : ∃ i, ∃ _hi : i ∈ ((0 : Shape r)...shape),
            (ymap i).toScalar = j then
          let i := choose h
          let hi := choose (choose_spec h)
          yj + a * xs[xmap i]'(map_toScalar_lt xmap i hi)
        else
          yj := by
  simpa [tensorAxpy] using
    (Fold.fold_eq_vector_map
      (range := ((0 : Shape r)...shape))
      (imap := fun i _ => (ymap i).toScalar)
      (f := fun i _ yj => yj + a * xs[xmap i])
      (init := ys)
      (himap := map_toScalar_lt ymap)
      (himap' := map_toScalar_injective ymap hymap))

def tensorDot [Add K] [Mul K] [Zero K] {m n : Nat} {r : Rank}
    {shape : Shape r} (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m)) : K := Id.run do
  let mut acc := 0
  for_all i in 0...shape do
    acc := acc + xs[xmap i] * ys[ymap i]
  return acc

open Classical in
theorem tensorDot_eq_sum [AddCommMonoid K] [Mul K] {m n : Nat} {r : Rank}
    {shape : Shape r} (xs : Vector K n) (xmap : Layout shape h(n))
    (ys : Vector K m) (ymap : Layout shape h(m)) :
    tensorDot xs xmap ys ymap =
      0 + ∑ i ∈ (NumLean.entries (ρ := Std.Rco (Shape r)) (α := HTuple Nat r)
          ((0 : Shape r)...shape)).toFinset,
        xs[xmap i.1]'(map_toScalar_lt xmap i.1 i.2) *
          ys[ymap i.1]'(map_toScalar_lt ymap i.1 i.2) := by
  simpa [tensorDot] using
    (Fold.fold_eq_sum
      (range := ((0 : Shape r)...shape))
      (f := fun i hi => xs[xmap i]'(map_toScalar_lt xmap i hi) *
        ys[ymap i]'(map_toScalar_lt ymap i hi))
      (init := (0 : K)))

def tensorGemv [Add K] [Mul K] [Zero K] {an xn yn : Nat}
    {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : K)
    (A : Vector K an) (amap : Layout (.prod rows cols) h(an))
    (x : Vector K xn) (xmap : Layout cols h(xn))
    (y : Vector K yn) (ymap : Layout rows h(yn))
    (_hymap : ymap.Injective) : Vector K yn := Id.run do
  let mut y := y
  for_all i in 0...rows do
    let mut acc := 0
    for_all j in 0...cols do
      acc := acc + A[amap (i.prod j)] * x[xmap j]
    y[ymap i] := alpha * acc + beta * y[ymap i]
  return y

open Classical in
theorem tensorGemv_eq_map [AddCommMonoid K] [Mul K] {an xn yn : Nat}
    {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : K)
    (A : Vector K an) (amap : Layout (.prod rows cols) h(an))
    (x : Vector K xn) (xmap : Layout cols h(xn))
    (y : Vector K yn) (ymap : Layout rows h(yn))
    (hymap : ymap.Injective) :
    tensorGemv alpha beta A amap x xmap y ymap hymap =
      y.mapFinIdx fun j yj _ =>
        if h : ∃ i, ∃ _hi : i ∈ ((0 : Shape ra)...rows),
            (ymap i).toScalar = j then
          let i := choose h
          let hi := choose (choose_spec h)
          alpha *
            (0 + ∑ k ∈ (NumLean.entries (0...cols)).toFinset,
              A[amap (i.prod k.1)]'(map_toScalar_lt amap (i.prod k.1)
                (prod_mem_zero_shape hi k.2)) *
                x[xmap k.1]'(map_toScalar_lt xmap k.1 k.2)) +
            beta * yj
        else
          yj := by
  simpa [tensorGemv, Fold.fold_eq_sum] using
    (Fold.fold_eq_vector_map
      (range := ((0 : Shape ra)...rows))
      (imap := fun i _ => (ymap i).toScalar)
      (f := fun i hi yj =>
        alpha *
          (0 + ∑ k ∈ (NumLean.entries (ρ := Std.Rco (Shape rc)) (α := HTuple Nat rc)
              ((0 : Shape rc)...cols)).toFinset,
            A[amap (i.prod k.1)]'(map_toScalar_lt amap (i.prod k.1)
              (prod_mem_zero_shape hi k.2)) *
              x[xmap k.1]'(map_toScalar_lt xmap k.1 k.2)) +
          beta * yj)
      (init := y)
      (himap := map_toScalar_lt ymap)
      (himap' := map_toScalar_injective ymap hymap))

def tensorGer [Add K] [Mul K] {an xn yn : Nat}
    {rr rc : Rank} {rows : Shape rr} {cols : Shape rc}
    (alpha : K)
    (x : Vector K xn) (xmap : Layout rows h(xn))
    (y : Vector K yn) (ymap : Layout cols h(yn))
    (A : Vector K an) (amap : Layout (.prod rows cols) h(an))
    (_hamap : amap.Injective) : Vector K an := Id.run do
  let mut A := A
  for_all i in 0...rows do
    for_all j in 0...cols do
      A[amap (i.prod j)] := A[amap (i.prod j)] + alpha * x[xmap i] * y[ymap j]
  return A

def tensorGemm [Add K] [Mul K] [Zero K] {an bn cn : Nat}
    {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Vector K an) (amap : Layout (.prod is ks) h(an))
    (B : Vector K bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Vector K cn) (cmap : Layout (.prod is js) h(cn))
    (_hcmap : cmap.Injective) : Vector K cn := Id.run do
  let mut C := C
  for_all i in 0...is do
    for_all j in 0...js do
      let mut acc := 0
      for_all k in 0...ks do
        acc := acc + A[amap (i.prod k)] * B[bmap (k.prod j)]
      C[cmap (i.prod j)] := alpha * acc + beta * C[cmap (i.prod j)]
  return C

end Vector
end NumLean
