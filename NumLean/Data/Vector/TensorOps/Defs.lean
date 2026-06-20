import NumLean.Data.Vector.Basic
import NumLean.Data.FinHTuple.Basic
import NumLean.Data.FinHTuple.FinHTupleMap
import NumLean.Meta.ForAll

set_option backward.do.legacy false

namespace NumLean

namespace Vector

namespace ForAll

/-- Reverse the first coordinate in a product domain `(.leaf k, shape)`. -/
def reverseIndex {k} {r : HTuple.Profile} {shape : HTuple Nat r} :
    FinHTuple (.prod (.leaf k) shape) → FinHTuple (.prod (.leaf k) shape) :=
  fun ⟨.prod (.leaf i) j, _h⟩ => ⟨.prod (.leaf (k - i - 1)) j, by grind⟩

/-- Swap the two coordinates in a square product domain. -/
def transposeIndex {r : HTuple.Profile} {shape : HTuple Nat r} :
    FinHTuple (.prod shape shape) → FinHTuple (.prod shape shape) :=
  fun ⟨.prod i j, _h⟩ => ⟨.prod j i, by grind⟩

/-- Swap the two coordinates in a square product domain. -/
def transposeIndex' {r : HTuple.Profile} {shape : HTuple Nat r} :
    HTuple Nat (.prod r r) → HTuple Nat (.prod r r) :=
  fun (.prod i j) => .prod j i

/-- Copy a splice from `src` to `dst` i.e. dst[dstMap i] := src[srcMap i]. -/
def copySlice {K n m} {r : HTuple.Profile} {shape : HTuple Nat r}
    (src : Vector K n) (srcMap : FinHTupleMap shape h(n))
    (dst : Vector K m) (dstMap : FinHTupleMap shape h(m))
    (_h : dstMap.Injective) : Vector K m := Id.run do
  let mut dst := dst
  for_all i in 0...shape do
    dst[dstMap i] := src[srcMap i]
  return dst

/-- Reverse along the first dimension of the domain of `map`, swapping
`xs[map (i, j)]` with `xs[map (k - i - 1, j)]`. -/
def reverseSlice {K n k} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Vector K n) (map : FinHTupleMap (.prod (.leaf k) shape) h(n))
    (_h : map.Injective) : Vector K n := Id.run do
  let mut xs := xs
  for_all i in (0 : Nat)...(k / 2) do
    for_all j in (0 : HTuple Nat r)...shape do
      let idx := map ((HTuple.leaf i).prod j)
      let idx' := map ((HTuple.leaf (k - i - 1)).prod j)
      xs := xs.swap idx idx'
  return xs

/-- Transpose elements of `xs` based on `map`, swapping `xs[map (i,j)]` with `xs[map (j,i)]`. -/
def transposeSlice {K n} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Vector K n) (map : FinHTupleMap (.prod shape shape) h(n))
    (_h : map.Injective) : Vector K n := Id.run do
  let mut xs := xs
  for_all i in (0 : HTuple Nat r)...shape do
    for_all j in (0 : HTuple Nat r)...shape do
      let ij := map (i.prod j)
      let ji := map (j.prod i)
      if ij.toScalar < ji then
        xs := xs.swap ij ji
  return xs

/-- Swap data between two vectors through corresponding slices. -/
def swapSlice {K m n} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Vector K m) (xmap : FinHTupleMap shape h(m))
    (ys : Vector K n) (ymap : FinHTupleMap shape h(n))
    (_h : xmap.Injective) (_h' : ymap.Injective) : Vector K m × Vector K n := Id.run do
  let mut xs := xs
  let mut ys := ys
  for_all i in (0 : HTuple Nat r)...shape do
    let idx := xmap i
    let jdx := ymap i
    let tmp := xs[idx]
    xs[idx] := ys[jdx]
    ys[jdx] := tmp
  return (xs, ys)

end ForAll

end Vector

end NumLean
