import NumLean.Data.Vector.TensorOps.Defs
import NumLean.Interfaces.VectorType.Basic

namespace NumLean

/-- Tensor-style operations on vector-like storage.

The operations mirror the reference implementations in `Vector.ForAll`. The specification fields are
part of this class: an implementation is required to commute with `VectorType.toVector` and
`VectorType.fromVector`, rather than satisfying a separate lawful class. -/
class TensorArrayOps (Ks : Nat → Type u) (K : outParam Type) [VectorType Ks K] where
  copySlice {m n : Nat} {r : HTuple.Profile} {shape : HTuple Nat r}
    (src : Ks n) (srcMap : FinHTupleMap shape h(n))
    (dst : Ks m) (dstMap : FinHTupleMap shape h(m))
    (hdst : dstMap.Injective) : Ks m
  copySlice_spec {m n : Nat} {r : HTuple.Profile} {shape : HTuple Nat r}
    (src : Ks n) (srcMap : FinHTupleMap shape h(n))
    (dst : Ks m) (dstMap : FinHTupleMap shape h(m))
    (hdst : dstMap.Injective) :
    VectorType.toVector (A:=K) (copySlice src srcMap dst dstMap hdst) =
      Vector.ForAll.copySlice (VectorType.toVector (A:=K) src) srcMap
        (VectorType.toVector (A:=K) dst) dstMap hdst

  reverseSlice {n k : Nat} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Ks n) (map : FinHTupleMap (.prod (.leaf k) shape) h(n))
    (hmap : map.Injective) : Ks n
  reverseSlice_spec {n k : Nat} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Ks n) (map : FinHTupleMap (.prod (.leaf k) shape) h(n))
    (hmap : map.Injective) :
    VectorType.toVector (A:=K) (reverseSlice xs map hmap) =
      Vector.ForAll.reverseSlice (VectorType.toVector (A:=K) xs) map hmap

  transposeSlice {n : Nat} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Ks n) (map : FinHTupleMap (.prod shape shape) h(n))
    (hmap : map.Injective) : Ks n
  transposeSlice_spec {n : Nat} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Ks n) (map : FinHTupleMap (.prod shape shape) h(n))
    (hmap : map.Injective) :
    VectorType.toVector (A:=K) (transposeSlice xs map hmap) =
      Vector.ForAll.transposeSlice (VectorType.toVector (A:=K) xs) map hmap

  swapSlice {m n : Nat} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Ks m) (xmap : FinHTupleMap shape h(m))
    (ys : Ks n) (ymap : FinHTupleMap shape h(n))
    (hxmap : xmap.Injective) (hymap : ymap.Injective) : Ks m × Ks n
  swapSlice_spec {m n : Nat} {r : HTuple.Profile} {shape : HTuple Nat r}
    (xs : Ks m) (xmap : FinHTupleMap shape h(m))
    (ys : Ks n) (ymap : FinHTupleMap shape h(n))
    (hxmap : xmap.Injective) (hymap : ymap.Injective) :
    let out := swapSlice xs xmap ys ymap hxmap hymap
    (VectorType.toVector (A:=K) out.1, VectorType.toVector (A:=K) out.2) =
      Vector.ForAll.swapSlice (VectorType.toVector (A:=K) xs) xmap
        (VectorType.toVector (A:=K) ys) ymap hxmap hymap

namespace TensorArrayOps

variable {Ks : Nat → Type u} {K : Type} [VectorType Ks K] [TensorArrayOps Ks K]

instance {K : Type} : TensorArrayOps (Vector K) K where
  copySlice src srcMap dst dstMap hdst :=
    Vector.ForAll.copySlice src srcMap dst dstMap hdst
  copySlice_spec := by intros; rfl
  reverseSlice xs map hmap :=
    Vector.ForAll.reverseSlice xs map hmap
  reverseSlice_spec := by intros; rfl
  transposeSlice xs map hmap :=
    Vector.ForAll.transposeSlice xs map hmap
  transposeSlice_spec := by intros; rfl
  swapSlice xs xmap ys ymap hxmap hymap :=
    Vector.ForAll.swapSlice xs xmap ys ymap hxmap hymap
  swapSlice_spec := by
    intro m n r shape xs xmap ys ymap hxmap hymap
    cases Vector.ForAll.swapSlice xs xmap ys ymap hxmap hymap
    rfl

end TensorArrayOps

end NumLean
