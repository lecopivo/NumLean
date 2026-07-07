module

public import NumLean.Interfaces.VectorType.Basic
public import NumLean.Interfaces.Algebra.Ring
public import NumLean.Data.Vector.TensorAlgebra.Lemmas

@[expose] public section

/-!
Interfaces for tensor algebra operations on vector-like storage types.
-/

namespace NumLean

open Tensor Interfaces Algebra

open VectorType in
/--
Tensor algebra operations for a family of vector-like storage types `Ks` over scalars `K`.
-/
@[hierarchy_graph algebra_ops]
class TensorRingOps (Ks : Nat → Type) (K : Type)
    [RingOps K] [VectorType Ks K] where

  /-- Sum the entries selected by a tensor layout. -/
  tensorSum {r : Rank} {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n)) : K

  /-- Add a scaled tensor into another tensor, writing through an injective destination layout. -/
  tensorAxpy {r : Rank} {m n : Nat} {shape : Shape r} (a : K)
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) : Ks m

  /-- Add a scaled slice of a tensor into a disjoint slice of the same tensor. -/
  tensorAxpySelf {r : Rank} {n : Nat} {shape : Shape r} (a : K)
    (data : Ks n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range) : Ks n

  /-- Scale the tensor entries selected by an injective layout in place. -/
  tensorScal {r : Rank} {n : Nat} {shape : Shape r} (a : K)
    (xs : Ks n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) : Ks n

  /-- Dot product of two tensors sharing the same logical shape. -/
  tensorDot {r : Rank} {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m)) : K

  /-- Multiply selected entries of the destination tensor by entries from another tensor. -/
  tensorMul {r : Rank} {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) : Ks m

  /-- Matrix-vector multiplication over tensor-shaped row and column axes. -/
  tensorGemv {an xn yn : Nat}
    {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod rows cols) h(an))
    (x : Ks xn) (xmap : Layout cols h(xn))
    (y : Ks yn) (ymap : Layout rows h(yn))
    (hymap : ymap.Injective) : Ks yn

  /-- Add a scaled outer product to a matrix-shaped tensor. -/
  tensorGer {an xn yn : Nat}
    {rr rc : Rank} {rows : Shape rr} {cols : Shape rc}
    (alpha : K)
    (x : Ks xn) (xmap : Layout rows h(xn))
    (y : Ks yn) (ymap : Layout cols h(yn))
    (A : Ks an) (amap : Layout (.prod rows cols) h(an))
    (hamap : amap.Injective) : Ks an

  /-- Matrix-matrix multiplication over tensor-shaped axes. -/
  tensorGemm {an bn cn : Nat}
    {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod is ks) h(an))
    (B : Ks bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Ks cn) (cmap : Layout (.prod is js) h(cn))
    (hcmap : cmap.Injective) : Ks cn


open VectorType in
/--
Laws relating `TensorRingOps` implementations to their `Vector` counterparts.
-/
@[hierarchy_graph algebra_lawful]
class LawfulTensorRingOps (Ks : Nat → Type) (K : Type)
    [CommRing K] [VectorType Ks K] [TensorRingOps Ks K] : Prop where

  tensorSum_eq_vector_tensorSum {r : Rank} {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n)) :
    TensorRingOps.tensorSum (Ks:=Ks) (K:=K) (r:=r) xs xmap
    =
    Vector.tensorSum (toVector xs) xmap

  toVector_tensorAxpy {r : Rank} {m n : Nat} {shape : Shape r} (a : K)
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) :
    toVector (TensorRingOps.tensorAxpy (Ks:=Ks) (K:=K) (r:=r) a xs xmap ys ymap hymap)
    =
    Vector.tensorAxpy a (toVector xs) xmap (toVector ys) ymap hymap

  toVector_tensorAxpySelf {r : Rank} {n : Nat} {shape : Shape r} (a : K)
    (data : Ks n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range) :
    toVector (TensorRingOps.tensorAxpySelf (Ks:=Ks) (K:=K) (r:=r)
      a data srcMap dstMap hdst h)
    =
    Vector.tensorAxpySelf a (toVector data) srcMap dstMap hdst h

  toVector_tensorScal {r : Rank} {n : Nat} {shape : Shape r} (a : K)
    (xs : Ks n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) :
    toVector (TensorRingOps.tensorScal (Ks:=Ks) (K:=K) (r:=r) a xs xmap hxmap)
    =
    Vector.tensorScal a (toVector xs) xmap hxmap

  tensorDot_eq_vector_tensorDot {r : Rank} {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m)) :
    TensorRingOps.tensorDot (Ks:=Ks) (K:=K) (r:=r) xs xmap ys ymap
    =
    Vector.tensorDot (toVector xs) xmap (toVector ys) ymap

  toVector_tensorMul {r : Rank} {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) :
    toVector (TensorRingOps.tensorMul (Ks:=Ks) (K:=K) (r:=r) xs xmap ys ymap hymap)
    =
    Vector.tensorMul (toVector xs) xmap (toVector ys) ymap hymap

  toVector_tensorGemv {an xn yn : Nat}
    {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod rows cols) h(an))
    (x : Ks xn) (xmap : Layout cols h(xn))
    (y : Ks yn) (ymap : Layout rows h(yn))
    (hymap : ymap.Injective) :
    toVector (TensorRingOps.tensorGemv (Ks:=Ks) (K:=K)
      alpha beta A amap x xmap y ymap hymap)
    =
    Vector.tensorGemv alpha beta (toVector A) amap (toVector x) xmap (toVector y) ymap hymap

  toVector_tensorGer {an xn yn : Nat}
    {rr rc : Rank} {rows : Shape rr} {cols : Shape rc}
    (alpha : K)
    (x : Ks xn) (xmap : Layout rows h(xn))
    (y : Ks yn) (ymap : Layout cols h(yn))
    (A : Ks an) (amap : Layout (.prod rows cols) h(an))
    (hamap : amap.Injective) :
    toVector (TensorRingOps.tensorGer (Ks:=Ks) (K:=K)
      alpha x xmap y ymap A amap hamap)
    =
    Vector.tensorGer alpha (toVector x) xmap (toVector y) ymap (toVector A) amap hamap

  toVector_tensorGemm {an bn cn : Nat}
    {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod is ks) h(an))
    (B : Ks bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Ks cn) (cmap : Layout (.prod is js) h(cn))
    (hcmap : cmap.Injective) :
  toVector (TensorRingOps.tensorGemm (Ks:=Ks) (K:=K)
      alpha beta A amap B bmap C cmap hcmap)
    =
    Vector.tensorGemm alpha beta (toVector A) amap (toVector B) bmap (toVector C) cmap hcmap

namespace TensorRingOps

section VectorInstances

instance {K} [RingOps K] : TensorRingOps (Vector K) K where
  tensorSum := Vector.tensorSum
  tensorAxpy := Vector.tensorAxpy
  tensorAxpySelf := Vector.tensorAxpySelf
  tensorScal := Vector.tensorScal
  tensorDot := Vector.tensorDot
  tensorMul := Vector.tensorMul
  tensorGemv := Vector.tensorGemv
  tensorGer := Vector.tensorGer
  tensorGemm := Vector.tensorGemm

instance {K} [CommRing K] : LawfulTensorRingOps (Vector K) K where
  tensorSum_eq_vector_tensorSum := by intros; rfl
  toVector_tensorAxpy := by intros; rfl
  toVector_tensorAxpySelf := by intros; rfl
  toVector_tensorScal := by intros; rfl
  tensorDot_eq_vector_tensorDot := by intros; rfl
  toVector_tensorMul := by intros; rfl
  toVector_tensorGemv := by intros; rfl
  toVector_tensorGer := by intros; rfl
  toVector_tensorGemm := by intros; rfl

end VectorInstances

open Classical VectorType IndexType

variable {Ks : Nat → Type} {K : Type} {r : Rank}
variable [CommRing K] [VectorType Ks K] [TensorRingOps Ks K]
variable [LawfulTensorRingOps Ks K]

theorem tensorSum_eq_sum [LawfulRingOps K] {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n)) :
    TensorRingOps.tensorSum (Ks:=Ks) (K:=K) (r:=r) xs xmap
    =
    ∑ i ∈ (NumLean.entries (0...shape)).toFinset,
      VectorType.get xs (xmap i) (by get_elem_tactic) := by
  rw [LawfulTensorRingOps.tensorSum_eq_vector_tensorSum]
  simpa [VectorType.get_spec] using
    (Vector.tensorSum_eq_sum (xs := toVector xs) xmap)

theorem tensorSum_eq_sum' [LawfulRingOps K] {n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n)) :
    TensorRingOps.tensorSum (Ks:=Ks) (K:=K) (r:=r) xs xmap
    =
    ∑ i : Fin shape.numel,
      let i := fromFin (I:=FinHTuple shape) i
      VectorType.get xs (xmap i) (by get_elem_tactic) := by
  rw [LawfulTensorRingOps.tensorSum_eq_vector_tensorSum]
  simpa [VectorType.get_spec] using
    (Vector.tensorSum_eq_sum' (xs := toVector xs) xmap)

@[simp]
theorem get_tensorAxpy {m n : Nat} {shape : Shape r} (a : K)
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) (idx : Nat) (hidx : idx < m) :
    VectorType.get (TensorRingOps.tensorAxpy (Ks:=Ks) (K:=K) (r:=r)
      a xs xmap ys ymap hymap) idx hidx
    =
    if hi : idx ∈ ymap.rangeNat then
      VectorType.get ys idx hidx
        + a * VectorType.get xs (xmap (ymap.rangeNatInv idx hi)) (by get_elem_tactic)
    else
      VectorType.get ys idx hidx := by
  rw [VectorType.get_spec, LawfulTensorRingOps.toVector_tensorAxpy]
  simpa only [VectorType.get_spec] using
    (Vector.getElem_tensorAxpy (a := a) (xs := toVector xs) (xmap := xmap)
      (ys := toVector ys) (ymap := ymap) (hymap := hymap) idx hidx)


set_option linter.unusedSectionVars false in
@[simp]
theorem get_tensorAxpySelf {n : Nat} {shape : Shape r} (a : K)
    (data : Ks n) (srcMap : Layout shape h(n)) (dstMap : Layout shape h(n))
    (hdst : dstMap.Injective) (h : Disjoint srcMap.range dstMap.range)
    (idx : Nat) (hidx : idx < n) :
    VectorType.get (TensorRingOps.tensorAxpySelf (Ks:=Ks) (K:=K) (r:=r)
      a data srcMap dstMap hdst h) idx hidx
    =
    if hi : idx ∈ dstMap.rangeNat then
      VectorType.get data idx hidx
        + a * VectorType.get data (srcMap (dstMap.rangeNatInv idx hi)) (by get_elem_tactic)
    else
      VectorType.get data idx hidx := by
  rw [VectorType.get_spec, LawfulTensorRingOps.toVector_tensorAxpySelf]
  simpa only [VectorType.get_spec] using
    (Vector.getElem_tensorAxpySelf (a := a) (data := toVector data) (srcMap := srcMap)
      (dstMap := dstMap) (hdst := hdst) (h := h) idx hidx)

@[simp]
theorem get_tensorScal {n : Nat} {shape : Shape r} (a : K)
    (xs : Ks n) (xmap : Layout shape h(n))
    (hxmap : xmap.Injective) (idx : Nat) (hidx : idx < n) :
    VectorType.get (TensorRingOps.tensorScal (Ks:=Ks) (K:=K) (r:=r)
      a xs xmap hxmap) idx hidx
    =
    if _hi : idx ∈ xmap.rangeNat then
      a * VectorType.get xs idx hidx
    else
      VectorType.get xs idx hidx := by
  rw [VectorType.get_spec, LawfulTensorRingOps.toVector_tensorScal]
  simpa only [VectorType.get_spec] using
    (Vector.getElem_tensorScal (a := a) (xs := toVector xs) (xmap := xmap)
      (hxmap := hxmap) idx hidx)

theorem tensorDot_eq_sum [LawfulRingOps K] {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m)) :
    TensorRingOps.tensorDot (Ks:=Ks) (K:=K) (r:=r) xs xmap ys ymap
    =
    ∑ i ∈ (NumLean.entries (0...shape)).toFinset,
      VectorType.get xs (xmap i) (by get_elem_tactic)
        * VectorType.get ys (ymap i) (by get_elem_tactic) := by
  rw [LawfulTensorRingOps.tensorDot_eq_vector_tensorDot]
  simpa [VectorType.get_spec] using
    (Vector.tensorDot_eq_sum (xs := toVector xs) (xmap := xmap)
      (ys := toVector ys) (ymap := ymap))

theorem tensorDot_eq_sum' [LawfulRingOps K] {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m)) :
    TensorRingOps.tensorDot (Ks:=Ks) (K:=K) (r:=r) xs xmap ys ymap
    =
    ∑ i : Fin shape.numel,
      let i := fromFin (I:=FinHTuple shape) i
      VectorType.get xs (xmap i) (by get_elem_tactic)
        * VectorType.get ys (ymap i) (by get_elem_tactic) := by
  rw [LawfulTensorRingOps.tensorDot_eq_vector_tensorDot]
  simpa [VectorType.get_spec] using
    (Vector.tensorDot_eq_sum' (xs := toVector xs) (xmap := xmap)
      (ys := toVector ys) (ymap := ymap))

@[simp]
theorem get_tensorMul {m n : Nat} {shape : Shape r}
    (xs : Ks n) (xmap : Layout shape h(n))
    (ys : Ks m) (ymap : Layout shape h(m))
    (hymap : ymap.Injective) (idx : Nat) (hidx : idx < m) :
    VectorType.get (TensorRingOps.tensorMul (Ks:=Ks) (K:=K) (r:=r)
      xs xmap ys ymap hymap) idx hidx
    =
    if hi : idx ∈ ymap.rangeNat then
      VectorType.get ys idx hidx
        * VectorType.get xs (xmap (ymap.rangeNatInv idx hi)) (by get_elem_tactic)
    else
      VectorType.get ys idx hidx := by
  rw [VectorType.get_spec, LawfulTensorRingOps.toVector_tensorMul]
  simpa only [VectorType.get_spec] using
    (Vector.getElem_tensorMul (xs := toVector xs) (xmap := xmap)
      (ys := toVector ys) (ymap := ymap) (hymap := hymap) idx hidx)

@[simp]
theorem get_tensorGemv [LawfulRingOps K] {an xn yn : Nat}
    {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod rows cols) h(an))
    (x : Ks xn) (xmap : Layout cols h(xn))
    (y : Ks yn) (ymap : Layout rows h(yn))
    (hymap : ymap.Injective) (idx : Nat) (hidx : idx < yn) :
    VectorType.get (TensorRingOps.tensorGemv (Ks:=Ks) (K:=K)
      alpha beta A amap x xmap y ymap hymap) idx hidx
    =
    if h : idx ∈ ymap.rangeNat then
      let ⟨i, hi⟩ := ymap.rangeNatInv idx h
      alpha * (∑ ⟨j,hj⟩ ∈ (NumLean.entries (0...cols)).toFinset,
        VectorType.get A (amap (i.prod j)) (by get_elem_tactic)
          * VectorType.get x (xmap j) (by get_elem_tactic))
      +
      beta * VectorType.get y idx hidx
    else
      VectorType.get y idx hidx := by
  rw [VectorType.get_spec, LawfulTensorRingOps.toVector_tensorGemv]
  simpa only [VectorType.get_spec] using
    (Vector.getElem_tensorGemv (alpha := alpha) (beta := beta) (A := toVector A)
      (amap := amap) (x := toVector x) (xmap := xmap) (y := toVector y)
      (ymap := ymap) (hymap := hymap) idx hidx)

@[simp]
theorem get_tensorGemv' [LawfulRingOps K] {an xn yn : Nat}
    {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod rows cols) h(an))
    (x : Ks xn) (xmap : Layout cols h(xn))
    (y : Ks yn) (ymap : Layout rows h(yn))
    (hymap : ymap.Injective) (idx : Nat) (hidx : idx < yn) :
    VectorType.get (TensorRingOps.tensorGemv (Ks:=Ks) (K:=K)
      alpha beta A amap x xmap y ymap hymap) idx hidx
    =
    if h : idx ∈ ymap.rangeNat then
      let ⟨i, hi⟩ := ymap.rangeNatInv idx h
      alpha * (∑ j : Fin cols.numel,
        let j := fromFin (I:=FinHTuple cols) j
        VectorType.get A (amap (i.prod j)) (by get_elem_tactic)
          * VectorType.get x (xmap j) (by get_elem_tactic))
      +
      beta * VectorType.get y idx hidx
    else
      VectorType.get y idx hidx := by
  rw [VectorType.get_spec, LawfulTensorRingOps.toVector_tensorGemv]
  simpa only [VectorType.get_spec] using
    (Vector.getElem_tensorGemv' (alpha := alpha) (beta := beta) (A := toVector A)
      (amap := amap) (x := toVector x) (xmap := xmap) (y := toVector y)
      (ymap := ymap) (hymap := hymap) idx hidx)

@[simp]
theorem get_tensorGer {an xn yn : Nat}
    {rr rc : Rank} {rows : Shape rr} {cols : Shape rc}
    (alpha : K)
    (x : Ks xn) (xmap : Layout rows h(xn))
    (y : Ks yn) (ymap : Layout cols h(yn))
    (A : Ks an) (amap : Layout (.prod rows cols) h(an))
    (hamap : amap.Injective) (idx : Nat) (hidx : idx < an) :
    VectorType.get (TensorRingOps.tensorGer (Ks:=Ks) (K:=K)
      alpha x xmap y ymap A amap hamap) idx hidx
    =
    if h : idx ∈ amap.rangeNat then
      let ⟨.prod i j, hij⟩ := amap.rangeNatInv idx h
      VectorType.get A idx hidx
        + alpha * VectorType.get x (xmap i) (by get_elem_tactic)
          * VectorType.get y (ymap j) (by get_elem_tactic)
    else
      VectorType.get A idx hidx := by
  rw [VectorType.get_spec, LawfulTensorRingOps.toVector_tensorGer]
  simpa only [VectorType.get_spec] using
    (Vector.getElem_tensorGer (alpha := alpha) (x := toVector x) (xmap := xmap)
      (y := toVector y) (ymap := ymap) (A := toVector A) (amap := amap)
      (hamap := hamap) idx hidx)

@[simp]
theorem get_tensorGemm [LawfulRingOps K] {an bn cn : Nat}
    {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod is ks) h(an))
    (B : Ks bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Ks cn) (cmap : Layout (.prod is js) h(cn))
    (hcmap : cmap.Injective) (idx : Nat) (hidx : idx < cn) :
    VectorType.get (TensorRingOps.tensorGemm (Ks:=Ks) (K:=K)
      alpha beta A amap B bmap C cmap hcmap) idx hidx
    =
    if h : idx ∈ cmap.rangeNat then
      let ⟨.prod i j, hij⟩ := cmap.rangeNatInv idx h
      alpha * (∑ ⟨k,hk⟩ ∈ (NumLean.entries (0...ks)).toFinset,
        VectorType.get A (amap (i.prod k)) (by get_elem_tactic)
          * VectorType.get B (bmap (k.prod j)) (by get_elem_tactic))
      +
      beta * VectorType.get C idx hidx
    else
      VectorType.get C idx hidx := by
  rw [VectorType.get_spec, LawfulTensorRingOps.toVector_tensorGemm]
  simpa only [VectorType.get_spec] using
    (Vector.getElem_tensorGemm (alpha := alpha) (beta := beta) (A := toVector A)
      (amap := amap) (B := toVector B) (bmap := bmap) (C := toVector C)
      (cmap := cmap) (hcmap := hcmap) idx hidx)

theorem get_tensorGemm' [LawfulRingOps K] {an bn cn : Nat}
    {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Ks an) (amap : Layout (.prod is ks) h(an))
    (B : Ks bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Ks cn) (cmap : Layout (.prod is js) h(cn))
    (hcmap : cmap.Injective) (idx : Nat) (hidx : idx < cn) :
    VectorType.get (TensorRingOps.tensorGemm (Ks:=Ks) (K:=K)
      alpha beta A amap B bmap C cmap hcmap) idx hidx
    =
    if h : idx ∈ cmap.rangeNat then
      let ⟨.prod i j, hij⟩ := cmap.rangeNatInv idx h
      alpha * (∑ k : Fin ks.numel,
        let k := fromFin (I := FinHTuple ks) k
        VectorType.get A (amap (i.prod k.val)) (by get_elem_tactic)
          * VectorType.get B (bmap (k.val.prod j)) (by get_elem_tactic))
      +
      beta * VectorType.get C idx hidx
    else
      VectorType.get C idx hidx := by
  rw [VectorType.get_spec, LawfulTensorRingOps.toVector_tensorGemm]
  simpa only [VectorType.get_spec] using
    (Vector.getElem_tensorGemm' (alpha := alpha) (beta := beta) (A := toVector A)
      (amap := amap) (B := toVector B) (bmap := bmap) (C := toVector C)
      (cmap := cmap) (hcmap := hcmap) idx hidx)

theorem tensorSum_id [LawfulRingOps K] {n : Nat}
    (xs : Ks n) :
    TensorRingOps.tensorSum (Ks:=Ks) (K:=K) (r:=.leaf) xs (Layout.id h(n))
    =
    ∑ i ∈ (NumLean.entries (0...h(n))).toFinset,
      VectorType.get xs i (by get_elem_tactic) := by
  simpa using
    (tensorSum_eq_sum (Ks:=Ks) (K:=K) (r:=.leaf) (xs := xs) (xmap := Layout.id h(n)))

@[simp mid+1]
theorem get_tensorAxpy_id
    {n : Nat} (a : K)
    (xs ys : Ks n) (idx : Nat) (hidx : idx < n) :
    VectorType.get (TensorRingOps.tensorAxpy (Ks:=Ks) (K:=K) (r:=.leaf)
      a xs (Layout.id h(n)) ys (Layout.id h(n)) (FinHTupleMap.injective_id h(n))) idx hidx
    =
    VectorType.get ys idx hidx + a * VectorType.get xs idx hidx := by
  rw [get_tensorAxpy]
  by_cases hi : idx ∈ (Layout.id h(n)).rangeNat
  · have hinv : ∀ hmem : idx ∈ (Layout.id h(n)).rangeNat,
        (↑((Layout.id h(n)).rangeNatInv idx hmem).val : Nat) = idx := by
      intro hmem
      simpa using (Layout.id h(n)).eval_rangeNatInv idx hmem
    simp [hi, hinv]
  · have hmem : idx ∈ (Layout.id h(n)).rangeNat := by
      refine ⟨⟨h(idx), ?_⟩, ?_⟩
      · simpa using hidx
      · simp
    exact False.elim (hi hmem)

@[simp mid+1]
theorem get_tensorScal_id
    {n : Nat} (a : K)
    (xs : Ks n) (idx : Nat) (hidx : idx < n) :
    VectorType.get (TensorRingOps.tensorScal (Ks:=Ks) (K:=K) (r:=.leaf)
      a xs (Layout.id h(n)) (FinHTupleMap.injective_id h(n))) idx hidx
    =
    a * VectorType.get xs idx hidx := by
  rw [get_tensorScal]
  by_cases hi : idx ∈ (Layout.id h(n)).rangeNat
  · simp [hi]
  · have hmem : idx ∈ (Layout.id h(n)).rangeNat := by
      refine ⟨⟨h(idx), ?_⟩, ?_⟩
      · simpa using hidx
      · simp
    exact False.elim (hi hmem)

theorem tensorDot_id [LawfulRingOps K] {n : Nat}
    (xs ys : Ks n) :
    TensorRingOps.tensorDot (Ks:=Ks) (K:=K) (r:=.leaf) xs (Layout.id h(n)) ys (Layout.id h(n))
    =
    ∑ i ∈ (NumLean.entries (0...h(n))).toFinset,
      VectorType.get xs i (by get_elem_tactic) * VectorType.get ys i (by get_elem_tactic) := by
  simpa using
    (tensorDot_eq_sum (Ks:=Ks) (K:=K) (r:=.leaf) (xs := xs) (xmap := Layout.id h(n))
      (ys := ys) (ymap := Layout.id h(n)))


@[simp mid+1]
theorem get_tensorMul_id
    {n : Nat}
    (xs ys : Ks n) (idx : Nat) (hidx : idx < n) :
    VectorType.get (TensorRingOps.tensorMul (Ks:=Ks) (K:=K) (r:=.leaf)
      xs (Layout.id h(n)) ys (Layout.id h(n)) (FinHTupleMap.injective_id h(n))) idx hidx
    =
    VectorType.get ys idx hidx * VectorType.get xs idx hidx := by
  rw [get_tensorMul]
  by_cases hi : idx ∈ (Layout.id h(n)).rangeNat
  · have hinv : ∀ hmem : idx ∈ (Layout.id h(n)).rangeNat,
        (↑((Layout.id h(n)).rangeNatInv idx hmem).val : Nat) = idx := by
      intro hmem
      simpa using (Layout.id h(n)).eval_rangeNatInv idx hmem
    simp [hi, hinv]
  · have hmem : idx ∈ (Layout.id h(n)).rangeNat := by
      refine ⟨⟨h(idx), ?_⟩, ?_⟩
      · simpa using hidx
      · simp
    exact False.elim (hi hmem)


private theorem vector_getElem_congr {α : Type u} {n i j : Nat} (v : Vector α n)
    (hi : i < n) (hj : j < n) (hij : i = j) : v[i]'hi = v[j]'hj := by
  subst hij
  rfl


set_option linter.unusedSectionVars false in
theorem get_tensorGemv_rowMajor [LawfulRingOps K]
    {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : K)
    (A : Ks (rows.prod cols).numel)
    (x : Ks cols.numel) (y : Ks rows.numel)
    (i : HTuple Nat ra) (hi : i <ₑ rows) :
    VectorType.get (TensorRingOps.tensorGemv (Ks:=Ks) (K:=K)
      alpha beta
      A (FinHTupleMap.rowMajorMap (rows.prod cols))
      x (FinHTupleMap.rowMajorMap cols)
      y (FinHTupleMap.rowMajorMap rows)
      (FinHTupleMap.injective_rowMajorMap rows))
      (i.rowMajorIndex rows) (HTuple.rowMajorIndex_lt_numel hi)
    =
    alpha * (∑ ⟨j, hj⟩ ∈ (NumLean.entries (0...cols)).toFinset,
      VectorType.get A ((i.prod j).rowMajorIndex (rows.prod cols))
        (HTuple.rowMajorIndex_lt_numel (by get_elem_tactic))
        * VectorType.get x (j.rowMajorIndex cols) (HTuple.rowMajorIndex_lt_numel (by get_elem_tactic)))
    +
    beta * VectorType.get y (i.rowMajorIndex rows) (HTuple.rowMajorIndex_lt_numel hi)
    := by
  rw [get_tensorGemv]
  have hmem : i.rowMajorIndex rows ∈ (FinHTupleMap.rowMajorMap rows).rangeNat :=
    FinHTupleMap.mem_rangeNat_rowMajorIndex rows i hi
  have hinv : (FinHTupleMap.rowMajorMap rows).rangeNatInv (i.rowMajorIndex rows) hmem =
      (⟨i, hi⟩ : FinHTuple rows) :=
    FinHTupleMap.rangeNatInv_rowMajorIndex rows i hi
  have hamap : ∀ j : HTuple Nat rc,
      (↑((FinHTupleMap.rowMajorMap (rows.prod cols)) (i.prod j)) : Nat) =
        (i.prod j).rowMajorIndex (rows.prod cols) := by
    intro j
    change (((FinHTupleMap.rowMajorMap (rows.prod cols)) (i.prod j)).toScalar) =
      (i.prod j).rowMajorIndex (rows.prod cols)
    rw [FinHTupleMap.eval_rowMajorMap]
    rfl
  have hxmap : ∀ j : HTuple Nat rc,
      (↑((FinHTupleMap.rowMajorMap cols) j) : Nat) = j.rowMajorIndex cols := by
    intro j
    change (((FinHTupleMap.rowMajorMap cols) j).toScalar) = j.rowMajorIndex cols
    rw [FinHTupleMap.eval_rowMajorMap]
    rfl
  simp only [hmem, ↓reduceDIte, hinv]
  apply congrArg (fun s => alpha * s + beta * VectorType.get y (i.rowMajorIndex rows)
    (HTuple.rowMajorIndex_lt_numel hi))
  apply Finset.sum_congr rfl
  intro j _hj
  rw [VectorType.get_spec, VectorType.get_spec, VectorType.get_spec, VectorType.get_spec]
  apply congrArg₂ (· * ·)
  · exact vector_getElem_congr (VectorType.toVector A) _ _ (hamap j.1)
  · exact vector_getElem_congr (VectorType.toVector x) _ _ (hxmap j.1)


set_option linter.unusedSectionVars false in
theorem get_tensorGer_rowMajor
    {rr rc : Rank} {rows : Shape rr} {cols : Shape rc}
    (alpha : K)
    (x : Ks rows.numel) (y : Ks cols.numel)
    (A : Ks (rows.prod cols).numel)
    (i : HTuple Nat rr) (hi : i <ₑ rows)
    (j : HTuple Nat rc) (hj : j <ₑ cols) :
    VectorType.get (TensorRingOps.tensorGer (Ks:=Ks) (K:=K)
      alpha
      x (FinHTupleMap.rowMajorMap rows)
      y (FinHTupleMap.rowMajorMap cols)
      A (FinHTupleMap.rowMajorMap (rows.prod cols))
      (FinHTupleMap.injective_rowMajorMap (rows.prod cols)))
      ((i.prod j).rowMajorIndex (rows.prod cols))
      (HTuple.rowMajorIndex_lt_numel (by get_elem_tactic))
    =
    VectorType.get A ((i.prod j).rowMajorIndex (rows.prod cols))
      (HTuple.rowMajorIndex_lt_numel (by get_elem_tactic))
      + alpha * VectorType.get x (i.rowMajorIndex rows) (HTuple.rowMajorIndex_lt_numel hi)
        * VectorType.get y (j.rowMajorIndex cols) (HTuple.rowMajorIndex_lt_numel hj) := by
  rw [get_tensorGer]
  have hmem : (i.prod j).rowMajorIndex (rows.prod cols) ∈
      (FinHTupleMap.rowMajorMap (rows.prod cols)).rangeNat :=
    FinHTupleMap.mem_rangeNat_rowMajorIndex (rows.prod cols) (i.prod j) (by get_elem_tactic)
  have hinv : (FinHTupleMap.rowMajorMap (rows.prod cols)).rangeNatInv
      ((i.prod j).rowMajorIndex (rows.prod cols)) hmem =
        (⟨i.prod j, by get_elem_tactic⟩ : FinHTuple (rows.prod cols)) :=
    FinHTupleMap.rangeNatInv_rowMajorIndex (rows.prod cols) (i.prod j) (by get_elem_tactic)
  have hxmap : (↑((FinHTupleMap.rowMajorMap rows) i) : Nat) = i.rowMajorIndex rows := by
    change (((FinHTupleMap.rowMajorMap rows) i).toScalar) = i.rowMajorIndex rows
    rw [FinHTupleMap.eval_rowMajorMap]
    rfl
  have hymap : (↑((FinHTupleMap.rowMajorMap cols) j) : Nat) = j.rowMajorIndex cols := by
    change (((FinHTupleMap.rowMajorMap cols) j).toScalar) = j.rowMajorIndex cols
    rw [FinHTupleMap.eval_rowMajorMap]
    rfl
  simp only [hmem, ↓reduceDIte, hinv]
  apply congrArg₂ (HAdd.hAdd · ·)
  · rfl
  · rw [VectorType.get_spec, VectorType.get_spec, VectorType.get_spec, VectorType.get_spec]
    apply congrArg₂ (fun xij yij => alpha * xij * yij)
    · exact vector_getElem_congr (VectorType.toVector x) _ _ hxmap
    · exact vector_getElem_congr (VectorType.toVector y) _ _ hymap


set_option linter.unusedSectionVars false in
theorem get_tensorGemm_rowMajor [LawfulRingOps K]
    {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : K)
    (A : Ks (is.prod ks).numel)
    (B : Ks (ks.prod js).numel)
    (C : Ks (is.prod js).numel)
    (i : HTuple Nat ri) (hi : i <ₑ is)
    (j : HTuple Nat rj) (hj : j <ₑ js) :
    VectorType.get (TensorRingOps.tensorGemm (Ks:=Ks) (K:=K)
      alpha beta
      A (FinHTupleMap.rowMajorMap (is.prod ks))
      B (FinHTupleMap.rowMajorMap (ks.prod js))
      C (FinHTupleMap.rowMajorMap (is.prod js))
      (FinHTupleMap.injective_rowMajorMap (is.prod js)))
      ((i.prod j).rowMajorIndex (is.prod js))
      (HTuple.rowMajorIndex_lt_numel (by get_elem_tactic))
    =
    alpha * (∑ ⟨k, hk⟩ ∈ (NumLean.entries (0...ks)).toFinset,
      VectorType.get A ((i.prod k).rowMajorIndex (is.prod ks))
        (HTuple.rowMajorIndex_lt_numel (by get_elem_tactic))
        * VectorType.get B ((k.prod j).rowMajorIndex (ks.prod js))
          (HTuple.rowMajorIndex_lt_numel (by get_elem_tactic)))
    +
    beta * VectorType.get C ((i.prod j).rowMajorIndex (is.prod js))
      (HTuple.rowMajorIndex_lt_numel (by get_elem_tactic)) := by
  rw [get_tensorGemm]
  have hmem : (i.prod j).rowMajorIndex (is.prod js) ∈
      (FinHTupleMap.rowMajorMap (is.prod js)).rangeNat :=
    FinHTupleMap.mem_rangeNat_rowMajorIndex (is.prod js) (i.prod j) (by get_elem_tactic)
  have hinv : (FinHTupleMap.rowMajorMap (is.prod js)).rangeNatInv
      ((i.prod j).rowMajorIndex (is.prod js)) hmem =
        (⟨i.prod j, by get_elem_tactic⟩ : FinHTuple (is.prod js)) :=
    FinHTupleMap.rangeNatInv_rowMajorIndex (is.prod js) (i.prod j) (by get_elem_tactic)
  have hamap : ∀ k : HTuple Nat rk,
      (↑((FinHTupleMap.rowMajorMap (is.prod ks)) (i.prod k)) : Nat) =
        (i.prod k).rowMajorIndex (is.prod ks) := by
    intro k
    change (((FinHTupleMap.rowMajorMap (is.prod ks)) (i.prod k)).toScalar) =
      (i.prod k).rowMajorIndex (is.prod ks)
    rw [FinHTupleMap.eval_rowMajorMap]
    rfl
  have hbmap : ∀ k : HTuple Nat rk,
      (↑((FinHTupleMap.rowMajorMap (ks.prod js)) (k.prod j)) : Nat) =
        (k.prod j).rowMajorIndex (ks.prod js) := by
    intro k
    change (((FinHTupleMap.rowMajorMap (ks.prod js)) (k.prod j)).toScalar) =
      (k.prod j).rowMajorIndex (ks.prod js)
    rw [FinHTupleMap.eval_rowMajorMap]
    rfl
  simp only [hmem, ↓reduceDIte, hinv]
  apply congrArg (fun s => alpha * s + beta * VectorType.get C
    ((i.prod j).rowMajorIndex (is.prod js)) (HTuple.rowMajorIndex_lt_numel (by get_elem_tactic)))
  apply Finset.sum_congr rfl
  intro k _hk
  rw [VectorType.get_spec, VectorType.get_spec, VectorType.get_spec, VectorType.get_spec]
  apply congrArg₂ (· * ·)
  · exact vector_getElem_congr (VectorType.toVector A) _ _ (hamap k.1)
  · exact vector_getElem_congr (VectorType.toVector B) _ _ (hbmap k.1)


end TensorRingOps
