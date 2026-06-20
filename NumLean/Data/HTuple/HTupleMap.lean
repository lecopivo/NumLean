import NumLean.Data.HTuple.Range

namespace NumLean

/-- An affine map between hierarchical tuple profiles. -/
structure HTupleMap (D : Type u) (p q : HTuple.Profile) where
  offset : HTuple D q
  stride : HTuple (HTuple D q) p

namespace HTupleMap

variable {I : Type u} {J : Type v} {K : Type w}
variable {p q r : HTuple.Profile}

/-- Evaluate an affine `HTupleMap`. -/
def eval [Zero J] [Add J] [SMul I J] (f : HTupleMap J p q) (x : HTuple I p) : HTuple J q :=
  f.offset + x.inner f.stride

/-- Compose affine `HTupleMap`s. -/
def comp [Zero K] [Add K] [SMul J K] (g : HTupleMap K q r) (f : HTupleMap J p q) :
    HTupleMap K p r where
  offset := g.offset + f.offset.inner g.stride
  stride := f.stride.map fun fs => fs.inner g.stride

/-- Identity affine `HTupleMap`. -/
def id [Zero K] [One K] (p : HTuple.Profile) : HTupleMap K p p where
  offset := 0
  stride := HTuple.basisTuple p

/-- Alias for `id`, matching the bounded `FinHTupleMap.identity` API. -/
def identity [Zero K] [One K] (p : HTuple.Profile) : HTupleMap K p p :=
  id p

/-- Project the left component of a product-valued affine map. -/
def fst (f : HTupleMap K p (.prod q r)) : HTupleMap K p q where
  offset := match f.offset with | .prod x _ => x
  stride := f.stride.map fun y => match y with | .prod x _ => x

/-- Project the right component of a product-valued affine map. -/
def snd (f : HTupleMap K p (.prod q r)) : HTupleMap K p r where
  offset := match f.offset with | .prod _ y => y
  stride := f.stride.map fun y => match y with | .prod _ y => y

/-- Pair two affine maps with the same source profile. -/
def prod (f : HTupleMap K p q) (g : HTupleMap K p r) : HTupleMap K p (.prod q r) where
  offset := .prod f.offset g.offset
  stride := HTuple.map₂ (fun x y => HTuple.prod x y) f.stride g.stride

/-- Constant affine map. -/
def const [Zero K] (p : HTuple.Profile) (x : HTuple K q) : HTupleMap K p q where
  offset := x
  stride := 0

/-- Row-major affine linearization map from `0...shape` into a flat natural coordinate. -/
def linearize (shape : HTuple Nat q) : HTupleMap Nat q .leaf where
  offset := .leaf 0
  stride := shape.rowMajorStride.map HTuple.leaf

/-- `linearize` computes the row-major range index. -/
theorem eval_linearize (shape : HTuple Nat q) (i : HTuple Nat q) :
    (linearize shape).eval i = h(i.rowMajorIndex shape) := by
  sorry

/-- `linearize` maps bounded coordinates into `0...shape.numel`. -/
theorem eval_linearize_lt_card {shape : HTuple Nat q} {i : HTuple Nat q}
    (hi : i <ₑ shape) : (linearize shape).eval i <ₑ h(shape.numel) := by
  sorry

@[simp]
theorem eval_id [Semiring I] (x : HTuple I p) :
    (id (K := I) p).eval x = x := by
  simp [id, eval]

/-- Move a nested output coefficient profile into the output profile. -/
def joinEquiv (I : Type u) (r p q : HTuple.Profile) :
    HTupleMap (HTuple I r) p q ≃ HTupleMap I p (r.tmul q) where
  toFun f :=
    { offset := f.offset.join
      stride := f.stride.map HTuple.join }
  invFun f :=
    { offset := f.offset.split
      stride := f.stride.map HTuple.split }
  left_inv f := by
    cases f
    simp
  right_inv f := by
    cases f
    simp

end HTupleMap

end NumLean
