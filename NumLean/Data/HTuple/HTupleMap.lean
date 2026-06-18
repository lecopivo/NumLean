import NumLean.Data.HTuple.Algebra

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

@[simp]
theorem eval_id [Semiring I] (x : HTuple I p) :
    (id (K := I) p).eval x = x := by
  simp [id, eval]

/-- Move a nested output coefficient profile into the output profile. -/
def joinEquiv (I : Type u) (r p q : HTuple.Profile) :
    HTupleMap (HTuple I r) p q ≃ HTupleMap I p (r * q) where
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
