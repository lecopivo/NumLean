module

public import NumLean.Data.HTuple.Range
public import NumLean.Data.HTuple.Algebra

@[expose] public section

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

@[simp]
theorem eval_mk [Zero J] [Add J] [SMul I J]
    (offset : HTuple J q) (strides : HTuple (HTuple J q) p) (x : HTuple I p) :
    (HTupleMap.mk offset strides).eval x = offset + x.inner strides := rfl

-- todo: do we want this even if we have to specialize to Nat?
instance : CoeFun (HTupleMap Nat p q) (fun _ => HTuple Nat p → HTuple Nat q) := ⟨eval⟩

variable (K) in
/-- Identity affine `HTupleMap`. -/
def id [Zero K] [One K] (p : HTuple.Profile) : HTupleMap K p p where
  offset := 0
  stride := HTuple.basisTuple p

@[simp]
theorem eval_id [Semiring I] (x : HTuple I p) : (id I p).eval x = x := by
  simp [id, eval]

/-- Constant affine map. -/
def const [Zero K] (p : HTuple.Profile) (x : HTuple K q) : HTupleMap K p q where
  offset := x
  stride := 0

@[simp]
theorem eval_const [Semiring I] [AddCommMonoid K] [Module I K]
    (x : HTuple K q) (i : HTuple I p) :
    (const p x).eval i = x := by
  simp [const, eval]

/-- Compose affine `HTupleMap`s. -/
def comp [Zero K] [Add K] [SMul J K] (g : HTupleMap K q r) (f : HTupleMap J p q) :
    HTupleMap K p r where
  offset := g.offset + f.offset.inner g.stride
  stride := f.stride.map fun fs => fs.inner g.stride

@[simp]
theorem eval_comp [Semiring I] [Semiring J] [AddCommMonoid K] [Module I J]
    [Module J K] [Module I K] [IsScalarTower I J K]
    (g : HTupleMap K q r) (f : HTupleMap J p q) (x : HTuple I p) :
    (g.comp f).eval x = g.eval (f.eval x) := by
  simp [comp, eval]
  rw [HTuple.inner_add_left, HTuple.inner_map_inner]
  simp [add_assoc]

/-- Project the left component of a product-valued affine map. -/
def fst (f : HTupleMap K p (.prod q r)) : HTupleMap K p q where
  offset := f.offset.fst
  stride := f.stride.map HTuple.fst

@[simp]
theorem eval_fst [Zero K] [Add K] [SMul I K] (f : HTupleMap K p (.prod q r))
    (i : HTuple I p) :
    f.fst.eval i = (f.eval i).fst := by
  cases f with | mk offset stride =>
  cases offset with | prod offset₀ offset₁ =>
  simp [fst, eval, HTuple.inner_map_prod_fst]
  cases i.inner stride with | prod x y => rfl

/-- Project the right component of a product-valued affine map. -/
def snd (f : HTupleMap K p (.prod q r)) : HTupleMap K p r where
  offset := f.offset.snd
  stride := f.stride.map HTuple.snd

@[simp]
theorem eval_snd [Zero K] [Add K] [SMul I K] (f : HTupleMap K p (.prod q r))
    (i : HTuple I p) :
    f.snd.eval i = (f.eval i).snd := by
  cases f with | mk offset stride =>
  cases offset with | prod offset₀ offset₁ =>
  simp [snd, eval, HTuple.inner_map_prod_snd]
  cases i.inner stride with | prod x y => rfl

/-- Pair two affine maps with the same source profile. -/
def prod (f : HTupleMap K p q) (g : HTupleMap K p r) : HTupleMap K p (.prod q r) where
  offset := .prod f.offset g.offset
  stride := HTuple.map₂ (fun x y => HTuple.prod x y) f.stride g.stride

@[simp]
theorem eval_prod [Zero K] [Add K] [SMul I K] (f : HTupleMap K p q) (g : HTupleMap K p r)
    (i : HTuple I p) :
    (f.prod g).eval i = HTuple.prod (f.eval i) (g.eval i) := by
  cases f with | mk offset₀ stride₀ =>
  cases g with | mk offset₁ stride₁ =>
  simp [prod, eval, HTuple.inner_map₂_prod]

/-- Cast an affine map across definitionally/simp-equal source and destination profiles. -/
def cast {p q : HTuple.Profile} (f : HTupleMap K p q) (p' q' : HTuple.Profile)
    (hp : p' = p := by simp) (hq : q' = q := by simp) : HTupleMap K p' q' := by
  cases hp
  cases hq
  exact f

@[simp]
theorem eval_cast [Zero J] [Add J] [SMul I J]
    {p q : HTuple.Profile} (f : HTupleMap J p q) (p' q' : HTuple.Profile)
    (hp : p' = p) (hq : q' = q) (i : HTuple I p') :
    (f.cast p' q' hp hq).eval i = hq.symm ▸ f.eval (hp ▸ i) := by
  cases hp
  cases hq
  rfl

/-- Same as `f.cast p' q'` but infers `p'` and `q'` from the expected type after simp-normalizing
the original profiles. -/
abbrev simpCast {p q : HTuple.Profile} (f : HTupleMap K p q) {p' q' : HTuple.Profile}
    (hp : p' = p := by (conv_rhs => simp))
    (hq : q' = q := by (conv_rhs => simp)) : HTupleMap K p' q' :=
  f.cast p' q' hp hq

/-- Row-major affine linearization map from `0...shape` into a flat natural coordinate. -/
def rowMajorMap (shape : HTuple Nat q) : HTupleMap Nat q .leaf where
  offset := .leaf 0
  stride := shape.rowMajorStride.map HTuple.leaf

/-- `linearize` computes the row-major range index. -/
@[simp]
theorem eval_rowMajorMap (shape : HTuple Nat q) (i : HTuple Nat q) :
    rowMajorMap shape i = h(i.rowMajorIndex shape) := by
  simp [rowMajorMap, HTuple.rowMajorIndex_eq_inner_rowMajorStride, HTuple.inner_map_leaf]

/-- `linearize` maps bounded coordinates into `0...shape.numel`. -/
theorem eval_rowMajorMap_lt_card {shape : HTuple Nat q} {i : HTuple Nat q}
    (hi : i <ₑ shape) : rowMajorMap shape i <ₑ h(shape.numel) := by
  rw [eval_rowMajorMap]
  simpa using HTuple.rowMajorIndex_lt_numel hi

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
