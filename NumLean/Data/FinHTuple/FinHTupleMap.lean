import NumLean.Data.FinHTuple.Basic

namespace NumLean

/-- Affine map from `HTuple Nat p` to `HTuple Nat q` with a guarantee that it will produce value
in `0...dst` when evaluated on `0...src`

This map is most often use to map tensor of shape `src` to a tensor of shape `dst`. Such maps
are often given by offset and strides which is exactly the data carried by `HTupleMap`.

You can evaluate this map in two ways
  - `f x`  for `x : FinHTuple src`
  - `f[x]` for `x : HTuple Nat p` assuming that `x <ₑ src` can be provan by `get_elem_tactic` -/
structure FinHTupleMap {p q} (src : HTuple Nat p) (dst : HTuple Nat q) extends HTupleMap Nat p q where
  inBounds : ∀ i : HTuple Nat p, i <ₑ src → toHTupleMap.eval i <ₑ dst

namespace FinHTupleMap

variable {p q : HTuple.Profile} {src : HTuple Nat p} {dst : HTuple Nat q}

/-- Raw evaluation of a bounded affine map on an unbounded tuple. -/
@[coe]
def eval (f : FinHTupleMap src dst) (i : HTuple Nat p) : HTuple Nat q := f.toHTupleMap.eval i

/-- Evaluate a bounded affine map on a bounded tuple, keeping the bounded output type. -/
def evalFin (f : FinHTupleMap src dst) (i : FinHTuple src) : FinHTuple dst :=
  ⟨f.eval i.val, f.inBounds i.val i.isLt⟩

instance : CoeFun (FinHTupleMap src dst) (fun _ => HTuple Nat p → HTuple Nat q) := ⟨eval⟩

-- todo: remove this
instance : GetElem (FinHTupleMap src dst) (HTuple Nat p) (FinHTuple dst) (fun _ i => i <ₑ src) where
  getElem f i h := f.evalFin ⟨i, h⟩

@[simp]
theorem eval_mk (f : HTupleMap Nat p q) (hf : ∀ i : HTuple Nat p, i <ₑ src → f.eval i <ₑ dst)
    (x : HTuple Nat p) :
    (FinHTupleMap.mk f hf) x = f x := by simp [eval]

@[simp]
theorem evalFin_val (f : FinHTupleMap src dst) (i : FinHTuple src) :
    (f.evalFin i).val = f.eval i.val := rfl

@[simp]
theorem getElem_val (f : FinHTupleMap src dst) (i : HTuple Nat p) (h : i <ₑ src) :
    (f[i]'h).val = f.eval i := rfl

@[simp]
theorem getElem_isLt (f : FinHTupleMap src dst) (i : HTuple Nat p) (h : i <ₑ src) :
    (f[i]'h).isLt = f.inBounds i h := rfl

@[grind ←, grind_htuple_order ←]
theorem eval_lt (f : FinHTupleMap src dst) (i : HTuple Nat p) : i <ₑ src → f i <ₑ dst := f.2 i

/-- Identity bounded affine map. -/
def id (src : HTuple Nat p) : FinHTupleMap src src where
  toHTupleMap := HTupleMap.id Nat p
  inBounds := by
    intro i hi
    simpa using hi

@[simp]
theorem id_eval (src : HTuple Nat p) (i : HTuple Nat p) : id src i = i := by
  simp [id, eval]

/-- Constant bounded affine map. -/
def const (src : HTuple Nat p) (dst : HTuple Nat q)
    (x : HTuple Nat q) (hx : x <ₑ dst := by get_elem_tactic) :
    FinHTupleMap src dst where
  toHTupleMap := HTupleMap.const p x
  inBounds := by
    intro i hi
    simpa only [HTupleMap.eval_const] using hx

@[simp]
theorem eval_const (src : HTuple Nat p) {dst : HTuple Nat q}
    (x : HTuple Nat q) (hx : x <ₑ dst) (i : HTuple Nat p) :
    const src dst x hx i = x := by
  simp [const, eval]

/-- Rank-1 strided map `i ↦ off + i * inc`. -/
def strided1D {len n : Nat} (off inc : Nat)
    (hb : off + len * inc ≤ n ∧ inc ≠ 0) : FinHTupleMap h(len) h(n) where
  toHTupleMap := ⟨h(off), h(h(inc))⟩
  inBounds := by
    intro i hi
    cases i with | leaf i =>
    simp only [HTuple.elementwiseLT_leaf] at hi ⊢
    have hinc : 0 < inc := Nat.pos_of_ne_zero hb.2
    have hidx : i * inc < len * inc := Nat.mul_lt_mul_of_pos_right hi hinc
    simp [HTupleMap.eval, HTuple.inner, HTuple.innerWith]
    omega

/-- Rank-1 contiguous map `i ↦ off + i`. -/
def contiguous1D {len n : Nat} (off : Nat) (h : off + len ≤ n) : FinHTupleMap h(len) h(n) :=
  strided1D off 1 (by omega)

/-- Rank-1 broadcast map `i ↦ idx`. The source index is ignored. -/
def broadcast1D {len n : Nat} (idx : Nat) (hidx : idx < n) : FinHTupleMap h(len) h(n) :=
  const h(len) h(n) h(idx) (by simpa)

@[simp]
theorem eval_strided1D {len n : Nat} (off inc : Nat)
    (hb : off + len * inc ≤ n ∧ inc ≠ 0) (i : HTuple Nat .leaf) :
    strided1D off inc hb i = h(off + i.toScalar * inc) := by
  cases i
  simp [strided1D, eval, HTupleMap.eval, HTuple.inner, HTuple.innerWith, nsmul_eq_mul]

@[simp]
theorem eval_contiguous1D {len n : Nat} (off : Nat) (hb : off + len ≤ n)
    (i : HTuple Nat .leaf) :
    contiguous1D off hb i = h(off + i.toScalar) := by
  cases i
  simp [contiguous1D, eval_strided1D]

@[simp]
theorem eval_broadcast1D {len n : Nat} (idx : Nat) (hidx : idx < n)
    (i : HTuple Nat .leaf) :
    broadcast1D (len := len) idx hidx i = h(idx) := by
  simp [broadcast1D]

/-- Compose bounded affine maps. -/
def comp {mid : HTuple Nat q} {r : HTuple.Profile} {dst : HTuple Nat r}
    (g : FinHTupleMap mid dst) (f : FinHTupleMap src mid) : FinHTupleMap src dst where
  toHTupleMap := g.toHTupleMap.comp f.toHTupleMap
  inBounds := by
    intro i hi
    simpa only [HTupleMap.eval_comp] using g.inBounds (f i) (f.inBounds i hi)

@[simp]
theorem eval_comp {mid : HTuple Nat q} {r : HTuple.Profile} {dst : HTuple Nat r}
    (g : FinHTupleMap mid dst) (f : FinHTupleMap src mid) (i : HTuple Nat p) :
    g.comp f i = g (f i) := by
  simp [comp, eval]

/-- Compose bounded affine maps when the inner map is known to land in the outer source. -/
def compCast {mid outerSrc : HTuple Nat q} {r : HTuple.Profile} {dst : HTuple Nat r}
    (g : FinHTupleMap outerSrc dst) (f : FinHTupleMap src mid)
    (hcast : ∀ i : HTuple Nat p, i <ₑ src → f.toHTupleMap.eval i <ₑ outerSrc) :
    FinHTupleMap src dst where
  toHTupleMap := HTupleMap.comp g.toHTupleMap f.toHTupleMap
  inBounds := by
    intro i hi
    simpa only [HTupleMap.eval_comp] using g.inBounds (f i) (hcast i hi)

@[simp]
theorem eval_compCast {mid outerSrc : HTuple Nat q} {r : HTuple.Profile} {dst : HTuple Nat r}
    (g : FinHTupleMap outerSrc dst) (f : FinHTupleMap src mid)
    (hcast : ∀ i : HTuple Nat p, i <ₑ src → f.toHTupleMap.eval i <ₑ outerSrc)
    (i : HTuple Nat p) :
    g.compCast f hcast i = g (f i) := by
  simp [compCast, eval]


/-- Project the left component of the bounded destination. -/
def fst {r : HTuple.Profile} {dst' : HTuple Nat r}
    (f : FinHTupleMap src (HTuple.prod dst dst')) : FinHTupleMap src dst where
  toHTupleMap := f.toHTupleMap.fst
  inBounds := by
    intro i hi
    have h := f.inBounds i hi
    cases hf : f.toHTupleMap.eval i with | prod x y =>
      simp [HTupleMap.eval_fst, hf] at h ⊢
      exact h.1

/-- Canonical bounded projection onto the left component of a product shape. -/
abbrev fstMap {r : HTuple.Profile} (shape : HTuple Nat p) (shape' : HTuple Nat r) :
    FinHTupleMap (HTuple.prod shape shape') shape := (id (shape.prod shape')).fst

@[simp]
theorem eval_fst {r : HTuple.Profile} {dst' : HTuple Nat r}
    (f : FinHTupleMap src (HTuple.prod dst dst')) (i : HTuple Nat p) :
    f.fst i = (f i).fst := by
  simp [fst, eval]

/-- Project the right component of the bounded destination. -/
def snd {r : HTuple.Profile} {dst' : HTuple Nat r}
    (f : FinHTupleMap src (HTuple.prod dst' dst)) : FinHTupleMap src dst where
  toHTupleMap := f.toHTupleMap.snd
  inBounds := by
    intro i hi
    have h := f.inBounds i hi
    cases hf : f.toHTupleMap.eval i with | prod x y =>
      simp [HTupleMap.eval_snd, hf] at h ⊢
      exact h.2

/-- Canonical bounded projection onto the right component of a product shape. -/
abbrev sndMap {r : HTuple.Profile} (shape : HTuple Nat p) (shape' : HTuple Nat r) :
    FinHTupleMap (HTuple.prod shape shape') shape' := (id (shape.prod shape')).snd

@[simp]
theorem eval_snd {r : HTuple.Profile} {dst' : HTuple Nat r}
    (f : FinHTupleMap src (HTuple.prod dst' dst)) (i : HTuple Nat p) :
    f.snd i = (f i).snd := by
  simp [snd, eval]

/-- Pair two bounded affine maps with the same source. -/
def prod {r : HTuple.Profile} {dst' : HTuple Nat r}
    (f : FinHTupleMap src dst) (g : FinHTupleMap src dst') :
    FinHTupleMap src (HTuple.prod dst dst') where
  toHTupleMap := HTupleMap.prod f.toHTupleMap g.toHTupleMap
  inBounds := by
    intro i hi
    simpa [eval, HTupleMap.eval_prod] using And.intro (f.inBounds i hi) (g.inBounds i hi)

@[simp]
theorem eval_prod {r : HTuple.Profile} {dst' : HTuple Nat r}
    (f : FinHTupleMap src dst) (g : FinHTupleMap src dst') (i : HTuple Nat p) :
    f.prod g i = HTuple.prod (f i) (g i) := by
  simp [prod, eval]

/-- Pair two bounded affine maps with independent sources. -/
def pair {p' q' : HTuple.Profile} {src' : HTuple Nat p'} {dst' : HTuple Nat q'}
    (f : FinHTupleMap src dst) (g : FinHTupleMap src' dst') :
    FinHTupleMap (HTuple.prod src src') (HTuple.prod dst dst') :=
  (f.comp (fstMap src src')).prod (g.comp (sndMap src src'))

@[simp]
theorem eval_pair {p' q' : HTuple.Profile} {src' : HTuple Nat p'} {dst' : HTuple Nat q'}
    (f : FinHTupleMap src dst) (g : FinHTupleMap src' dst')
    (i : HTuple Nat (.prod p p')) :
    f.pair g i = HTuple.prod (f i.fst) (g i.snd) := by
  simp [pair]

/-- Canonical bounded row-major linearization map for a shape. -/
def rowMajorMap (shape : HTuple Nat p) : FinHTupleMap shape h(shape.numel) where
  toHTupleMap := HTupleMap.rowMajorMap shape
  inBounds := by
    intro i hi
    exact HTupleMap.eval_rowMajorMap_lt_card hi

@[simp]
theorem eval_rowMajorMap (shape : HTuple Nat p) (i : HTuple Nat p) :
    rowMajorMap shape i = h(i.rowMajorIndex shape) := by
  simp [rowMajorMap, eval]

theorem eval_rowMajorMap_eq_linearIndex (shape : HTuple Nat p) (i : HTuple Nat p) :
    rowMajorMap shape i = h(HTuple.Range.linearIndex 0 shape i) := by
  simp [HTuple.Range.linearIndex_zero]

/-- Linearize the bounded destination of a map into its row-major flat index. -/
abbrev linearize (f : FinHTupleMap src dst) : FinHTupleMap src h(dst.numel) :=
  (rowMajorMap dst).comp f

def point (shape : HTuple Nat p) (x : HTuple Nat p) (h : x <ₑ shape := by get_elem_tactic) :
    FinHTupleMap h(1) shape where
  toHTupleMap := HTupleMap.const .leaf x
  inBounds := by
    intro i hi
    simp [h]

@[simp]
theorem eval_point (shape : HTuple Nat p) (x : HTuple Nat .leaf) (y : HTuple Nat p)
    (h : y <ₑ shape := by get_elem_tactic) :
  (point shape y) x = y := by simp [point]

-- do we need this? It might be handy
-- abbrev cast' {p q} {src : HTuple Nat p} {dst : HTuple Nat q}
--     (f : FinHTupleMap src dst) (p' q') (src' : HTuple Nat p') (dst' : HTuple Nat q')
--     (hp : p' = p := by conv_rhs => simp)
--     (hq : q' = q := by conv_rhs => simp)
--     (hsrc : src' = hp ▸ src := by (conv_rhs => simp))
--     (hdst : dst' = hq ▸ dst := by (conv_rhs => simp)) :
--     FinHTupleMap src' dst' where
--   toHTupleMap := f.toHTupleMap.cast p' q' hp hq
--   inBounds := by
--     intros
--     have := f.inBounds
--     sorry

def cast {p q} {src : HTuple Nat p} {dst : HTuple Nat q}
    (f : FinHTupleMap src dst) (src') (dst')
    (hsrc : src' = src := by simp)
    (hdst : dst' = dst := by simp) :
    FinHTupleMap src' dst' where
  toHTupleMap := f.toHTupleMap
  inBounds := by
    intros
    have := f.inBounds
    simp_all

@[simp]
theorem eval_cast {p q} {src : HTuple Nat p} {dst : HTuple Nat q}
    (f : FinHTupleMap src dst) (src' dst')
    (hsrc : src' = src) (hdst : dst' = dst) (i : HTuple Nat p) :
    f.cast src' dst' hsrc hdst i = f i := by
  simp [cast, eval]

/-- Same as `f.cast src' dst'` but you do not have to specify `src'` and `dst'`. The original
`src` and `dst` are put into simp-normal form. -/
abbrev simpCast {p q} {src : HTuple Nat p} {dst : HTuple Nat q}
    (f : FinHTupleMap src dst) {src'} {dst'}
    (hsrc : src' = src := by (conv_rhs => simp))
    (hdst : dst' = dst := by (conv_rhs => simp)) :
    FinHTupleMap src' dst' := f.cast src' dst' hsrc hdst

-- abbrev simpCast' {p q} {src : HTuple Nat p} {dst : HTuple Nat q}
--     (f : FinHTupleMap src dst) {p' q'} {src' : HTuple Nat p'} {dst' : HTuple Nat q'}
--     (hp : p' = p := by conv_rhs => simp)
--     (hq : q' = q := by conv_rhs => simp)
--     (hsrc : src' = hp ▸ src := by (conv_rhs => simp))
--     (hdst : dst' = hq ▸ dst := by (conv_rhs => simp)) :
--     FinHTupleMap src' dst' := f.cast' p' q' src' dst' hp hq hsrc hdst

/-- A bounded map has no collisions on its bounded domain. -/
def Injective (f : FinHTupleMap src dst) : Prop :=
  Function.Injective f.evalFin

@[grind ←]
theorem injective_id (src : HTuple Nat p) : (id src).Injective := by
  intro i j h
  apply FinHTuple.ext
  simpa using congrArg FinHTuple.val h

@[grind ←]
theorem injective_comp {mid : HTuple Nat q} {r : HTuple.Profile} {dst : HTuple Nat r}
    (g : FinHTupleMap mid dst) (f : FinHTupleMap src mid)
    (hg : g.Injective) (hf : f.Injective) : (g.comp f).Injective := by
  intro i j h
  apply hf
  apply hg
  apply FinHTuple.ext
  simpa using congrArg FinHTuple.val h

@[grind ←]
theorem injective_of_fst {r : HTuple.Profile} {dst' : HTuple Nat r}
    (f : FinHTupleMap src dst) (g : FinHTupleMap src dst') (hf : f.Injective) :
    (f.prod g).Injective := by
  intro i j h
  apply hf
  apply FinHTuple.ext
  have hval := congrArg FinHTuple.val h
  simpa using congrArg HTuple.fst hval

@[grind ←]
theorem injective_of_snd {r : HTuple.Profile} {dst' : HTuple Nat r}
    (f : FinHTupleMap src dst) (g : FinHTupleMap src dst') (hf : g.Injective) :
    (f.prod g).Injective := by
  intro i j h
  apply hf
  apply FinHTuple.ext
  have hval := congrArg FinHTuple.val h
  simpa using congrArg HTuple.snd hval

@[grind ←]
theorem injective_rowMajorMap (shape : HTuple Nat p) : (rowMajorMap shape).Injective := by
  intro i j h
  apply (FinHTuple.equivFin shape).injective
  apply Fin.ext
  have hval := congrArg FinHTuple.val h
  have hi := FinHTuple.equivFin_val_eq_linearIndex_zero shape i
  have hj := FinHTuple.equivFin_val_eq_linearIndex_zero shape j
  simp [evalFin, eval_rowMajorMap] at hval
  simpa [hi, hj, HTuple.Range.linearIndex_zero] using hval

@[grind ←]
theorem injective_prod_left {r : HTuple.Profile} {dst' : HTuple Nat r}
    {f : FinHTupleMap src dst} {g : FinHTupleMap src dst'}
    (hf : f.Injective) : (f.prod g).Injective := by
  intro i j h
  apply hf
  apply FinHTuple.ext
  have hval := congrArg FinHTuple.val h
  simpa using congrArg HTuple.fst hval

@[grind ←]
theorem injective_prod_right {r : HTuple.Profile} {dst' : HTuple Nat r}
    {f : FinHTupleMap src dst} {g : FinHTupleMap src dst'}
    (hg : g.Injective) : (f.prod g).Injective := by
  intro i j h
  apply hg
  apply FinHTuple.ext
  have hval := congrArg FinHTuple.val h
  simpa using congrArg HTuple.snd hval

@[grind ←]
theorem injective_of_pair {p' q' : HTuple.Profile} {src' : HTuple Nat p'} {dst' : HTuple Nat q'}
    {f : FinHTupleMap src dst} {g : FinHTupleMap src' dst'}
    (hf : f.Injective) (hg : g.Injective) : (f.pair g).Injective := by
  intro i j h
  cases i with | mk ival hi =>
  cases j with | mk jval hj =>
  cases ival with | prod il ir =>
  cases jval with | prod jl jr =>
  have hval := congrArg FinHTuple.val h
  have hl : (⟨il, hi.1⟩ : FinHTuple src) = ⟨jl, hj.1⟩ := by
    apply hf
    apply FinHTuple.ext
    simpa [evalFin] using congrArg HTuple.fst hval
  have hr : (⟨ir, hi.2⟩ : FinHTuple src') = ⟨jr, hj.2⟩ := by
    apply hg
    apply FinHTuple.ext
    simpa [evalFin] using congrArg HTuple.snd hval
  cases hl
  cases hr
  rfl

@[grind ←]
theorem injective_point (shape : HTuple Nat p) (y : HTuple Nat p)
    (h : y <ₑ shape := by get_elem_tactic) :
    (point shape y).Injective := by
  intro ⟨.leaf i,hi⟩ ⟨.leaf j,hj⟩ h
  have h' : i = j := by grind
  simp [h']

@[grind ←]
theorem injective_of_cast {src' : HTuple Nat p} {dst' : HTuple Nat q}
    {f : FinHTupleMap src dst} (hsrc : src' = src) (hdst : dst' = dst)
    (hf : f.Injective) : (f.cast src' dst' hsrc hdst).Injective := by
  subst hsrc
  subst hdst
  simpa [cast] using hf

/-- A bounded map has no collisions on its bounded domain. -/
def Bijective (f : FinHTupleMap src dst) : Prop :=
  Function.Bijective f.evalFin

/-- `f` maps `0...src` onto `f.range`

For very `y ∈ f.range` there is `x ∈ 0...src` such that `f x = y`. -/
def range (f : FinHTupleMap src dst) : Set (HTuple Nat q) :=
  Set.range fun i : FinHTuple src => f i

/-- `f` maps `0...src` onto `f.rangeNat`. This is variant of `f.range` where the `dst` is a scalar.

For very `y ∈ f.range` there is `x ∈ 0...src` such that `f x = y`. -/
def rangeNat {m} (f : FinHTupleMap src h(m)) : Set Nat :=
  Set.range fun i : FinHTuple src => (f i.1)

@[grind →, grind_htuple_order →]
theorem mem_range_lt {f : FinHTupleMap src dst} {i : HTuple Nat q} (h : i ∈ f.range) : i <ₑ dst := by
  rcases h with ⟨j, rfl⟩
  exact f.inBounds j.val j.isLt

@[simp, grind ←, grind_htuple_order ←]
theorem mem_range_eval {f : FinHTupleMap src dst} {i : FinHTuple src} : f i ∈ f.range := by
  simp [range]

@[grind →, grind_htuple_order →]
theorem mem_rangeNat_lt {f : FinHTupleMap src h(m)} {i : Nat} (h : i ∈ f.rangeNat) : i < m := by
  rcases h with ⟨j, rfl⟩
  simpa using f.inBounds j.val j.isLt

@[simp, grind ←, grind_htuple_order ←]
theorem mem_rangeNat_eval {m} {f : FinHTupleMap src h(m)} {i : FinHTuple src} :
    (f i : Nat) ∈ f.rangeNat := by
  simp [rangeNat]

section Disjoint

theorem disjoint_range_of_eval_ne {p' : HTuple.Profile} {src' : HTuple Nat p'}
    {f : FinHTupleMap src dst} {g : FinHTupleMap src' dst}
    (h : ∀ i : FinHTuple src, ∀ j : FinHTuple src', f i ≠ g j) :
    Disjoint f.range g.range := by
  rw [Set.disjoint_left]
  rintro x ⟨i, rfl⟩ ⟨j, hj⟩
  exact h i j hj.symm

@[grind ←]
theorem disjoint_range_point {i j : HTuple Nat p}
    {hi : i <ₑ src} {hj : j <ₑ src} (hij : i ≠ j) :
    Disjoint (point src i hi).range (point src j hj).range := by
  apply disjoint_range_of_eval_ne
  intro x y hxy
  exact hij (by simpa [point] using hxy)

@[grind ←]
theorem disjoint_range_pair_left {p' q' p₀ p₁ : HTuple.Profile}
    {src' : HTuple Nat p'} {dst' : HTuple Nat q'}
    {src₀ : HTuple Nat p₀} {src₁ : HTuple Nat p₁}
    {f : FinHTupleMap src dst} {g : FinHTupleMap src₀ dst}
    {f' : FinHTupleMap src' dst'} {g' : FinHTupleMap src₁ dst'}
    (hfg : Disjoint f.range g.range) :
    Disjoint (f.pair f').range (g.pair g').range := by
  apply disjoint_range_of_eval_ne
  intro i j hij
  cases i with | mk ival hi =>
  cases j with | mk jval hj =>
  cases ival with | prod il ir =>
  cases jval with | prod jl jr =>
  have hfst : f (⟨il, hi.1⟩ : FinHTuple src) = g (⟨jl, hj.1⟩ : FinHTuple src₀) := by
    simpa using congrArg HTuple.fst hij
  exact Set.disjoint_left.mp hfg mem_range_eval (by
    refine ⟨⟨jl, hj.1⟩, ?_⟩
    exact hfst.symm)

@[grind ←]
theorem disjoint_range_pair_right {p' q' p₀ p₁ : HTuple.Profile}
    {src' : HTuple Nat p'} {dst' : HTuple Nat q'}
    {src₀ : HTuple Nat p₀} {src₁ : HTuple Nat p₁}
    {f : FinHTupleMap src dst} {g : FinHTupleMap src₀ dst}
    {f' : FinHTupleMap src' dst'} {g' : FinHTupleMap src₁ dst'}
    (hfg : Disjoint f'.range g'.range) :
    Disjoint (f.pair f').range (g.pair g').range := by
  apply disjoint_range_of_eval_ne
  intro i j hij
  cases i with | mk ival hi =>
  cases j with | mk jval hj =>
  cases ival with | prod il ir =>
  cases jval with | prod jl jr =>
  have hsnd : f' (⟨ir, hi.2⟩ : FinHTuple src') = g' (⟨jr, hj.2⟩ : FinHTuple src₁) := by
    simpa using congrArg HTuple.snd hij
  exact Set.disjoint_left.mp hfg mem_range_eval (by
    refine ⟨⟨jr, hj.2⟩, ?_⟩
    exact hsnd.symm)

@[grind ←]
theorem disjoint_range_comp_of_injective {p₀ : HTuple.Profile} {src₀ : HTuple Nat p₀}
    {mid : HTuple Nat q} {r : HTuple.Profile} {dst₀ : HTuple Nat r}
    {f : FinHTupleMap src mid} {g : FinHTupleMap src₀ mid} {h : FinHTupleMap mid dst₀}
    (hfg : Disjoint f.range g.range) (hh : h.Injective) :
    Disjoint (h.comp f).range (h.comp g).range := by
  apply disjoint_range_of_eval_ne
  intro i j hij
  have hmid : f i = g j := by
    have hfin : h.evalFin ⟨f i, f.inBounds i i.isLt⟩ =
        h.evalFin ⟨g j, g.inBounds j j.isLt⟩ := by
      apply FinHTuple.ext
      simpa [evalFin] using hij
    exact congrArg FinHTuple.val (hh hfin)
  exact Set.disjoint_left.mp hfg mem_range_eval (by
    refine ⟨j, ?_⟩
    exact hmid.symm)

@[grind ←]
theorem disjoint_range_linearize {p₀ : HTuple.Profile} {src₀ : HTuple Nat p₀}
    {f : FinHTupleMap src dst} {g : FinHTupleMap src₀ dst}
    (hfg : Disjoint f.range g.range) :
    Disjoint f.linearize.range g.linearize.range := by
  exact disjoint_range_comp_of_injective hfg (injective_rowMajorMap dst)

end Disjoint

@[grind _=_, grind_htuple_order _=_]
theorem mem_range_iff_mem_rangeNat
    {p} {src : HTuple Nat p}
    (map : FinHTupleMap src h(n)) (i : Nat) :
    h(i) ∈ map.range ↔ i ∈ map.rangeNat := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    simpa using congrArg HTuple.toScalar hj
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    apply HTuple.toScalar_injective
    simpa using hj

noncomputable
def rangeInv (f : FinHTupleMap src dst) (i : HTuple Nat q) (h : i ∈ f.range) : FinHTuple src :=
  Classical.choose h

noncomputable
def rangeNatInv (f : FinHTupleMap src h(m)) (i : Nat) (h : i ∈ f.rangeNat) : FinHTuple src :=
  Classical.choose h

@[grind ←, grind_htuple_order ←]
theorem rangeInv_lt_src (f : FinHTupleMap src dst) (i : HTuple Nat q) (h : i ∈ f.range) :
    (f.rangeInv i h).val <ₑ src :=
  (f.rangeInv i h).isLt

@[grind ←, grind_htuple_order ←]
theorem rangeNatInv_lt_src (f : FinHTupleMap src h(m)) (i : Nat) (h : i ∈ f.rangeNat) :
    (f.rangeNatInv i h).val <ₑ src :=
  (f.rangeNatInv i h).isLt

open Function in
theorem invFun_evalFin_lt_src [Nonempty (FinHTuple src)]
    (f : FinHTupleMap src dst) (i : FinHTuple dst) :
    (invFun f.evalFin i).val <ₑ src :=
  (invFun f.evalFin i).isLt

open Function in
theorem eval_invFun (f : FinHTupleMap src dst) (i : HTuple Nat q) (h : i ∈ Set.range f) :
    f (invFun f i) = i := by
  apply Function.invFun_eq h

theorem eval_rangeInv (f : FinHTupleMap src dst) (i : HTuple Nat q) (h : i ∈ f.range) :
    f (f.rangeInv i h) = i := by
  exact Classical.choose_spec h

theorem eval_rangeNatInv (f : FinHTupleMap src h(m)) (i : Nat) (h : i ∈ f.rangeNat) :
    (f (f.rangeNatInv i h) : Nat) = i := by
  exact Classical.choose_spec h

theorem rangeInv_eval (f : FinHTupleMap src dst) (i : FinHTuple src) (h : f.Injective) :
    f.rangeInv (f i) (by simp) = i := by
  apply h
  apply FinHTuple.ext
  exact f.eval_rangeInv (f i) (by simp)

theorem rangeNatInv_eval (f : FinHTupleMap src h(m)) (i : FinHTuple src) (h : f.Injective) :
    f.rangeNatInv (f i) (by simp) = i := by
  apply h
  apply FinHTuple.ext
  apply HTuple.toScalar_injective
  simpa using f.eval_rangeNatInv (f i) (by simp)

-- -- is this even true? probably yes as we are working with Nat
-- /-- Bounded affine maps are equal when their underlying affine maps agree on all bounded inputs. -/
-- theorem ext (f g : FinHTupleMap src dst) :
--     (∀ i : FinHTuple src, f.toHTupleMap.eval i.val = g.toHTupleMap.eval i.val) → f = g := by
--   intro h
--   cases f
--   cases g
--   simp at h
--   sorry

-- @[simp]
-- theorem evalToFinHTuple_val (f : FinHTupleMap src dst) (i : FinHTuple src) :
--     f i = f.toHTupleMap.eval i.val := rfl

-- @[simp]
-- theorem getElem_val (f : FinHTupleMap src dst) (i : HTuple Nat p) (h) :
--     (f[i]'h) = f.toHTupleMap.eval i := rfl

end FinHTupleMap

end NumLean
