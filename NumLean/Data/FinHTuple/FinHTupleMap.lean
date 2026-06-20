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

/-- Identity bounded affine map. -/
def id (src : HTuple Nat p) : FinHTupleMap src src where
  toHTupleMap := HTupleMap.id p
  inBounds := by
    intro i hi
    simpa using hi

/-- Alias for `id`. -/
def identity (src : HTuple Nat p) : FinHTupleMap src src :=
  id src

/-- Compose bounded affine maps. -/
def comp {mid : HTuple Nat q} {r : HTuple.Profile} {dst : HTuple Nat r}
    (g : FinHTupleMap mid dst) (f : FinHTupleMap src mid) : FinHTupleMap src dst where
  toHTupleMap := HTupleMap.comp g.toHTupleMap f.toHTupleMap
  inBounds := by
    intro i hi
    sorry

/-- Compose bounded affine maps when the inner map is known to land in the outer source. -/
def compCast {mid outerSrc : HTuple Nat q} {r : HTuple.Profile} {dst : HTuple Nat r}
    (g : FinHTupleMap outerSrc dst) (f : FinHTupleMap src mid)
    (hcast : ∀ i : HTuple Nat p, i <ₑ src → f.toHTupleMap.eval i <ₑ outerSrc) :
    FinHTupleMap src dst where
  toHTupleMap := HTupleMap.comp g.toHTupleMap f.toHTupleMap
  inBounds := by
    intro i hi
    sorry

/-- Project the left component of the bounded destination. -/
def fst {r : HTuple.Profile} {dst' : HTuple Nat r}
    (f : FinHTupleMap src (HTuple.prod dst dst')) : FinHTupleMap src dst where
  toHTupleMap := HTupleMap.fst f.toHTupleMap
  inBounds := by
    intro i hi
    sorry

/-- Project the right component of the bounded destination. -/
def snd {r : HTuple.Profile} {dst' : HTuple Nat r}
    (f : FinHTupleMap src (HTuple.prod dst' dst)) : FinHTupleMap src dst where
  toHTupleMap := HTupleMap.snd f.toHTupleMap
  inBounds := by
    intro i hi
    sorry

/-- Pair two bounded affine maps with the same source. -/
def prod {r : HTuple.Profile} {dst' : HTuple Nat r}
    (f : FinHTupleMap src dst) (g : FinHTupleMap src dst') :
    FinHTupleMap src (HTuple.prod dst dst') where
  toHTupleMap := HTupleMap.prod f.toHTupleMap g.toHTupleMap
  inBounds := by
    intro i hi
    sorry

/-- Constant bounded affine map. -/
def const (src : HTuple Nat p) {dst : HTuple Nat q} (x : HTuple Nat q) (hx : x <ₑ dst) :
    FinHTupleMap src dst where
  toHTupleMap := HTupleMap.const p x
  inBounds := by
    intro i hi
    sorry

/-- Linearize the bounded destination of a map into its row-major flat index. -/
def linearize (f : FinHTupleMap src dst) : FinHTupleMap src h(dst.numel) where
  toHTupleMap := HTupleMap.comp (HTupleMap.linearize dst) f.toHTupleMap
  inBounds := by
    intro i hi
    sorry

/-- Raw evaluation of a bounded affine map on an unbounded tuple. -/
@[coe]
def eval (f : FinHTupleMap src dst) (i : HTuple Nat p) : HTuple Nat q := f.toHTupleMap.eval i

/-- Raw evaluation of a bounded affine map on an unbounded tuple. -/
abbrev evalRaw (f : FinHTupleMap src dst) (i : HTuple Nat p) : HTuple Nat q :=
  f.eval i

/-- Evaluate a bounded affine map on a bounded tuple, keeping the bounded output type. -/
def evalFin (f : FinHTupleMap src dst) (i : FinHTuple src) : FinHTuple dst :=
  ⟨f.evalRaw i.val, f.inBounds i.val i.isLt⟩

instance : CoeFun (FinHTupleMap src dst) (fun _ => HTuple Nat p → HTuple Nat q) := ⟨eval⟩

instance : GetElem (FinHTupleMap src dst) (HTuple Nat p) (FinHTuple dst) (fun _ i => i <ₑ src) where
  getElem f i h := f.evalFin ⟨i, h⟩

@[simp]
theorem evalFin_val (f : FinHTupleMap src dst) (i : FinHTuple src) :
    (f.evalFin i).val = f.evalRaw i.val := rfl

@[simp]
theorem getElem_val (f : FinHTupleMap src dst) (i : HTuple Nat p) (h : i <ₑ src) :
    (f[i]'h).val = f.evalRaw i := rfl

@[simp]
theorem getElem_isLt (f : FinHTupleMap src dst) (i : HTuple Nat p) (h : i <ₑ src) :
    (f[i]'h).isLt = f.inBounds i h := rfl

@[grind ←, grind_htuple_order ←]
theorem eval_lt (f : FinHTupleMap src dst) (i : HTuple Nat p) : i <ₑ src → f i <ₑ dst := f.2 i

/-- A bounded map has no collisions on its bounded domain. -/
def Injective (f : FinHTupleMap src dst) : Prop :=
  Function.Injective fun i : FinHTuple src => f i

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
  sorry

@[simp, grind ←, grind_htuple_order ←]
theorem mem_range_eval {f : FinHTupleMap src dst} {i : FinHTuple src} : f i ∈ f.range := by
  simp [range]

@[grind →, grind_htuple_order →]
theorem mem_rangeNat_lt {f : FinHTupleMap src h(m)} {i : Nat} (h : i ∈ f.rangeNat) : i < m := by
  rcases h with ⟨j, rfl⟩
  sorry

@[simp, grind ←, grind_htuple_order ←]
theorem mem_rangeNat_eval {m} {f : FinHTupleMap src h(m)} {i : FinHTuple src} :
    (f i : Nat) ∈ f.rangeNat := by
  simp [rangeNat]

@[grind _=_, grind_htuple_order _=_]
theorem mem_range_iff_mem_rangeNat
    {p} {src : HTuple Nat p}
    (map : FinHTupleMap src h(n)) (i : Nat) :
    h(i) ∈ map.range ↔ i ∈ map.rangeNat := by sorry

open Function
@[grind ←, grind_htuple_order ←]
theorem invFun_lt_src (f : FinHTupleMap src dst) (i : HTuple Nat q) (hi : i ∈ f.range) :
    (invFun f i) <ₑ src := by
  let f' : FinHTuple src → FinHTuple dst := fun i => ⟨f i, f.2 i i.2⟩
  have ⟨j, hj⟩ := hi
  have : Nonempty (FinHTuple src) := .intro j
  have h : ∀ x : FinHTuple src, invFun f (f x) = invFun f' (f' x) := by
    sorry
  simp[← hj, h]
  grind only [grind_htuple_order]

@[grind ←, grind_htuple_order ←]
theorem invFun_lt_src_nat (f : FinHTupleMap src h(n)) (i : Nat) (hi : i ∈ f.rangeNat) :
    (invFun f i) <ₑ src := by
  fail_if_success grind only [grind_htuple_order]
  have : h(i) ∈ f.range := by grind only [grind_htuple_order]
  simp
  grind only [grind_htuple_order]

noncomputable
def rangeInv (f : FinHTupleMap src dst) (i : HTuple Nat q) (h : i ∈ f.range) : FinHTuple src :=
  Classical.choose h

open Function in
theorem eval_invFun (f : FinHTupleMap src dst) (i : HTuple Nat q) (h : i ∈ Set.range f) :
    f (invFun f i) = i := by
  apply Function.invFun_eq h

theorem eval_rangeInv (f : FinHTupleMap src dst) (i : HTuple Nat q) (h : i ∈ f.range) :
    f (f.rangeInv i h) = i := by
  exact Classical.choose_spec h

theorem rangeInv_eval (f : FinHTupleMap src dst) (i : FinHTuple src) (h : f.Injective) :
    f.rangeInv (f i) (by simp) = i := by
  apply h
  exact f.eval_rangeInv (f i) (by simp)

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
