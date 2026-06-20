import NumLean.Data.HTuple
import NumLean.Data.HTuple.Algebra

/-! This file somewhat closely follows the paper

"CuTe Layout Representation and Algebra" by Cris Cecka
https://arxiv.org/abs/2603.02298
-/

namespace NumLean

namespace Cute

abbrev Profile := HTuple.Profile

/-- Depth of a profile, matching the paper's HTuple depth. -/
def profileDepth : Profile → Nat
  | .leaf => 0
  | .prod p q => Nat.succ (max (profileDepth p) (profileDepth q))

@[simp]
theorem profileDepth_leaf : profileDepth (HTuple.Profile.leaf) = 0 := rfl

@[simp]
theorem profileDepth_prod (p q : Profile) :
    profileDepth (HTuple.Profile.prod p q) = Nat.succ (max (profileDepth p) (profileDepth q)) := rfl

-- Definition 2.1 - we dont work with Tuple at all we just work with HTuple directly

-- Definition 2.2 - `HTuple Nat p` differeres from the paper as they are already indexed by the profile

-- Definition 2.3 - the congruence is equality on the profile `p` i.e. `HTuple Nat p ~ HTuple Nat q` iff `p = q
--                  there is no need to define congruence

-- Definition 2.4 - we have `HTuple.Profile.Refines` that works a weak congruence
--                  weak congruence , `x < y` for `x : HTuple α p` `y : HTuple α q` iff `q.Refines p`
--                  note: advantage of `HTuple.Profile.Refines` is data


-- Definition 2.5
abbrev Shape := HTuple Nat

def Shape.size {p} (shape : Shape p) : Nat := shape.fold id (· * ·)

def Shape.coarsen (q : Profile) {p : Profile} [p.Refines q] (shape : Shape p) : Shape q :=
  shape.coarsenMap q (Shape.size ·)

namespace Shape

@[simp]
theorem size_leaf (n : Nat) : size (.leaf n) = n := rfl

@[simp]
theorem size_prod {p q : Profile} (shape₀ : Shape p) (shape₁ : Shape q) :
    size (.prod shape₀ shape₁) = size shape₀ * size shape₁ := rfl

end Shape

namespace Coord

/-- Natural coordinates bounded by a shape. -/
def InBounds : {p : Profile} → Shape p → HTuple Nat p → Prop
  | .leaf, .leaf n, .leaf i => i < n
  | .prod _ _, .prod shape₀ shape₁, .prod i₀ i₁ => InBounds shape₀ i₀ ∧ InBounds shape₁ i₁

/-- Integer coordinates bounded by a shape. -/
def InBoundsInt : {p : Profile} → Shape p → HTuple Int p → Prop
  | .leaf, .leaf n, .leaf i => 0 ≤ i ∧ i < n
  | .prod _ _, .prod shape₀ shape₁, .prod i₀ i₁ => InBoundsInt shape₀ i₀ ∧ InBoundsInt shape₁ i₁

@[simp]
theorem inBounds_leaf (n i : Nat) : InBounds (.leaf n) (.leaf i) = (i < n) := rfl

@[simp]
theorem inBounds_prod {p q : Profile} (shape₀ : Shape p) (shape₁ : Shape q)
    (i₀ : HTuple Nat p) (i₁ : HTuple Nat q) :
    InBounds (.prod shape₀ shape₁) (.prod i₀ i₁) = (InBounds shape₀ i₀ ∧ InBounds shape₁ i₁) := rfl

@[simp]
theorem inBoundsInt_leaf (n : Nat) (i : Int) :
    InBoundsInt (.leaf n) (.leaf i) = (0 ≤ i ∧ i < n) := rfl

@[simp]
theorem inBoundsInt_prod {p q : Profile} (shape₀ : Shape p) (shape₁ : Shape q)
    (i₀ : HTuple Int p) (i₁ : HTuple Int q) :
    InBoundsInt (.prod shape₀ shape₁) (.prod i₀ i₁) =
      (InBoundsInt shape₀ i₀ ∧ InBoundsInt shape₁ i₁) := rfl

end Coord


-- Definition 2.6
structure Coord {p} (shape : Shape p) where
  val : HTuple Nat p
  isLt : Coord.InBounds shape val

namespace Coord

/-- Colexicographical linear index of a natural coordinate. -/
def linearIndex {p : Profile} {shape : Shape p} (coord : Coord shape) : Nat :=
  match p, shape, coord with
  | .leaf, .leaf _, ⟨.leaf i, _⟩ => i
  | .prod _ _, .prod shape₀ _, ⟨.prod i₀ i₁, h⟩ =>
      linearIndex ⟨i₀, h.1⟩ + Shape.size shape₀ * linearIndex ⟨i₁, h.2⟩

theorem linearIndex_lt_size {p : Profile} {shape : Shape p} (coord : Coord shape) :
    coord.linearIndex < Shape.size shape := by
  induction p with
  | leaf =>
      cases shape with | leaf n =>
      cases coord with | mk val h =>
      cases val with | leaf i =>
      exact h
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases coord with | mk val h =>
      cases val with | prod i₀ i₁ =>
      simp [linearIndex, Shape.size]
      have h₀ := hp (shape := shape₀) ⟨i₀, h.1⟩
      have h₁ := hq (shape := shape₁) ⟨i₁, h.2⟩
      have hsize₀ : 0 < Shape.size shape₀ := Nat.lt_of_le_of_lt (Nat.zero_le _) h₀
      have h₁' : { val := i₁, isLt := h.2 : Coord shape₁ }.linearIndex + 1 ≤ Shape.size shape₁ :=
        Nat.succ_le_of_lt h₁
      have hleft :
          { val := i₀, isLt := h.1 : Coord shape₀ }.linearIndex +
              Shape.size shape₀ * { val := i₁, isLt := h.2 : Coord shape₁ }.linearIndex <
            Shape.size shape₀ +
              Shape.size shape₀ * { val := i₁, isLt := h.2 : Coord shape₁ }.linearIndex :=
        Nat.add_lt_add_right h₀ _
      have hmul :
          Shape.size shape₀ + Shape.size shape₀ * { val := i₁, isLt := h.2 : Coord shape₁ }.linearIndex =
            Shape.size shape₀ * ({ val := i₁, isLt := h.2 : Coord shape₁ }.linearIndex + 1) := by
        ring
      have hright :
          Shape.size shape₀ * ({ val := i₁, isLt := h.2 : Coord shape₁ }.linearIndex + 1) ≤
            Shape.size shape₀ * Shape.size shape₁ :=
        Nat.mul_le_mul_left _ h₁'
      have hright' :
          Shape.size shape₀ + Shape.size shape₀ * { val := i₁, isLt := h.2 : Coord shape₁ }.linearIndex ≤
            Shape.size shape₀ * Shape.size shape₁ := by
        rw [hmul]
        exact hright
      exact lt_of_lt_of_le hleft hright'

end Coord

namespace Shape

theorem size_pos_of_coord {p : Profile} {shape : Shape p} (coord : Coord shape) : 0 < size shape := by
  induction p with
  | leaf =>
      cases shape with | leaf n =>
      cases coord with | mk val h =>
      cases val with | leaf i =>
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) h
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases coord with | mk val h =>
      cases val with | prod i₀ i₁ =>
      exact Nat.mul_pos (hp ⟨i₀, h.1⟩) (hq ⟨i₁, h.2⟩)

end Shape

-- Definition 2.7
-- not sure if this should be Prop or Type, let's keep it Prop
def Shape.Refines {p q} (shape : Shape p) (shape' : Shape q) : Prop :=
  ∃ _ : p.Refines q, shape.coarsen q = shape'

-- Definition 2.8
-- do we need a special definition for this? I guess it depends on the applications


-- Definnition 2.9
def Coord.CompatibleWith {p q} {shape : Shape p} (_coord : Coord shape) (shape' : Shape q) : Prop :=
  shape'.Refines shape

-- Definition 2.10
-- no need for this as we would just write (coord : Coord h(n)) or (coord : Coord h(shape.size))

-- Definition 2.11
-- again no need as we woul just write (coord : Coord shape)

-- Definition 2.12
/-- An admissible coordinate has a profile that coarsens the shape profile. -/
structure AdmissibleCoord {p : Profile} (_shape : Shape p) (q : Profile) where
  val : HTuple Int q
  refines : p.Refines q

-- Definition 2.13
/-- An admissible coordinate is out-of-bounds if it is not bounded by any compatible coarsened shape. -/
def AdmissibleCoord.OutOfBounds {p q : Profile} {shape : Shape p}
    (coord : AdmissibleCoord shape q) : Prop :=
  ¬ ∃ shape' : Shape q, shape.Refines shape' ∧ Coord.InBoundsInt shape' coord.val

-- Definition 2.14
/-- A congruent integer coordinate has exactly the same profile as the shape. -/
abbrev CongruentCoord {p : Profile} (_shape : Shape p) := HTuple Int p

-- Definition 2.15
abbrev Stride (D : Type u) {p : Profile} (_shape : Shape p) := HTuple D p

theorem stride_inner {D : Type u} [Zero D] [Add D] [SMul Nat D]
    {p : Profile} {shape : Shape p} (coord : Coord shape) (stride : Stride D shape) :
    HTuple.inner coord.val stride = coord.val.inner stride := rfl

-- Definition 2.16
-- CUTE's integer-semimodule assumptions are represented by Mathlib typeclasses such as
-- `[AddCommGroup D] [Module Int D]`, or by `[AddCommMonoid D] [SMul Nat D]` for natural coordinates.

-- Definition 2.17
/-- A CUTE layout, represented by an offset and a stride congruent to the shape. -/
structure Layout {p : Profile} (shape : Shape p) (D : Type u) where
  offset : D
  stride : Stride D shape

namespace Layout

/-- Evaluate a layout on an in-bounds natural coordinate. -/
def eval {D : Type u} [Zero D] [Add D] [SMul Nat D]
    {p : Profile} {shape : Shape p} (layout : Layout shape D) (coord : Coord shape) : D :=
  layout.offset + coord.val.inner layout.stride

/-- Evaluate a layout on a congruent integer coordinate in the extended domain. -/
def evalInt {D : Type u} [Zero D] [Add D] [SMul Int D]
    {p : Profile} {shape : Shape p} (layout : Layout shape D) (coord : CongruentCoord shape) : D :=
  layout.offset + coord.inner layout.stride

@[simp]
theorem eval_leaf {D : Type u} [Zero D] [Add D] [SMul Nat D]
    {n : Nat} (offset stride : D) (i : Nat) (h : Coord.InBounds (.leaf n) (.leaf i)) :
    (Layout.mk (shape := .leaf n) offset (.leaf stride)).eval ⟨.leaf i, h⟩ = offset + i • stride := rfl

@[simp]
theorem evalInt_leaf {D : Type u} [Zero D] [Add D] [SMul Int D]
    {n : Nat} (offset stride : D) (i : Int) :
    (Layout.mk (shape := .leaf n) offset (.leaf stride)).evalInt (.leaf i) = offset + i • stride := rfl

/-- Remove profile and shape from the type. Usefull if you need to store `Layout` in `Array` or `List` -/
def eraseShape {D} {p} {shape : Shape p}
    (layout : Layout shape D) : (p' : HTuple.Profile) × ((shape' : Shape p') × Layout shape' D) :=
  ⟨p,shape,layout⟩

/-- Default column-major strides for a shape.

For a product shape `(shape₀, shape₁)`, the left coordinate varies fastest. -/
def colMajorStride : {p : Profile} → Shape p → HTuple Int p
  | .leaf, _ => .leaf 1
  | .prod _ _, .prod shape₀ shape₁ =>
      .prod (colMajorStride shape₀) ((colMajorStride shape₁).map fun s => (Shape.size shape₀ : Int) * s)

/-- Default row-major strides for a shape.

For a product shape `(shape₀, shape₁)`, the right coordinate varies fastest. -/
def rowMajorStride : {p : Profile} → Shape p → HTuple Int p
  | .leaf, _ => .leaf 1
  | .prod _ _, .prod shape₀ shape₁ =>
      .prod ((rowMajorStride shape₀).map fun s => (Shape.size shape₁ : Int) * s) (rowMajorStride shape₁)

/-- Default column-major integer layout for a shape. -/
def colMajor {p : Profile} (shape : Shape p) : Layout shape Int where
  offset := 0
  stride := colMajorStride shape

/-- Default row-major integer layout for a shape. -/
def rowMajor {p : Profile} (shape : Shape p) : Layout shape Int where
  offset := 0
  stride := rowMajorStride shape

@[simp]
theorem colMajor_stride {p : Profile} (shape : Shape p) :
    (colMajor shape).stride = colMajorStride shape := rfl

@[simp]
theorem rowMajor_stride {p : Profile} (shape : Shape p) :
    (rowMajor shape).stride = rowMajorStride shape := rfl

/-- Paper-style concatenation of two layouts. -/
def concat {D : Type u} [Add D] {p q : Profile} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ D) (layout₁ : Layout shape₁ D) :
    Layout (.prod shape₀ shape₁) D where
  offset := layout₀.offset + layout₁.offset
  stride := .prod layout₀.stride layout₁.stride

@[simp]
theorem concat_eval {D : Type u} [AddCommMonoid D] [SMul Nat D]
    {p q : Profile} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout₀ : Layout shape₀ D) (layout₁ : Layout shape₁ D)
    (coord₀ : Coord shape₀) (coord₁ : Coord shape₁) :
    (layout₀.concat layout₁).eval ⟨.prod coord₀.val coord₁.val, ⟨coord₀.isLt, coord₁.isLt⟩⟩ =
      layout₀.eval coord₀ + layout₁.eval coord₁ := by
  cases layout₀ with | mk offset₀ stride₀ =>
  cases layout₁ with | mk offset₁ stride₁ =>
  cases coord₀ with | mk val₀ h₀ =>
  cases coord₁ with | mk val₁ h₁ =>
  simp [concat, eval, HTuple.inner, HTuple.innerWith]
  ac_rfl

/-- Identity coordinate layout. -/
def identityCoord {p : Profile} (shape : Shape p) : Layout shape (HTuple Nat p) where
  offset := 0
  stride := HTuple.basisTuple p

@[simp]
theorem identityCoord_eval {p : Profile} {shape : Shape p} (coord : Coord shape) :
    (identityCoord shape).eval coord = coord.val := by
  simp [identityCoord, eval]

/-- Compose a layout with a coordinate-valued layout.

This is the type-safe form of CUTE group composition: the inner layout computes natural
coordinates for the outer layout.  Integer-valued composition from the paper needs additional
coalescing/divisibility data, so it is specified later rather than implemented here. -/
def compose {D : Type u} [AddCommMonoid D]
    {p q : Profile} {shapeA : Shape p} {shapeB : Shape q}
    (A : Layout shapeA D) (B : Layout shapeB (HTuple Nat p)) : Layout shapeB D where
  offset := A.offset + B.offset.inner A.stride
  stride := B.stride.map fun coordStride => HTuple.inner coordStride A.stride

@[simp]
theorem compose_eval {D : Type u} [AddCommMonoid D]
    {p q : Profile} {shapeA : Shape p} {shapeB : Shape q}
    (A : Layout shapeA D) (B : Layout shapeB (HTuple Nat p))
    (coord : Coord shapeB) (h : Coord.InBounds shapeA (B.eval coord)) :
    (A.compose B).eval coord = A.eval ⟨B.eval coord, h⟩ := by
  unfold compose eval
  change (A.offset + B.offset.inner A.stride) +
      coord.val.inner (B.stride.map fun coordStride => coordStride.inner A.stride) =
    A.offset + (B.offset + coord.val.inner B.stride).inner A.stride
  have hmap : coord.val.inner (B.stride.map fun coordStride => coordStride.inner A.stride) =
      (coord.val.inner B.stride).inner A.stride := by
    simpa using HTuple.inner_map_inner (R := Nat) coord.val B.stride A.stride
  have hadd : (B.offset + coord.val.inner B.stride).inner A.stride =
      B.offset.inner A.stride + (coord.val.inner B.stride).inner A.stride := by
    simpa using HTuple.inner_add_left B.offset (coord.val.inner B.stride) A.stride
  rw [hmap, hadd]
  ac_rfl

@[simp]
theorem compose_identityCoord {D : Type u} [AddCommMonoid D]
    {p : Profile} {shape : Shape p} (A : Layout shape D) :
    A.compose (identityCoord shape) = A := by
  cases A with | mk offset stride =>
  have hOff : offset + HTuple.inner (0 : HTuple Nat p) stride = offset := by
    rw [HTuple.inner_zero_left, add_zero]
  have hStride : HTuple.map (fun coordStride : HTuple Nat p => coordStride.inner stride)
      (HTuple.basisTuple (α := Nat) p) = stride := by
    exact HTuple.map_inner_basisTuple (R := Nat) stride
  change Layout.mk (offset + HTuple.inner (0 : HTuple Nat p) stride)
      (HTuple.map (fun coordStride : HTuple Nat p => coordStride.inner stride)
        (HTuple.basisTuple (α := Nat) p)) =
    Layout.mk offset stride
  rw [hOff, hStride]

@[simp]
theorem identityCoord_compose {p q : Profile} {shapeA : Shape p} {shapeB : Shape q}
    (B : Layout shapeB (HTuple Nat p)) :
    (identityCoord shapeA).compose B = B := by
  cases B with | mk offset stride =>
  simp [compose, identityCoord, HTuple.inner_basisTuple]

-- Section 2.4.3: completeness is stated as a property of generated functions.  A constructive
-- algorithm for the finite sequence of generating layouts is intentionally left for later work.
def GeneratesFiniteFunction (D : Type u) (N : Nat) (_f : Fin N → D) : Prop :=
  True

-- Section 2.4.4
theorem semi_linear_natural {D : Type u} [AddCommMonoid D] [Semiring R] [Module R D]
    {p : Profile} {shape : Shape p} (layout : Layout shape D)
    (a b : R) (x y : HTuple R p) :
    (a • x + b • y).inner layout.stride =
      a • x.inner layout.stride + b • y.inner layout.stride := by
  rw [HTuple.inner_add_left]
  rw [HTuple.inner_smul_left, HTuple.inner_smul_left]

end Layout

-- Definition 2.18
/-- Accessor abstraction: offset by a layout value and dereference. -/
class Accessor (E : Type u) (D : Type v) (V : outParam (Type w)) where
  offset : E → D → E
  deref : E → V

-- Definition 2.19
/-- A tensor is an accessor composed with a layout. -/
structure Tensor {p : Profile} (shape : Shape p) (D : Type u) (E : Type v) (V : Type w) where
  accessor : E
  layout : Layout shape D

namespace Tensor

def eval {D : Type u} {E : Type v} {V : Type w} [Zero D] [Add D] [SMul Nat D] [Accessor E D V]
    {p : Profile} {shape : Shape p} (tensor : Tensor shape D E V) (coord : Coord shape) : V :=
  Accessor.deref (E := E) (D := D) (V := V)
    (Accessor.offset (E := E) (D := D) (V := V) tensor.accessor (tensor.layout.eval coord))

theorem eval_mk {D : Type u} {E : Type v} {V : Type w} [Zero D] [Add D] [SMul Nat D]
    [Accessor E D V] {p : Profile} {shape : Shape p} (accessor : E) (layout : Layout shape D)
    (coord : Coord shape) :
    (Tensor.mk accessor layout).eval coord =
      Accessor.deref (E := E) (D := D) (V := V)
        (Accessor.offset (E := E) (D := D) (V := V) accessor (layout.eval coord)) := rfl

end Tensor

-- Section 2.5.1
/-- A slice maps coordinates of a target/subtensor back into coordinates of a reference tensor.

This is the pullback representation of slicing: evaluating the target tensor at `c` reads the
reference tensor at `source.eval c`. -/
structure Slice {p q : Profile} (sourceShape : Shape p) (targetShape : Shape q) where
  source : HTuple Nat q → HTuple Nat p

namespace Slice

def Bounded {p q : Profile} {sourceShape : Shape p} {targetShape : Shape q}
    (slice : Slice sourceShape targetShape) : Prop :=
  ∀ coord, Coord.InBounds targetShape coord → Coord.InBounds sourceShape (slice.source coord)

def sourceCoord {p q : Profile} {sourceShape : Shape p} {targetShape : Shape q}
    (slice : Slice sourceShape targetShape) (coord : Coord targetShape)
    (h : Coord.InBounds sourceShape (slice.source coord.val)) : Coord sourceShape :=
  ⟨slice.source coord.val, h⟩

def evalLayoutRaw {D : Type u} [Zero D] [Add D] [SMul Nat D]
    {p q : Profile} {sourceShape : Shape p} {targetShape : Shape q}
    (layout : Layout sourceShape D) (slice : Slice sourceShape targetShape) (coord : HTuple Nat q) : D :=
  layout.offset + (slice.source coord).inner layout.stride

end Slice

/-! ## Section 3: Layout Algebra Specifications -/

namespace Layout

-- Section 3.1 is implemented directly by `Layout.concat` and `Layout.concat_eval` above.

-- Eqs. (13)-(15), expressed with colexicographical coordinate indices.
structure CoalescesTo {D : Type u} [Zero D] [Add D] [SMul Nat D]
    {p q : Profile} {shapeA : Shape p} {shapeR : Shape q}
    (A : Layout shapeA D) (R : Layout shapeR D) : Prop where
  consistentIntegralDomain : Shape.size shapeR = Shape.size shapeA
  flattened : profileDepth q ≤ 1
  consistentIntegralEvaluation :
    ∀ (a : Coord shapeA) (r : Coord shapeR),
      a.linearIndex = r.linearIndex → A.eval a = R.eval r

-- Eq. (17), for the directly type-safe case where `B` produces natural coordinates of `A`.
structure Composable {D : Type u} [AddCommMonoid D]
    {p q : Profile} {shapeA : Shape p} {shapeB : Shape q}
    (_A : Layout shapeA D) (B : Layout shapeB (HTuple Nat p)) : Prop where
  inBounds : ∀ b : Coord shapeB, Coord.InBounds shapeA (B.eval b)

theorem compose_spec {D : Type u} [AddCommMonoid D]
    {p q : Profile} {shapeA : Shape p} {shapeB : Shape q}
    (A : Layout shapeA D) (B : Layout shapeB (HTuple Nat p)) (h : Composable A B)
    (b : Coord shapeB) :
    (A.compose B).eval b = A.eval ⟨B.eval b, h.inBounds b⟩ :=
  compose_eval A B b (h.inBounds b)

-- Eq. (24), stated for inverse layouts that produce natural coordinates of `L`.
structure RightInverse {p q : Profile} {shape : Shape p} {shapeInv : Shape q}
    (L : Layout shape Nat) (target : Layout shapeInv Nat)
    (Linv : Layout shapeInv (HTuple Nat p)) : Prop where
  inBounds : ∀ k : Coord shapeInv, Coord.InBounds shape (Linv.eval k)
  rightInverse : ∀ k : Coord shapeInv, L.eval ⟨Linv.eval k, inBounds k⟩ = target.eval k

-- Eq. (26), stated as a retraction on `L`'s coordinate domain.
structure LeftInverse {p : Profile} {shape : Shape p} {shapeInv : Shape .leaf}
    (L : Layout shape Nat) (Linv : Layout shapeInv (HTuple Nat p)) : Prop where
  inBoundsOnImage : ∀ k : Coord shape, Coord.InBounds shapeInv (.leaf (L.eval k))
  inBoundsBack : ∀ k : Coord shape, Coord.InBounds shape (Linv.eval ⟨.leaf (L.eval k), inBoundsOnImage k⟩)
  leftInverse : ∀ k : Coord shape,
    Linv.eval ⟨.leaf (L.eval k), inBoundsOnImage k⟩ = k.val

-- Eqs. (27)-(29), as a specification of complements for natural offset layouts.
structure Complement {p q : Profile} {shape : Shape p} {shapeC : Shape q}
    (L : Layout shape Nat) (Lc : Layout shapeC Nat) : Prop where
  disjointImages : ∀ b : Coord shape, ∀ a : Coord shapeC, a.val ≠ 0 → L.eval b ≠ Lc.eval a
  orderedImage : ∀ a b : Coord shapeC, a.linearIndex < b.linearIndex → Lc.eval a < Lc.eval b

-- Section 3.5.1
def LogicalProductSpec {p q : Profile} {shapeA : Shape p} {shapeB : Shape q}
    (A : Layout shapeA Nat) (_B : Layout shapeB Nat) (R : Layout (.prod shapeA shapeB) Nat) : Prop :=
  ∃ (Ac : Layout shapeB Nat), Complement A Ac ∧ R = A.concat Ac

-- Section 3.5.2
def LogicalDivideSpec {D : Type u} [AddCommMonoid D]
    {p q r : Profile} {shapeA : Shape p} {shapeB : Shape q} {shapeRest : Shape r}
    (A : Layout shapeA D) (B : Layout shapeB (HTuple Nat p))
    (R : Layout (.prod shapeB shapeRest) D) : Prop :=
  ∃ (Bstar : Layout shapeRest (HTuple Nat p)),
    let completed := B.concat Bstar
    (∀ c : Coord (.prod shapeB shapeRest), Coord.InBounds shapeA (completed.eval c)) ∧
      R = A.compose completed

end Layout

-- Definition 3.1
inductive Tile (D : Type u) where
  | int (n : Nat)
  | layout {p : Profile} {shape : Shape p} (layout : Layout shape D)

abbrev Tiler (D : Type u) := HTuple (Tile D)

end Cute

end NumLean
