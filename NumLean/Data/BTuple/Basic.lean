import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-!
# Binary tuples with tensor-product and direct-sum structure

`HTuple` describes tree-shaped products only. This is enough for spaces such as
`(ℝⁿ ⊗ ℝᵐ) ⊗ ℝᵏ`, where every internal node is tensor-like: a value contains data from both
children.

`BTuple` adds one more internal node, `Profile.sum`, for direct sums. A profile such as
`(.prod (.prod .leaf .leaf) (.sum .leaf .leaf))` can represent a space shaped like
`(ℝⁿ ⊗ ℝᵐ) ⊗ (ℝᵏ ⊕ ℝˡ)`.

The key distinction is:

* `prod p q` behaves like a tensor/product node. A `BTuple α (p.prod q)` contains a left tuple
  and a right tuple, so both subprofiles are present.
* `sum p q` behaves like a direct-sum/coproduct node. A `BTuple α (p.sum q)` is tagged: it is
  either in the left summand or in the right summand. Only one branch is active at a time.

This affects the API. Product projections `fst` and `snd` are total. Sum injections `inl` and `inr`
build tagged values. Leaf lookup returns `Option α`, because asking for a leaf in the inactive
summand of a direct sum returns `none`.

`Shape` carries concrete dimensions. Products multiply dimensions, matching tensor products:
`dim (V ⊗ W) = dim V * dim W`. Sums add dimensions, matching direct sums:
`dim (V ⊕ W) = dim V + dim W`.
-/

namespace NumLean

namespace BTuple

/-- The structural profile of a binary tuple.

`leaf` is an atomic vector-space factor. `prod p q` represents a tensor/product node and stores
both children in a value. `sum p q` represents a direct sum node and stores exactly one tagged
child in a value. -/
inductive Profile where
  /-- Atomic factor, e.g. `ℝⁿ`. -/
  | leaf
  /-- Tensor/product node, e.g. `V ⊗ W`; values contain both sides. -/
  | prod (p q : Profile)
  /-- Direct-sum node, e.g. `V ⊕ W`; values contain either the left or the right side. -/
  | sum (p q : Profile)
  deriving DecidableEq, Repr

namespace Profile

/-- Number of syntactic leaves in a profile.

For both tensor products and direct sums, this counts leaves in the full expression tree, not just
the leaves active in a particular `BTuple` value. For active leaves of a value, use
`BTuple.activeSize`. -/
@[inline] def size : Profile → Nat
  | .leaf => 1
  | .prod p q => p.size + q.size
  | .sum p q => p.size + q.size

@[simp] theorem size_leaf : Profile.leaf.size = 1 := rfl

@[simp] theorem size_prod (p q : Profile) : (Profile.prod p q).size = p.size + q.size := rfl

@[simp] theorem size_sum (p q : Profile) : (Profile.sum p q).size = p.size + q.size := rfl

theorem size_pos (p : Profile) : 0 < p.size := by
  induction p with
  | leaf => simp [size]
  | prod p _ hp _ => simp [size, Nat.add_pos_left hp]
  | sum p _ hp _ => simp [size, Nat.add_pos_left hp]

end Profile

/-- Concrete dimensions for a binary tuple profile.

The constructors mirror the algebraic dimension rules: a tensor/product shape multiplies its child
sizes, while a direct-sum shape adds them. -/
inductive Shape : Profile → Type where
  /-- Dimension of an atomic factor, e.g. `ℝⁿ`. -/
  | leaf (n : Nat) : Shape .leaf
  /-- Shape of `V ⊗ W`; dimensions multiply in `numel`. -/
  | prod {p q} (s : Shape p) (t : Shape q) : Shape (p.prod q)
  /-- Shape of `V ⊕ W`; dimensions add in `numel`. -/
  | sum {p q} (s : Shape p) (t : Shape q) : Shape (p.sum q)

namespace Shape

/-- Number of scalar coordinates represented by a shape.

This is the dimension of the modeled finite-dimensional space: tensor/product nodes multiply and
direct-sum nodes add. -/
@[inline] def numel : Shape p → Nat
  | .leaf n => n
  | .prod s t => s.numel * t.numel
  | .sum s t => s.numel + t.numel

@[simp] theorem numel_leaf (n : Nat) : numel (Shape.leaf n) = n := rfl

@[simp] theorem numel_prod {p q : Profile} (s : Shape p) (t : Shape q) :
    numel (Shape.prod s t) = s.numel * t.numel := rfl

@[simp] theorem numel_sum {p q : Profile} (s : Shape p) (t : Shape q) :
    numel (Shape.sum s t) = s.numel + t.numel := rfl

end Shape

end BTuple

open BTuple in
/-- A binary tuple with profile-indexed leaves, products, and tagged sums.

Compared with `HTuple`, the product constructor has the same meaning: it stores data for both
subprofiles. The two sum constructors are different: they are injections into a direct sum. A value
of profile `p.sum q` is either `.sumLeft a q` or `.sumRight p b`, never both. -/
inductive BTuple (α : Type u) : Profile → Type u where
  /-- Leaf value. -/
  | leaf (a : α) : BTuple α .leaf
  /-- Product/tensor value containing both factors. -/
  | prod {p q} (a : BTuple α p) (b : BTuple α q) : BTuple α (p.prod q)
  /-- Left injection into a direct sum. -/
  | sumLeft {p} (a : BTuple α p) (q : Profile) : BTuple α (p.sum q)
  /-- Right injection into a direct sum. -/
  | sumRight (p : Profile) {q} (a : BTuple α q) : BTuple α (p.sum q)
  deriving DecidableEq, Repr

namespace BTuple

/-- Extract the scalar from a leaf tuple. -/
@[coe]
def toScalar (x : BTuple α .leaf) : α :=
  match x with
  | .leaf a => a

instance : CoeOut (BTuple α .leaf) α := ⟨toScalar⟩
instance : Coe α (BTuple α .leaf) := ⟨.leaf⟩

@[simp] theorem leaf_toScalar (a : α) : (BTuple.leaf a).toScalar = a := rfl

@[simp] theorem leaf_toScalar_eta (x : BTuple α .leaf) : BTuple.leaf x.toScalar = x := by
  cases x
  rfl

@[simp] theorem coe_leaf (a : α) : ((BTuple.leaf a : BTuple α .leaf) : α) = a := rfl

@[simp] theorem leaf_coe (x : BTuple α .leaf) : (BTuple.leaf (x : α) : BTuple α .leaf) = x := by
  cases x
  rfl

theorem toScalar_injective : Function.Injective (toScalar : BTuple α .leaf → α) := by
  intro x y h
  cases x
  cases y
  simp_all

/-- Map a function over every present leaf of a binary tuple.

Products recurse through both sides. Direct sums preserve their tag and recurse only through the
active branch. -/
@[inline, specialize] def map {α : Type u} {β : Type v} (f : α → β) :
    {p : Profile} → BTuple α p → BTuple β p
  | .leaf, .leaf a => .leaf (f a)
  | .prod _ _, .prod a b => .prod (map f a) (map f b)
  | .sum _ _, .sumLeft a q => .sumLeft (map f a) q
  | .sum _ _, .sumRight p b => .sumRight p (map f b)

/-- Combine two binary tuples with matching profile and active sum branch.

For product nodes this behaves like `HTuple.map₂`, combining both children. For direct sums the tags
must agree. If one value lies in the left summand and the other lies in the right summand, there is
no leafwise pairing, so the result is `none`. -/
@[inline, specialize] def map₂ {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) :
    {p : Profile} → BTuple α p → BTuple β p → Option (BTuple γ p)
  | .leaf, .leaf a, .leaf b => some (.leaf (f a b))
  | .prod _ _, .prod a₀ a₁, .prod b₀ b₁ => do
      let c₀ ← map₂ f a₀ b₀
      let c₁ ← map₂ f a₁ b₁
      return .prod c₀ c₁
  | .sum _ _, .sumLeft a q, .sumLeft b _ => Option.map (fun c => .sumLeft c q) (map₂ f a b)
  | .sum _ _, .sumRight p a, .sumRight _ b => Option.map (fun c => .sumRight p c) (map₂ f a b)
  | .sum _ _, _, _ => none

abbrev zipWith := @map₂

/-- Fold a binary tuple using operations for leaves, products, and direct sums.

The `prod` argument combines the two recursive results at tensor/product nodes. The `sumLeft` and
`sumRight` arguments observe which summand is active and receive the inactive profile so callers can
preserve type-level shape information if needed. -/
@[inline, specialize] def fold {α : Type u} {β : Type v}
    (leaf : α → β) (prod : β → β → β) (sumLeft : β → Profile → β)
    (sumRight : Profile → β → β) : {p : Profile} → BTuple α p → β
  | .leaf, .leaf a => leaf a
  | .prod _ _, .prod a b => prod (fold leaf prod sumLeft sumRight a) (fold leaf prod sumLeft sumRight b)
  | .sum _ _, .sumLeft a q => sumLeft (fold leaf prod sumLeft sumRight a) q
  | .sum _ _, .sumRight p b => sumRight p (fold leaf prod sumLeft sumRight b)

/-- Fold all present leaves into an additive monoid-like target.

Product nodes add contributions from both sides. Sum nodes contribute only the active summand. -/
@[inline, specialize] def foldMap {α : Type u} {β : Type v} [Zero β] [Add β]
    (f : α → β) {p : Profile} (x : BTuple α p) : β :=
  x.fold f (· + ·) (fun x _ => x) (fun _ x => x)

/-- Number of present leaves in a binary tuple value.

This differs from `Profile.size` at direct sums. The profile `p.sum q` contains all leaves of `p`
and `q` syntactically, but a value has only the active branch present. -/
@[inline] def activeSize : {p : Profile} → BTuple α p → Nat
  | .leaf, .leaf _ => 1
  | .prod _ _, .prod a b => a.activeSize + b.activeSize
  | .sum _ _, .sumLeft a _ => a.activeSize
  | .sum _ _, .sumRight _ b => b.activeSize

/-- Leaf values present in a binary tuple, in left-to-right order.

For products this concatenates both sides. For sums this lists only the active summand. -/
@[inline] def toList {α : Type u} : {p : Profile} → BTuple α p → List α
  | .leaf, .leaf a => [a]
  | .prod _ _, .prod a b => a.toList ++ b.toList
  | .sum _ _, .sumLeft a _ => a.toList
  | .sum _ _, .sumRight _ b => b.toList

@[simp] theorem length_toList {α : Type u} : {p : Profile} → (x : BTuple α p) → x.toList.length = x.activeSize
  | .leaf, .leaf _ => rfl
  | .prod _ _, .prod a b => by simp [toList, activeSize, length_toList a, length_toList b]
  | .sum _ _, .sumLeft a _ => length_toList a
  | .sum _ _, .sumRight _ b => length_toList b

/-- Remove `Profile` from the type. Useful if you need to store `BTuple` in `Array` or `List`. -/
def eraseProfile {α p} (x : BTuple α p) : (p' : BTuple.Profile) × BTuple α p' := ⟨p, x⟩

/-- Left projection from a product-profile tuple.

This is total because a product/tensor value contains both children. -/
@[inline] def fst {α : Type u} {p q : Profile} : BTuple α (.prod p q) → BTuple α p
  | .prod a _ => a

/-- Right projection from a product-profile tuple.

This is total because a product/tensor value contains both children. -/
@[inline] def snd {α : Type u} {p q : Profile} : BTuple α (.prod p q) → BTuple α q
  | .prod _ b => b

/-- Left injection into a sum-profile tuple.

This is the tuple-level analogue of the canonical map `V → V ⊕ W`. -/
@[inline] def inl {α : Type u} {p : Profile} (a : BTuple α p) (q : Profile) : BTuple α (.sum p q) :=
  .sumLeft a q

/-- Right injection into a sum-profile tuple.

This is the tuple-level analogue of the canonical map `W → V ⊕ W`. -/
@[inline] def inr {α : Type u} (p : Profile) {q : Profile} (b : BTuple α q) : BTuple α (.sum p q) :=
  .sumRight p b

@[simp] theorem fst_prod {α : Type u} {p q : Profile} (a : BTuple α p) (b : BTuple α q) :
    fst (.prod a b) = a := rfl

@[simp] theorem snd_prod {α : Type u} {p q : Profile} (a : BTuple α p) (b : BTuple α q) :
    snd (.prod a b) = b := rfl

@[simp] theorem map_leaf {α : Type u} {β : Type v} (f : α → β) (a : α) :
    map f (.leaf a) = .leaf (f a) := rfl

@[simp] theorem map_prod {α : Type u} {β : Type v} (f : α → β)
    {p q : Profile} (a : BTuple α p) (b : BTuple α q) :
    map f (.prod a b) = .prod (map f a) (map f b) := rfl

@[simp] theorem map_sumLeft {α : Type u} {β : Type v} (f : α → β)
    {p : Profile} (a : BTuple α p) (q : Profile) :
    map f (.sumLeft a q) = .sumLeft (map f a) q := rfl

@[simp] theorem map_sumRight {α : Type u} {β : Type v} (f : α → β)
    (p : Profile) {q : Profile} (b : BTuple α q) :
    map f (.sumRight p b) = .sumRight p (map f b) := rfl

@[simp] theorem map_map {α : Type u} {β : Type v} {γ : Type w}
    (g : β → γ) (f : α → β) {p : Profile} (x : BTuple α p) :
    map g (map f x) = map (fun a => g (f a)) x := by
  induction p with
  | leaf => cases x; rfl
  | prod _ _ hp hq => cases x; simp [hp, hq]
  | sum _ _ hp hq => cases x <;> simp [hp, hq]

@[simp] theorem map_id {α : Type u} {p : Profile} (x : BTuple α p) : map id x = x := by
  induction p with
  | leaf => cases x; rfl
  | prod _ _ hp hq => cases x; simp [hp, hq]
  | sum _ _ hp hq => cases x <;> simp [hp, hq]

@[simp] theorem map_id_fun {α : Type u} {p : Profile} (x : BTuple α p) :
    map (fun a => a) x = x := by
  simpa only [id_eq] using (map_id x)

@[simp] theorem toList_leaf {α : Type u} (a : α) : toList (.leaf a) = [a] := rfl

@[simp] theorem toList_prod {α : Type u} {p q : Profile} (a : BTuple α p) (b : BTuple α q) :
    toList (.prod a b) = a.toList ++ b.toList := rfl

@[simp] theorem toList_sumLeft {α : Type u} {p : Profile} (a : BTuple α p) (q : Profile) :
    toList (.sumLeft a q) = a.toList := rfl

@[simp] theorem toList_sumRight {α : Type u} (p : Profile) {q : Profile} (b : BTuple α q) :
    toList (.sumRight p b) = b.toList := rfl

/-- A selector for a leaf position in a binary profile.

For product/tensor nodes, `left` and `right` select a leaf in one of the two factors. For direct-sum
nodes, `sumLeft` and `sumRight` select a leaf in one of the two summands. A selector can name an
inactive summand of a particular value; in that case `get` returns `none`. -/
inductive Index : Profile → Type where
  /-- The unique leaf selector for `.leaf`. -/
  | leaf : Index .leaf
  /-- Select a leaf in the left side of a product/tensor node. -/
  | left {p q : Profile} : Index p → Index (.prod p q)
  /-- Select a leaf in the right side of a product/tensor node. -/
  | right {p q : Profile} : Index q → Index (.prod p q)
  /-- Select a leaf in the left summand of a direct-sum node. -/
  | sumLeft {p q : Profile} : Index p → Index (.sum p q)
  /-- Select a leaf in the right summand of a direct-sum node. -/
  | sumRight {p q : Profile} : Index q → Index (.sum p q)
  deriving DecidableEq, Repr

namespace Index

/-- Convert a binary tuple leaf selector to a flat `Fin p.size`.

Both `prod` and `sum` profiles are flattened left-to-right. This enumerates syntactic leaf
positions, not only leaves active in a particular direct-sum value. -/
@[inline] def toFin : {p : Profile} → Index p → Fin p.size
  | .leaf, .leaf => ⟨0, by simp [Profile.size]⟩
  | .prod _ _, .left i => ⟨i.toFin.1, Nat.lt_of_lt_of_le i.toFin.2 (Nat.le_add_right _ _)⟩
  | .prod p _, .right i => ⟨p.size + i.toFin.1, Nat.add_lt_add_left i.toFin.2 p.size⟩
  | .sum _ _, .sumLeft i => ⟨i.toFin.1, Nat.lt_of_lt_of_le i.toFin.2 (Nat.le_add_right _ _)⟩
  | .sum p _, .sumRight i => ⟨p.size + i.toFin.1, Nat.add_lt_add_left i.toFin.2 p.size⟩

end Index

/-- Build a binary tuple by giving values for every leaf of products, choosing left for sums.

Unlike `HTuple.ofFn`, this cannot populate both sides of a direct sum: a direct-sum value must pick
one tag. The default choice here is the left summand. If you need a right-summand value, use
`BTuple.inr` or `BTuple.sumRight` directly. -/
@[inline, specialize] def ofFn {α : Type u} : {p : Profile} → (Index p → α) → BTuple α p
  | .leaf, f => .leaf (f .leaf)
  | .prod _ _, f => .prod (ofFn fun i => f (.left i)) (ofFn fun i => f (.right i))
  | .sum _ q, f => .sumLeft (ofFn fun i => f (.sumLeft i)) q

/-- Read a leaf selected by `BTuple.Index`.

For product/tensor nodes this is total along both sides. For direct-sum nodes this returns `some`
only when the selector follows the active tag; selectors into the inactive summand return `none`. -/
@[inline] def get {α : Type u} : {p : Profile} → BTuple α p → Index p → Option α
  | .leaf, .leaf a, .leaf => some a
  | .prod _ _, .prod a _, .left i => a.get i
  | .prod _ _, .prod _ b, .right i => b.get i
  | .sum _ _, .sumLeft a _, .sumLeft i => a.get i
  | .sum _ _, .sumLeft _ _, .sumRight _ => none
  | .sum _ _, .sumRight _ _, .sumLeft _ => none
  | .sum _ _, .sumRight _ b, .sumRight i => b.get i

/-- Replace a leaf selected by `BTuple.Index`.

For products, replacement recurses into the selected child. For sums, replacement only affects the
active summand. A request to replace a leaf in the inactive summand leaves the value unchanged. -/
@[inline] def set {α : Type u} : {p : Profile} → BTuple α p → Index p → α → BTuple α p
  | .leaf, .leaf _, .leaf, value => .leaf value
  | .prod _ _, .prod a b, .left i, value => .prod (a.set i value) b
  | .prod _ _, .prod a b, .right i, value => .prod a (b.set i value)
  | .sum _ _, .sumLeft a q, .sumLeft i, value => .sumLeft (a.set i value) q
  | .sum _ _, .sumLeft a q, .sumRight _, _ => .sumLeft a q
  | .sum _ _, .sumRight p b, .sumLeft _, _ => .sumRight p b
  | .sum _ _, .sumRight p b, .sumRight i, value => .sumRight p (b.set i value)

/-- Modify a leaf selected by `BTuple.Index`.

Inactive direct-sum branches are ignored, so modifying an inactive selector leaves the tuple
unchanged. -/
@[inline, specialize] def modify {α : Type u} {p : Profile}
    (x : BTuple α p) (i : Index p) (f : α → α) : BTuple α p :=
  match x.get i with
  | some a => x.set i (f a)
  | none => x

@[simp] theorem get_leaf {α : Type u} (a : α) : get (.leaf a) .leaf = some a := rfl

@[simp] theorem get_prod_left {α : Type u} {p q : Profile} (a : BTuple α p) (b : BTuple α q)
    (i : Index p) : get (.prod a b) (.left i) = a.get i := rfl

@[simp] theorem get_prod_right {α : Type u} {p q : Profile} (a : BTuple α p) (b : BTuple α q)
    (i : Index q) : get (.prod a b) (.right i) = b.get i := rfl

@[simp] theorem get_sumLeft_active {α : Type u} {p q : Profile} (a : BTuple α p) (i : Index p) :
    get (.sumLeft a q) (.sumLeft i) = a.get i := rfl

@[simp] theorem get_sumLeft_inactive {α : Type u} {p q : Profile} (a : BTuple α p) (i : Index q) :
    get (.sumLeft a q) (.sumRight i) = none := rfl

@[simp] theorem get_sumRight_inactive {α : Type u} {p q : Profile} (b : BTuple α q) (i : Index p) :
    get (.sumRight p b) (.sumLeft i) = none := rfl

@[simp] theorem get_sumRight_active {α : Type u} {p q : Profile} (b : BTuple α q) (i : Index q) :
    get (.sumRight p b) (.sumRight i) = b.get i := rfl

@[simp] theorem get_map {α : Type u} {β : Type v} (f : α → β) {p : Profile}
    (x : BTuple α p) (i : Index p) :
    (map f x).get i = Option.map f (x.get i) := by
  induction p with
  | leaf => cases x; cases i; rfl
  | prod _ _ hp hq => cases x; cases i <;> simp [hp, hq]
  | sum _ _ hp hq => cases x <;> cases i <;> simp [hp, hq]

@[simp] theorem set_leaf {α : Type u} (old value : α) : set (.leaf old) .leaf value = .leaf value := rfl

end BTuple

end NumLean
