import NumLean.Data.HTuple.Basic
import NumLean.Algebra.Order

namespace NumLean

namespace HTuple

/-- Pointwise zero tuple. -/
def zero {α : Type u} [Zero α] : {p : Profile} → HTuple α p
  | .leaf => .leaf 0
  | .prod _ _ => .prod zero zero

/-- Pointwise one tuple. -/
def one {α : Type u} [One α] : {p : Profile} → HTuple α p
  | .leaf => .leaf 1
  | .prod _ _ => .prod one one

/-- Pointwise addition of hierarchical tuples. -/
def add {α : Type u} [Add α] : {p : Profile} → HTuple α p → HTuple α p → HTuple α p
  | .leaf, .leaf x, .leaf y => .leaf (x + y)
  | .prod _ _, .prod x₀ x₁, .prod y₀ y₁ => .prod (add x₀ y₀) (add x₁ y₁)

/-- Pointwise multiplication of hierarchical tuples. -/
def mul {α : Type u} [Mul α] : {p : Profile} → HTuple α p → HTuple α p → HTuple α p
  | .leaf, .leaf x, .leaf y => .leaf (x * y)
  | .prod _ _, .prod x₀ x₁, .prod y₀ y₁ => .prod (mul x₀ y₀) (mul x₁ y₁)

/-- Pointwise negation of hierarchical tuples. -/
def neg {α : Type u} [Neg α] : {p : Profile} → HTuple α p → HTuple α p
  | .leaf, .leaf x => .leaf (-x)
  | .prod _ _, .prod x₀ x₁ => .prod (neg x₀) (neg x₁)

/-- Pointwise subtraction of hierarchical tuples. -/
def sub {α : Type u} [Sub α] : {p : Profile} → HTuple α p → HTuple α p → HTuple α p
  | .leaf, .leaf x, .leaf y => .leaf (x - y)
  | .prod _ _, .prod x₀ x₁, .prod y₀ y₁ => .prod (sub x₀ y₀) (sub x₁ y₁)

/-- Pointwise scalar multiplication of hierarchical tuples. -/
def smul {R : Type u} {α : Type v} [SMul R α] (r : R) : {p : Profile} → HTuple α p → HTuple α p
  | .leaf, .leaf x => .leaf (r • x)
  | .prod _ _, .prod x₀ x₁ => .prod (smul r x₀) (smul r x₁)

/-- Map a refined tuple to a coarser profile by collapsing each refined subtree. -/
def coarsenMap {α : Type u} {β : Type v} (p : Profile) {q : Profile} (x : HTuple α q)
    (f : {q' : Profile} → HTuple α q' → β) [h : q.Refines p] : HTuple β p :=
  match h, x with
  | .leaf _, x => .leaf (f x)
  | .prod _ _, .prod x₁ x₂ => .prod (coarsenMap _ x₁ f) (coarsenMap _ x₂ f)

/-- Apply `coarsenMap` at every coarsening of the input tuple's profile. -/
def allCoarseningsMap {α : Type u} {β : Type v} {p : Profile} (x : HTuple α p)
    (f : {q : Profile} → HTuple α q → β) : Array (Sigma fun q : Profile => HTuple β q) :=
  match x with
  | .leaf _ => #[⟨.leaf, .leaf (f x)⟩]
  | .prod x₁ x₂ => Id.run do
      let xs₁ := allCoarseningsMap x₁ f
      let xs₂ := allCoarseningsMap x₂ f
      let mut xs : Array (Sigma fun q : Profile => HTuple β q) := #[⟨.leaf, .leaf (f x)⟩]
      for ⟨q₁, y₁⟩ in xs₁ do
        for ⟨q₂, y₂⟩ in xs₂ do
          xs := xs.push ⟨.prod q₁ q₂, .prod y₁ y₂⟩
      return xs

/-- Binary version of `coarsenMap`, collapsing matching refined subtrees. -/
def coarsenMap₂ {α : Type u} {β : Type v} {γ : Type w} (p : Profile) {q : Profile}
    (x : HTuple α q) (y : HTuple β q)
    (f : {q' : Profile} → HTuple α q' → HTuple β q' → γ) [h : q.Refines p] : HTuple γ p :=
  match h, x, y with
  | .leaf _, x, y => .leaf (f x y)
  | .prod _ _, .prod x₁ x₂, .prod y₁ y₂ =>
      .prod (coarsenMap₂ _ x₁ y₁ f) (coarsenMap₂ _ x₂ y₂ f)

/-- Map a coarse tuple to a refined profile by broadcasting leaves over refined subtrees. -/
def refineMap {α : Type u} {β : Type v} (q : Profile) {p : Profile} (x : HTuple α p)
    (f : α → β) [h : q.Refines p] : HTuple β q :=
  match h, x with
  | .leaf q, .leaf x => HTuple.ofFn (p := q) fun _ => f x
  | .prod _ _, .prod x₁ x₂ => .prod (refineMap _ x₁ f) (refineMap _ x₂ f)

/-- Binary version of `refineMap`, broadcasting the left tuple over the refined right tuple. -/
def refineMap₂ {α : Type u} {β : Type v} {γ : Type w} (q : Profile) {p : Profile}
    (x : HTuple α p) (y : HTuple β q) (f : α → β → γ) [h : q.Refines p] : HTuple γ q :=
  match h, x, y with
  | .leaf _, .leaf x, y => y.map (f x)
  | .prod _ _, .prod x₁ x₂, .prod y₁ y₂ =>
      .prod (refineMap₂ _ x₁ y₁ f) (refineMap₂ _ x₂ y₂ f)

/-- Scalar multiplication where the left tuple may have a coarser profile than the right tuple. -/
def refinedSMul {α : Type u} {β : Type v} {p q : Profile} [SMul α β]
    [q.Refines p] (x : HTuple α p) (y : HTuple β q) : HTuple β q :=
  refineMap₂ q x y (· • ·)

instance {α : Type u} [Zero α] {p : Profile} : Zero (HTuple α p) where
  zero := zero

instance {α : Type u} [One α] {p : Profile} : One (HTuple α p) where
  one := one

instance {α : Type u} [Add α] {p : Profile} : Add (HTuple α p) where
  add := add

instance {α : Type u} [Mul α] {p : Profile} : Mul (HTuple α p) where
  mul := mul

instance {α : Type u} [Neg α] {p : Profile} : Neg (HTuple α p) where
  neg := neg

instance {α : Type u} [Sub α] {p : Profile} : Sub (HTuple α p) where
  sub := sub

instance (priority := low) {R : Type u} {α : Type v} [SMul R α] {p : Profile} : SMul R (HTuple α p) where
  smul r x := smul r x

instance {α : Type u} {β : Type v} [SMul α β] {p q : Profile} [q.Refines p] :
    SMul (HTuple α p) (HTuple β q) where
  smul := refinedSMul

/-- The basis tuple whose selected leaf is `1` and all other leaves are `0`. -/
def basis {α : Type u} [Zero α] [One α] : {p : Profile} → Index p → HTuple α p
  | .leaf, .leaf => .leaf 1
  | .prod _ _, .left i => .prod (basis i) 0
  | .prod _ _, .right i => .prod 0 (basis i)

/-- All basis tuples for a profile, arranged with the same profile. -/
def basisTuple {α : Type u} [Zero α] [One α] : (p : Profile) → HTuple (HTuple α p) p
  | .leaf => .leaf (.leaf 1)
  | .prod left right =>
      .prod
        (map (fun x => HTuple.prod x (0 : HTuple α right)) (basisTuple (α := α) left))
        (map (fun x => HTuple.prod (0 : HTuple α left) x) (basisTuple (α := α) right))

@[simp]
theorem zero_leaf {α : Type u} [Zero α] : (0 : HTuple α .leaf) = .leaf 0 := rfl

@[simp]
theorem zero_prod {α : Type u} [Zero α] {p q : Profile} :
    (0 : HTuple α (.prod p q)) = .prod (0 : HTuple α p) (0 : HTuple α q) := rfl

@[simp]
theorem one_leaf {α : Type u} [One α] : (1 : HTuple α .leaf) = .leaf 1 := rfl

@[simp]
theorem one_prod {α : Type u} [One α] {p q : Profile} :
    (1 : HTuple α (.prod p q)) = .prod (1 : HTuple α p) (1 : HTuple α q) := rfl

@[simp]
theorem add_leaf {α : Type u} [Add α] (x y : α) :
    (.leaf x : HTuple α .leaf) + .leaf y = .leaf (x + y) := rfl

@[simp]
theorem add_prod {α : Type u} [Add α] {p q : Profile}
    (x₀ y₀ : HTuple α p) (x₁ y₁ : HTuple α q) :
    (.prod x₀ x₁ : HTuple α (.prod p q)) + .prod y₀ y₁ = .prod (x₀ + y₀) (x₁ + y₁) := rfl

@[simp]
theorem mul_leaf {α : Type u} [Mul α] (x y : α) :
    (.leaf x : HTuple α .leaf) * .leaf y = .leaf (x * y) := rfl

@[simp]
theorem mul_prod {α : Type u} [Mul α] {p q : Profile}
    (x₀ y₀ : HTuple α p) (x₁ y₁ : HTuple α q) :
    (.prod x₀ x₁ : HTuple α (.prod p q)) * .prod y₀ y₁ = .prod (x₀ * y₀) (x₁ * y₁) := rfl

@[simp]
theorem neg_leaf {α : Type u} [Neg α] (x : α) :
    -(.leaf x : HTuple α .leaf) = .leaf (-x) := rfl

@[simp]
theorem neg_prod {α : Type u} [Neg α] {p q : Profile} (x₀ : HTuple α p) (x₁ : HTuple α q) :
    -(.prod x₀ x₁ : HTuple α (.prod p q)) = .prod (-x₀) (-x₁) := rfl

@[simp]
theorem sub_leaf {α : Type u} [Sub α] (x y : α) :
    (.leaf x : HTuple α .leaf) - .leaf y = .leaf (x - y) := rfl

@[simp]
theorem sub_prod {α : Type u} [Sub α] {p q : Profile}
    (x₀ y₀ : HTuple α p) (x₁ y₁ : HTuple α q) :
    (.prod x₀ x₁ : HTuple α (.prod p q)) - .prod y₀ y₁ = .prod (x₀ - y₀) (x₁ - y₁) := rfl

@[simp]
theorem smul_leaf {R : Type u} {α : Type v} [SMul R α] (r : R) (x : α) :
    r • (.leaf x : HTuple α .leaf) = .leaf (r • x) := rfl

@[simp]
theorem smul_prod {R : Type u} {α : Type v} [SMul R α] {p q : Profile}
    (r : R) (x₀ : HTuple α p) (x₁ : HTuple α q) :
    r • (.prod x₀ x₁ : HTuple α (.prod p q)) = .prod (r • x₀) (r • x₁) := rfl

@[simp]
theorem coarsenMap_leaf {α : Type u} {β : Type v} {q : Profile} (x : HTuple α q)
    (f : {q' : Profile} → HTuple α q' → β) [h : q.Refines .leaf] :
    coarsenMap .leaf x f = .leaf (f x) := by
  cases h
  simp [coarsenMap]

@[simp]
theorem coarsenMap_prod {α : Type u} {β : Type v} {p₁ p₂ q₁ q₂ : Profile}
    [q₁.Refines p₁] [q₂.Refines p₂] (x₁ : HTuple α q₁) (x₂ : HTuple α q₂)
    (f : {q' : Profile} → HTuple α q' → β) :
    coarsenMap (.prod p₁ p₂) (.prod x₁ x₂) f =
      .prod (coarsenMap p₁ x₁ f) (coarsenMap p₂ x₂ f) := rfl

@[simp]
theorem coarsenMap₂_leaf {α : Type u} {β : Type v} {γ : Type w} {q : Profile}
    (x : HTuple α q) (y : HTuple β q)
    (f : {q' : Profile} → HTuple α q' → HTuple β q' → γ) [h : q.Refines .leaf] :
    coarsenMap₂ .leaf x y f = .leaf (f x y) := by
  cases h
  simp [coarsenMap₂]

@[simp]
theorem coarsenMap₂_prod {α : Type u} {β : Type v} {γ : Type w} {p₁ p₂ q₁ q₂ : Profile}
    [q₁.Refines p₁] [q₂.Refines p₂] (x₁ : HTuple α q₁) (x₂ : HTuple α q₂)
    (y₁ : HTuple β q₁) (y₂ : HTuple β q₂)
    (f : {q' : Profile} → HTuple α q' → HTuple β q' → γ) :
    coarsenMap₂ (.prod p₁ p₂) (.prod x₁ x₂) (.prod y₁ y₂) f =
      .prod (coarsenMap₂ p₁ x₁ y₁ f) (coarsenMap₂ p₂ x₂ y₂ f) := rfl

@[simp]
theorem refineMap_leaf {α : Type u} {β : Type v} {q : Profile} (x : α) (f : α → β) :
    refineMap q (.leaf x) f = HTuple.ofFn (p := q) (fun _ => f x) := rfl

@[simp]
theorem refineMap_prod {α : Type u} {β : Type v} {p₁ p₂ q₁ q₂ : Profile}
    [q₁.Refines p₁] [q₂.Refines p₂] (x₁ : HTuple α p₁) (x₂ : HTuple α p₂)
    (f : α → β) :
    refineMap (.prod q₁ q₂) (.prod x₁ x₂) f =
      .prod (refineMap q₁ x₁ f) (refineMap q₂ x₂ f) := rfl

@[simp]
theorem refineMap₂_leaf {α : Type u} {β : Type v} {γ : Type w} {q : Profile}
    (x : α) (y : HTuple β q) (f : α → β → γ) :
    refineMap₂ q (.leaf x) y f = y.map (f x) := rfl

@[simp]
theorem refineMap₂_prod {α : Type u} {β : Type v} {γ : Type w} {p₁ p₂ q₁ q₂ : Profile}
    [q₁.Refines p₁] [q₂.Refines p₂] (x₁ : HTuple α p₁) (x₂ : HTuple α p₂)
    (y₁ : HTuple β q₁) (y₂ : HTuple β q₂) (f : α → β → γ) :
    refineMap₂ (.prod q₁ q₂) (.prod x₁ x₂) (.prod y₁ y₂) f =
      .prod (refineMap₂ q₁ x₁ y₁ f) (refineMap₂ q₂ x₂ y₂ f) := rfl

@[simp]
theorem smul_leaf_refined {α : Type u} {β : Type v} {q : Profile} [SMul α β]
    (x : α) (y : HTuple β q) :
    (.leaf x : HTuple α .leaf) • y = y.map (x • ·) := rfl

@[simp]
theorem smul_prod_refined {α : Type u} {β : Type v} [SMul α β]
    {p₁ p₂ q₁ q₂ : Profile} [q₁.Refines p₁] [q₂.Refines p₂]
    (x₁ : HTuple α p₁) (x₂ : HTuple α p₂) (y₁ : HTuple β q₁) (y₂ : HTuple β q₂) :
    (.prod x₁ x₂ : HTuple α (.prod p₁ p₂)) • (.prod y₁ y₂ : HTuple β (.prod q₁ q₂)) =
      .prod (x₁ • y₁) (x₂ • y₂) := rfl

end HTuple

end NumLean
