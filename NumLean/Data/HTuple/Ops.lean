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

instance {α : Type u} [LT α] {p : Profile} : LexLT (HTuple α p) where
  lexLT x y := NumLean.List.lexLT x.toList y.toList

instance {α : Type u} [LT α] {p : Profile} : LexLE (HTuple α p) where
  lexLE x y := NumLean.List.lexLE x.toList y.toList

instance {α : Type u} [LT α] {p : Profile} : ColexLT (HTuple α p) where
  colexLT x y := NumLean.List.colexLT x.toList y.toList

instance {α : Type u} [LT α] {p : Profile} : ColexLE (HTuple α p) where
  colexLE x y := NumLean.List.colexLE x.toList y.toList

instance {α : Type u} [LT α] {p : Profile} : ElementwiseLT (HTuple α p) where
  elementwiseLT x y := NumLean.List.elementwiseLT x.toList y.toList

instance {α : Type u} [LE α] {p : Profile} : ElementwiseLE (HTuple α p) where
  elementwiseLE x y := NumLean.List.elementwiseLE x.toList y.toList

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

end HTuple

end NumLean
