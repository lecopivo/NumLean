import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

set_option linter.unnecessarySimpa false

namespace NumLean

namespace HTuple

/-- The structural profile of a hierarchical tuple. -/
inductive Profile where
  | leaf
  | prod (left right : Profile)
  deriving DecidableEq, Repr

namespace Profile

/-- Number of leaves in a profile. -/
def size : Profile → Nat
  | .leaf => 1
  | .prod left right => left.size + right.size

@[simp]
theorem size_leaf : Profile.leaf.size = 1 := rfl

@[simp]
theorem size_prod (left right : Profile) :
    (Profile.prod left right).size = left.size + right.size := rfl

theorem size_pos (p : Profile) : 0 < p.size := by
  induction p with
  | leaf => simp [size]
  | prod left _ hleft _ => simp [size, Nat.add_pos_left hleft]

end Profile

end HTuple

/-- A hierarchical tuple with profile-indexed leaves. -/
inductive HTuple (α : Type u) : HTuple.Profile → Type u where
  | leaf (value : α) : HTuple α .leaf
  | prod {left right : HTuple.Profile} (fst : HTuple α left) (snd : HTuple α right) :
      HTuple α (.prod left right)
  deriving Repr

namespace HTuple

/-- Types that can be converted to a homogeneous hierarchical tuple. -/
class ToHTuple (P : Type u) (α : outParam (Type v)) (p : outParam Profile) where
  toHTuple : P → HTuple α p

export ToHTuple (toHTuple)

instance (priority := low) {α : Type u} : ToHTuple α α .leaf where
  toHTuple x := .leaf x

instance {P : Type u} {Q : Type v} {α : Type w} {p q : Profile}
    [ToHTuple P α p] [ToHTuple Q α q] : ToHTuple (P × Q) α (.prod p q) where
  toHTuple
    | (x, y) => HTuple.prod (toHTuple x) (toHTuple y)

/-- Map a function over every leaf of a hierarchical tuple. -/
def map {α : Type u} {β : Type v} (f : α → β) : {p : Profile} → HTuple α p → HTuple β p
  | .leaf, .leaf value => .leaf (f value)
  | .prod _ _, .prod fst snd => .prod (map f fst) (map f snd)

/-- Combine two hierarchical tuples leafwise. -/
def map₂ {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) :
    {p : Profile} → HTuple α p → HTuple β p → HTuple γ p
  | .leaf, .leaf a, .leaf b => .leaf (f a b)
  | .prod _ _, .prod a₀ a₁, .prod b₀ b₁ => .prod (map₂ f a₀ b₀) (map₂ f a₁ b₁)

abbrev zipWith := @map₂

/-- Fold a hierarchical tuple using one operation for leaves and one for products. -/
def fold {α : Type u} {β : Type v} (leaf : α → β) (prod : β → β → β) :
    {p : Profile} → HTuple α p → β
  | .leaf, .leaf value => leaf value
  | .prod _ _, .prod fst snd => prod (fold leaf prod fst) (fold leaf prod snd)

/-- Fold a hierarchical tuple into an additive monoid-like target. -/
def foldMap {α : Type u} {β : Type v} [Zero β] [Add β] (f : α → β) {p : Profile}
    (x : HTuple α p) : β :=
  x.fold f (· + ·)

/-- Sum a leafwise operation over two hierarchical tuples of the same profile. -/
def innerWith {α : Type u} {β : Type v} {γ : Type w} [Zero γ] [Add γ]
    (f : α → β → γ) : {p : Profile} → HTuple α p → HTuple β p → γ
  | .leaf, .leaf a, .leaf b => f a b
  | .prod _ _, .prod x₀ x₁, .prod y₀ y₁ => innerWith f x₀ y₀ + innerWith f x₁ y₁

/-- Natural semimodule inner product over matching hierarchical tuples. -/
def inner {α : Type u} {β : Type v} [Zero β] [Add β] [SMul α β] {p : Profile}
    (idx : HTuple α p) (stride : HTuple β p) : β :=
  innerWith (fun n d => n • d) idx stride

/-- The leaf values of a hierarchical tuple in left-to-right order. -/
def toList {α : Type u} : {p : Profile} → HTuple α p → List α
  | .leaf, .leaf value => [value]
  | .prod _ _, .prod fst snd => fst.toList ++ snd.toList

@[simp]
theorem map_leaf {α : Type u} {β : Type v} (f : α → β) (value : α) :
    map f (.leaf value) = .leaf (f value) := rfl

@[simp]
theorem map_prod {α : Type u} {β : Type v} (f : α → β)
    {p q : Profile} (fst : HTuple α p) (snd : HTuple α q) :
    map f (.prod fst snd) = .prod (map f fst) (map f snd) := rfl

@[simp]
theorem map_map {α : Type u} {β : Type v} {γ : Type w}
    (g : β → γ) (f : α → β) {p : Profile} (x : HTuple α p) :
    map g (map f x) = map (fun a => g (f a)) x := by
  induction p with
  | leaf =>
      cases x with | leaf value => rfl
  | prod p q hp hq =>
      cases x with | prod fst snd =>
      simp [hp, hq]

@[simp]
theorem map₂_leaf {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (a : α) (b : β) :
    map₂ f (.leaf a) (.leaf b) = .leaf (f a b) := rfl

@[simp]
theorem map₂_prod {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ)
    {p q : Profile} (a₀ : HTuple α p) (a₁ : HTuple α q) (b₀ : HTuple β p) (b₁ : HTuple β q) :
    map₂ f (.prod a₀ a₁) (.prod b₀ b₁) = .prod (map₂ f a₀ b₀) (map₂ f a₁ b₁) := rfl

@[simp]
theorem toList_leaf {α : Type u} (value : α) : toList (.leaf value) = [value] := rfl

@[simp]
theorem toList_prod {α : Type u} {p q : Profile} (fst : HTuple α p) (snd : HTuple α q) :
    toList (.prod fst snd) = fst.toList ++ snd.toList := rfl

/-- A selector for one leaf of a hierarchical tuple. -/
inductive Index : Profile → Type where
  | leaf : Index .leaf
  | left {left right : Profile} : Index left → Index (.prod left right)
  | right {left right : Profile} : Index right → Index (.prod left right)
  deriving DecidableEq, Repr

namespace Index

/-- Convert a hierarchical tuple leaf selector to a flat `Fin p.size`. -/
def toFin : {p : Profile} → Index p → Fin p.size
  | .leaf, .leaf => ⟨0, by simp [Profile.size]⟩
  | .prod _ _, .left i => ⟨i.toFin, by
      exact Nat.lt_of_lt_of_le i.toFin.isLt (Nat.le_add_right _ _)⟩
  | .prod l _, .right i => ⟨l.size + i.toFin, by
      exact Nat.add_lt_add_left i.toFin.isLt l.size⟩

/-- Convert a flat leaf index to a hierarchical tuple leaf selector. -/
def ofFin : (p : Profile) → Fin p.size → Index p
  | .leaf, _ => .leaf
  | .prod l r, i =>
      if h : i.1 < l.size then
        .left (ofFin l ⟨i.1, h⟩)
      else
        .right (ofFin r ⟨i.1 - l.size, by
          have hi : i.1 < l.size + r.size := by simpa [Profile.size] using i.2
          have hle : l.size ≤ i.1 := Nat.le_of_not_gt h
          omega⟩)

theorem toFin_ofFin : ∀ {p : Profile} (i : Fin p.size), (ofFin p i).toFin = i
  | .leaf, i => by
      apply Fin.ext
      simp [ofFin, toFin]
  | .prod l r, i => by
      by_cases h : i.1 < l.size
      · simp [ofFin, h, toFin, toFin_ofFin]
      · apply Fin.ext
        have hle : l.size ≤ i.1 := Nat.le_of_not_gt h
        have hlt : i.1 - l.size < r.size := by
          have hi : i.1 < l.size + r.size := by simpa [Profile.size] using i.2
          omega
        have hrec : (ofFin r ⟨i.1 - l.size, hlt⟩).toFin = ⟨i.1 - l.size, hlt⟩ :=
          toFin_ofFin (p := r) ⟨i.1 - l.size, hlt⟩
        have hval : (ofFin r ⟨i.1 - l.size, hlt⟩).toFin.1 = i.1 - l.size :=
          congrArg Fin.val hrec
        simp [ofFin, h, toFin, hval, Nat.add_sub_of_le hle]

theorem ofFin_toFin : ∀ {p : Profile} (i : Index p), ofFin p i.toFin = i
  | .leaf, .leaf => rfl
  | .prod l r, .left i => by
      simp [toFin, ofFin, i.toFin.isLt, ofFin_toFin]
  | .prod l r, .right i => by
      have hnot : ¬ l.size + i.toFin.1 < l.size := by omega
      simp [toFin, ofFin, hnot, ofFin_toFin]

/-- Equivalence between hierarchical leaf selectors and flat finite indices. -/
def equivFin (p : Profile) : Index p ≃ Fin p.size where
  toFun := toFin
  invFun := ofFin p
  left_inv := ofFin_toFin
  right_inv := toFin_ofFin

end Index

/-- Build a hierarchical tuple by giving a value for each leaf index. -/
def ofFn {α : Type u} : {p : Profile} → (Index p → α) → HTuple α p
  | .leaf, f => .leaf (f .leaf)
  | .prod _ _, f => .prod (ofFn fun i => f (.left i)) (ofFn fun i => f (.right i))

/-- Read a leaf selected by `HTuple.Index`. -/
def get {α : Type u} : {p : Profile} → HTuple α p → Index p → α
  | .leaf, .leaf value, .leaf => value
  | .prod _ _, .prod fst _, .left i => fst.get i
  | .prod _ _, .prod _ snd, .right i => snd.get i

/-- Replace a leaf selected by `HTuple.Index`. -/
def set {α : Type u} : {p : Profile} → HTuple α p → Index p → α → HTuple α p
  | .leaf, .leaf _, .leaf, value => .leaf value
  | .prod _ _, .prod fst snd, .left i, value => .prod (fst.set i value) snd
  | .prod _ _, .prod fst snd, .right i, value => .prod fst (snd.set i value)

/-- Modify a leaf selected by `HTuple.Index`. -/
def modify {α : Type u} {p : Profile} (x : HTuple α p) (i : Index p) (f : α → α) : HTuple α p :=
  x.set i (f (x.get i))

@[simp]
theorem get_leaf {α : Type u} (value : α) : get (.leaf value) .leaf = value := rfl

@[simp]
theorem get_prod_left {α : Type u} {p q : Profile} (fst : HTuple α p) (snd : HTuple α q)
    (i : Index p) :
    get (.prod fst snd) (.left i) = fst.get i := rfl

@[simp]
theorem get_prod_right {α : Type u} {p q : Profile} (fst : HTuple α p) (snd : HTuple α q)
    (i : Index q) :
    get (.prod fst snd) (.right i) = snd.get i := rfl

@[simp]
theorem get_map {α : Type u} {β : Type v} (f : α → β) {p : Profile}
    (x : HTuple α p) (i : Index p) :
    (map f x).get i = f (x.get i) := by
  induction p with
  | leaf =>
      cases x with | leaf value =>
      cases i
      rfl
  | prod p q hp hq =>
      cases x with | prod fst snd =>
      cases i <;> simp [hp, hq]

@[simp]
theorem set_leaf {α : Type u} (old value : α) : set (.leaf old) .leaf value = .leaf value := rfl

@[simp]
theorem set_prod_left {α : Type u} {p q : Profile} (fst : HTuple α p) (snd : HTuple α q)
    (i : Index p) (value : α) :
    set (.prod fst snd) (.left i) value = .prod (fst.set i value) snd := rfl

@[simp]
theorem set_prod_right {α : Type u} {p q : Profile} (fst : HTuple α p) (snd : HTuple α q)
    (i : Index q) (value : α) :
    set (.prod fst snd) (.right i) value = .prod fst (snd.set i value) := rfl

@[simp]
theorem get_ofFn {α : Type u} {p : Profile} (f : Index p → α) (i : Index p) :
    (ofFn f).get i = f i := by
  induction p with
  | leaf => cases i; rfl
  | prod p q hp hq => cases i <;> simp [ofFn, hp, hq]

@[simp]
theorem ofFn_get {α : Type u} {p : Profile} (x : HTuple α p) :
    ofFn (fun i => x.get i) = x := by
  induction p with
  | leaf =>
      cases x with | leaf x => rfl
  | prod p q hp hq =>
      cases x with | prod x₀ x₁ =>
      simp [ofFn, hp, hq]

end HTuple

end NumLean
