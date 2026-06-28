module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Tactic
public import NumLean.Interfaces.SetElem

@[expose] public section

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
@[inline] def size : Profile → Nat
  | .leaf => 1
  | .prod left right => left.size + right.size

/-- Tensorial product of profiles, replacing each leaf of the second profile by the first profile. -/
@[inline] def tmul (p q : Profile) : Profile :=
  match q with
  | .leaf => p
  | .prod q₁ q₂ => .prod (tmul p q₁) (tmul p q₂)

/-- `p.Refines q` means that `q` is obtained from `p` by collapsing subtrees. -/
class inductive Refines : Profile → Profile → Type where
  | leaf (p : Profile) : Refines p .leaf
  | prod {p₁ p₂ q₁ q₂ : Profile} (h₁ : Refines p₁ q₁) (h₂ : Refines p₂ q₂) :
      Refines (.prod p₁ p₂) (.prod q₁ q₂)

/-- `p.StrictlyRefines q` means that `q` is obtained from `p` by at least one real collapse.

Unlike `Refines`, there is no reflexive constructor: `.leaf` does not strictly refine itself, and
products strictly refine products only when at least one component strictly refines its target. -/
class inductive StrictlyRefines : Profile → Profile → Type where
  | leaf (p₁ p₂ : Profile) : StrictlyRefines (.prod p₁ p₂) .leaf
  | prodLeft {p₁ p₂ q₁ q₂ : Profile} (h₁ : StrictlyRefines p₁ q₁) (h₂ : Refines p₂ q₂) :
      StrictlyRefines (.prod p₁ p₂) (.prod q₁ q₂)
  | prodRight {p₁ p₂ q₁ q₂ : Profile} (h₁ : Refines p₁ q₁) (h₂ : StrictlyRefines p₂ q₂) :
      StrictlyRefines (.prod p₁ p₂) (.prod q₁ q₂)

@[reducible] def StrictlyRefines.toRefines {p q : Profile} : p.StrictlyRefines q → p.Refines q
  | .leaf p₁ p₂ => .leaf (.prod p₁ p₂)
  | .prodLeft h₁ h₂ => .prod h₁.toRefines h₂
  | .prodRight h₁ h₂ => .prod h₁ h₂.toRefines

instance (priority := low) {p q : Profile} [h : p.StrictlyRefines q] : p.Refines q :=
  h.toRefines

instance {p₁ p₂ : Profile} : (Profile.prod p₁ p₂).StrictlyRefines .leaf :=
  .leaf p₁ p₂

instance {p₁ p₂ q₁ q₂ : Profile} [h₁ : p₁.StrictlyRefines q₁] [h₂ : p₂.Refines q₂] :
    (Profile.prod p₁ p₂).StrictlyRefines (Profile.prod q₁ q₂) :=
  .prodLeft h₁ h₂

instance {p₁ p₂ q₁ q₂ : Profile} [h₁ : p₁.Refines q₁] [h₂ : p₂.StrictlyRefines q₂] :
    (Profile.prod p₁ p₂).StrictlyRefines (Profile.prod q₁ q₂) :=
  .prodRight h₁ h₂

theorem not_strictlyRefines_self (p : Profile) : p.StrictlyRefines p → False := by
  induction p with
  | leaf =>
      intro h
      cases h
  | prod p₁ p₂ ih₁ ih₂ =>
      intro h
      cases h with
      | prodLeft h₁ _ => exact ih₁ h₁
      | prodRight _ h₂ => exact ih₂ h₂

/-- Decide whether `p` refines `q`, returning the refinement proof when it does. -/
def refines? : (p q : Profile) → Option (p.Refines q)
  | p, .leaf => some (.leaf p)
  | .leaf, .prod _ _ => none
  | .prod p₁ p₂, .prod q₁ q₂ =>
      match refines? p₁ q₁, refines? p₂ q₂ with
      | some h₁, some h₂ => some (.prod h₁ h₂)
      | _, _ => none

/-- All profiles obtained by coarsening `p`, including `.leaf` and `p` itself. -/
def allCoarsenings : Profile → Array Profile
  | .leaf => #[.leaf]
  | .prod p₁ p₂ => Id.run do
      let ps₁ := allCoarsenings p₁
      let ps₂ := allCoarsenings p₂
      let mut ps := #[.leaf]
      for q₁ in ps₁ do
        for q₂ in ps₂ do
          ps := ps.push (.prod q₁ q₂)
      return ps

-- instance : Mul Profile where
--   mul := mul

instance {q : Profile} : q.Refines .leaf := .leaf q

instance {p₁ p₂ q₁ q₂ : Profile} [h₁ : p₁.Refines q₁] [h₂ : p₂.Refines q₂] :
    (Profile.prod p₁ p₂).Refines (Profile.prod q₁ q₂) := .prod h₁ h₂

@[simp]
theorem size_leaf : Profile.leaf.size = 1 := rfl

@[simp]
theorem size_prod (left right : Profile) :
    (Profile.prod left right).size = left.size + right.size := rfl

@[simp]
theorem mul_leaf (p : Profile) : p.tmul .leaf = p := rfl

@[simp]
theorem mul_prod (p q r : Profile) : p.tmul (.prod q r) = .prod (p.tmul q) (p.tmul r) := rfl

@[simp]
theorem leaf_mul (p : Profile) : (Profile.leaf).tmul p = p := by
  induction p with
  | leaf => rfl
  | prod p q hp hq => simp [hp, hq]

theorem size_pos (p : Profile) : 0 < p.size := by
  induction p with
  | leaf => simp [size]
  | prod left _ hleft _ => simp [size, Nat.add_pos_left hleft]

mutual
  /-- Render a profile using the same compact shape as `hp(...)` notation. -/
  def toNotationString : Profile → String
    | .leaf => "•"
    | .prod left right => toNotationComponentString left ++ "," ++ toNotationString right

  def toNotationComponentString : Profile → String
    | .leaf => "•"
    | .prod left right => "(" ++ toNotationString (.prod left right) ++ ")"
end

instance : ToString Profile where
  toString p := "hp(" ++ p.toNotationString ++ ")"

end Profile

end HTuple

/-- A hierarchical tuple with profile-indexed leaves. -/
inductive HTuple (α : Type u) : HTuple.Profile → Type u where
  | leaf (value : α) : HTuple α .leaf
  | prod {left right : HTuple.Profile} (fst : HTuple α left) (snd : HTuple α right) :
      HTuple α (.prod left right)
  deriving Repr

namespace HTuple

declare_syntax_cat htuple_stx (behavior := both)
syntax term : htuple_stx
syntax (priority := high) htuple_stx ", " htuple_stx,* : htuple_stx
syntax (priority := high) "(" htuple_stx ")" : htuple_stx

/-- Tuple notation for homogeneous hierarchical tuples.

Each argument becomes a leaf, comma-separated arguments become right-associated products, and
syntactic nested tuples are decomposed recursively. -/
syntax "h(" htuple_stx ")" : term

open Lean Syntax
macro_rules
  | `(htuple_stx| ( $x:htuple_stx ) ) =>
    `(htuple_stx| $x:htuple_stx )

  | `(htuple_stx| $x:term )     => `(HTuple.leaf $x)

  | `(htuple_stx| $x:htuple_stx , $y:htuple_stx, $ys:htuple_stx,* ) =>
    `(htuple_stx| $x:htuple_stx , ($y:htuple_stx, $ys:htuple_stx,*) )

  | `(htuple_stx| $x:htuple_stx , $y:htuple_stx ) => `(HTuple.prod h($x:htuple_stx) h($y:htuple_stx))

  | `(term| h( $x:htuple_stx )) => do
    let x ← `(htuple_stx| ( $x:htuple_stx ))
    match ← Macro.expandMacro? x.raw with
    | some x => return x
    | none => Macro.throwUnsupported

@[app_unexpander HTuple.leaf] meta def unexpandHTupleLeaf : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:term) => `(h($x:term))
  | _ => throw ()

@[app_unexpander HTuple.prod] meta def unexpandHTupleProd : Lean.PrettyPrinter.Unexpander
  | `($(_) h($x:term) h($y:htuple_stx) ) => `(h($x:term, $y))
  | `($(_) h($x:htuple_stx) h($y:htuple_stx) ) => `(h(($x), $y))
  | _ => throw ()


declare_syntax_cat htuple_profile_stx (behavior := both)
syntax "•" : htuple_profile_stx
syntax (priority := high) htuple_profile_stx ", " htuple_profile_stx,* : htuple_profile_stx
syntax (priority := high) "(" htuple_profile_stx ")" : htuple_profile_stx

open Lean Syntax
syntax:max "hp(" htuple_profile_stx ")" : term

macro_rules
  | `(htuple_profile_stx| ( $x:htuple_profile_stx ) ) =>
    `(htuple_profile_stx| $x:htuple_profile_stx )

  | `(htuple_profile_stx| • ) => `(HTuple.Profile.leaf)

  | `(htuple_profile_stx| $x:htuple_profile_stx , $y:htuple_profile_stx, $ys:htuple_profile_stx,* ) =>
    `(htuple_profile_stx| $x:htuple_profile_stx , ($y:htuple_profile_stx, $ys:htuple_profile_stx,*) )

  | `(htuple_profile_stx| $x:htuple_profile_stx , $y:htuple_profile_stx ) =>
    `(HTuple.Profile.prod hp($x:htuple_profile_stx) hp($y:htuple_profile_stx))

  | `(term| hp( $x:htuple_profile_stx )) => do
    let x ← `(htuple_profile_stx| ( $x:htuple_profile_stx ))
    match ← Macro.expandMacro? x.raw with
    | some x => return x
    | none => Macro.throwUnsupported

@[app_unexpander Profile.leaf] meta def unexpandHTupleProfileLeaf : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(hp(•))

@[app_unexpander Profile.prod] meta def unexpandHTupleProfileProd : Lean.PrettyPrinter.Unexpander
  | `($(_) hp(•) hp($y:htuple_profile_stx)) => `(hp(•, $y))
  | `($(_) hp($x:htuple_profile_stx) hp($y:htuple_profile_stx)) => `(hp(($x), $y))
  | _ => throw ()

mutual
  /-- Render an `HTuple` using the same compact shape as `h(...)` notation. -/
  def toNotationString [ToString α] : {p : Profile} → HTuple α p → String
    | .leaf, .leaf x => toString x
    | .prod _ _, .prod left right => toNotationComponentString left ++ "," ++ toNotationString right

  def toNotationComponentString [ToString α] : {p : Profile} → HTuple α p → String
    | .leaf, .leaf x => toString x
    | .prod _ _, .prod left right => "(" ++ toNotationString (.prod left right) ++ ")"
end

instance [ToString α] : ToString (HTuple α p) where
  toString x := "h(" ++ x.toNotationString ++ ")"

@[coe]
def toScalar (x : HTuple α .leaf) : α := match x with | .leaf x => x

instance : CoeOut (HTuple α .leaf) α := ⟨toScalar⟩
instance : Coe α (HTuple α .leaf) := ⟨.leaf⟩

@[simp]
theorem leaf_toScalar (a : α) : (HTuple.leaf a).toScalar = a := rfl

@[simp]
theorem leaf_toScalar_eta (x : HTuple α .leaf) : HTuple.leaf x.toScalar = x := by
  cases x
  rfl

@[simp]
theorem coe_leaf (a : α) : ((HTuple.leaf a : HTuple α .leaf) : α) = a := rfl

@[simp]
theorem leaf_coe (x : HTuple α .leaf) : (HTuple.leaf (x : α) : HTuple α .leaf) = x := by
  cases x
  rfl

theorem toScalar_injective : Function.Injective (toScalar : HTuple α .leaf → α) := by
  intro x y h
  cases x
  cases y
  simp_all

/-- We provide this instance because when we write `xs[i]` and `i : HTuple Nat .leaf` the index
does not get coerced to `Nat`. This instance will force `xs[i]` to be turned into `xs[i.toScalar]`.-/
@[reducible]
instance [GetElem cont idx elem dom] : GetElem cont (HTuple idx .leaf) elem (fun xs i => dom xs i) where
  getElem xs i h := xs[(i : idx)]'h

/-- Normalize `getElem` from index type `HTuple idx .leaf` to `idx`. -/
@[simp]
theorem getElem_leaf [GetElem cont idx elem dom] (xs : cont) (i : HTuple idx .leaf) (h : dom xs i) :
  getElem xs i h = getElem xs i.toScalar h := rfl

/-- We provide this instance because when we write `xs[i] := ...` and `i : HTuple Nat .leaf` the
index does not get coerced to `Nat`. This instance will force `xs[i] := ...` to be turned into
`xs[i.toScalar] := ...`.-/
@[reducible]
instance [inst : SetElem cont idx elem dom] :
    SetElem cont (HTuple idx .leaf) elem (fun xs i => dom xs i) where
  setElem xs i x h := setElem xs (i : idx) x h
  setElem_valid := inst.setElem_valid

/-- Normalize `getElem` from index type `HTuple idx .leaf` to `idx`. -/
@[simp]
theorem setElem_leaf [SetElem cont idx elem dom]
    (xs : cont) (i : HTuple idx .leaf) (x : elem) (h : dom xs i) :
  setElem xs i x h = setElem xs i.toScalar x h := rfl

/-- Map a function over every leaf of a hierarchical tuple. -/
@[inline, specialize] def map {α : Type u} {β : Type v} (f : α → β) : {p : Profile} → HTuple α p → HTuple β p
  | .leaf, .leaf value => .leaf (f value)
  | .prod _ _, .prod fst snd => .prod (map f fst) (map f snd)

/-- Combine two hierarchical tuples leafwise. -/
@[inline, specialize] def map₂ {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) :
    {p : Profile} → HTuple α p → HTuple β p → HTuple γ p
  | .leaf, .leaf a, .leaf b => .leaf (f a b)
  | .prod _ _, .prod a₀ a₁, .prod b₀ b₁ => .prod (map₂ f a₀ b₀) (map₂ f a₁ b₁)

abbrev zipWith := @map₂

/-- Fold a hierarchical tuple using one operation for leaves and one for products. -/
@[inline, specialize] def fold {α : Type u} {β : Type v} (leaf : α → β) (prod : β → β → β) :
    {p : Profile} → HTuple α p → β
  | .leaf, .leaf value => leaf value
  | .prod _ _, .prod fst snd => prod (fold leaf prod fst) (fold leaf prod snd)

/-- Fold a hierarchical tuple into an additive monoid-like target. -/
@[inline, specialize] def foldMap {α : Type u} {β : Type v} [Zero β] [Add β] (f : α → β) {p : Profile}
    (x : HTuple α p) : β :=
  x.fold f (· + ·)

/-- Sum a leafwise operation over two hierarchical tuples of the same profile. -/
@[inline, specialize] def innerWith {α : Type u} {β : Type v} {γ : Type w} [Zero γ] [Add γ]
    (f : α → β → γ) : {p : Profile} → HTuple α p → HTuple β p → γ
  | .leaf, .leaf a, .leaf b => f a b
  | .prod _ _, .prod x₀ x₁, .prod y₀ y₁ => innerWith f x₀ y₀ + innerWith f x₁ y₁

/-- Natural semimodule inner product over matching hierarchical tuples. -/
@[inline, specialize] def inner {α : Type u} {β : Type v} [Zero β] [Add β] [SMul α β] {p : Profile}
    (idx : HTuple α p) (stride : HTuple β p) : β :=
  innerWith (fun n d => n • d) idx stride

/-- Number of elements in the bounded rectangle `0...shape`. -/
@[inline] def numel {p : Profile} : HTuple Nat p → Nat
  | .leaf n => n
  | .prod l r => l.numel * r.numel

/-- Row-major stride for `0...shape`, with the rightmost coordinate innermost. -/
@[inline] def rowMajorStride {p : Profile} (shape : HTuple Nat p) : HTuple Nat p :=
  match p, shape with
  | .leaf, .leaf _ => .leaf 1
  | .prod _ _, .prod l r => .prod ((rowMajorStride l).map (fun x => r.numel * x)) (rowMajorStride r)

/-- Row-major index inside `0...shape`, with the rightmost coordinate innermost. -/
@[inline] def rowMajorIndex {p : Profile} (x : HTuple Nat p) (shape : HTuple Nat p) : Nat :=
  match p, x, shape with
  | .leaf, .leaf i, .leaf _ => i
  | .prod _ _, .prod il ir, .prod sl sr => rowMajorIndex ir sr + sr.numel * rowMajorIndex il sl

/-- Column-major stride for `0...shape`, with the leftmost coordinate innermost. -/
@[inline] def colMajorStride {p : Profile} (shape : HTuple Nat p) : HTuple Nat p :=
  match p, shape with
  | .leaf, .leaf _ => .leaf 1
  | .prod _ _, .prod l r => .prod (colMajorStride l) ((colMajorStride r).map (fun x => l.numel * x))

/-- Column-major index inside `0...shape`, with the leftmost coordinate innermost. -/
@[inline] def colMajorIndex {p : Profile} (x : HTuple Nat p) (shape : HTuple Nat p) : Nat :=
  match p, x, shape with
  | .leaf, .leaf i, .leaf _ => i
  | .prod _ _, .prod il ir, .prod sl sr => colMajorIndex il sl + sl.numel * colMajorIndex ir sr

theorem inner_map_mul_left (n : Nat) {p : Profile} (i stride : HTuple Nat p) :
    i.inner (stride.map (fun x => n * x)) = n * i.inner stride := by
  induction p with
  | leaf =>
      cases i with | leaf i =>
      cases stride with | leaf stride =>
      change i * (n * stride) = n * (i * stride)
      ac_rfl
  | prod p q hp hq =>
      cases i with | prod il ir =>
      cases stride with | prod sl sr =>
      change il.inner (sl.map (fun x => n * x)) + ir.inner (sr.map (fun x => n * x)) =
        n * (il.inner sl + ir.inner sr)
      rw [hp il sl, hq ir sr, Nat.left_distrib]

/-- Recursive row-major indexing agrees with evaluating against the row-major stride. -/
theorem rowMajorIndex_eq_inner_rowMajorStride {p : Profile} (i shape : HTuple Nat p) :
    rowMajorIndex i shape = i.inner (rowMajorStride shape) := by
  induction p with
  | leaf =>
      cases i with | leaf i =>
      cases shape with | leaf shape =>
      simp [rowMajorIndex, rowMajorStride, inner, innerWith]
  | prod p q hp hq =>
      cases i with | prod il ir =>
      cases shape with | prod sl sr =>
      change rowMajorIndex ir sr + sr.numel * rowMajorIndex il sl =
        il.inner ((rowMajorStride sl).map (fun x => sr.numel * x)) + ir.inner (rowMajorStride sr)
      rw [hp il sl, hq ir sr, inner_map_mul_left]
      omega

/-- Recursive column-major indexing agrees with evaluating against the column-major stride. -/
theorem colMajorIndex_eq_inner_colMajorStride {p : Profile} (i shape : HTuple Nat p) :
    colMajorIndex i shape = i.inner (colMajorStride shape) := by
  induction p with
  | leaf =>
      cases i with | leaf i =>
      cases shape with | leaf shape =>
      simp [colMajorIndex, colMajorStride, inner, innerWith]
  | prod p q hp hq =>
      cases i with | prod il ir =>
      cases shape with | prod sl sr =>
      change colMajorIndex il sl + sl.numel * colMajorIndex ir sr =
        il.inner (colMajorStride sl) + ir.inner ((colMajorStride sr).map (fun x => sl.numel * x))
      rw [hp il sl, hq ir sr, inner_map_mul_left]

/-- The leaf values of a hierarchical tuple in left-to-right order. -/
@[inline] def toList {α : Type u} : {p : Profile} → HTuple α p → List α
  | .leaf, .leaf value => [value]
  | .prod _ _, .prod fst snd => fst.toList ++ snd.toList

@[simp]
theorem length_toList {α : Type u} : {p : Profile} → (x : HTuple α p) → x.toList.length = p.size
  | .leaf, .leaf _ => rfl
  | .prod _ _, .prod fst snd => by
      simp [toList, length_toList fst, length_toList snd]

theorem toList_injective {α : Type u} {p : Profile} :
    Function.Injective (fun x : HTuple α p => x.toList) := by
  induction p with
  | leaf =>
      intro x y h
      cases x with | leaf x =>
      cases y with | leaf y =>
      simp [toList] at h
      exact congrArg HTuple.leaf h
  | prod p q hp hq =>
      intro x y h
      cases x with | prod x₀ x₁ =>
      cases y with | prod y₀ y₁ =>
      have h₀ : x₀.toList = y₀.toList := by
        have ht := congrArg (fun xs : List α => xs.take p.size) h
        simpa [toList, length_toList x₀, length_toList y₀] using ht
      have h₁ : x₁.toList = y₁.toList := by
        have hd := congrArg (fun xs : List α => xs.drop p.size) h
        simpa [toList, length_toList x₀, length_toList y₀] using hd
      exact congrArg₂ HTuple.prod (hp h₀) (hq h₁)

/-- Remove `Profile` from the type. Useful if you need to store `HTuple` in `Array` or `List` -/
def eraseProfile {α p} (x : HTuple α p) : (p' : HTuple.Profile) × HTuple α p' := ⟨p, x⟩

/-- Left projection from a product-profile tuple. -/
@[inline] def fst {α : Type u} {p q : Profile} : HTuple α (.prod p q) → HTuple α p
  | .prod x _ => x

/-- Right projection from a product-profile tuple. -/
@[inline] def snd {α : Type u} {p q : Profile} : HTuple α (.prod p q) → HTuple α q
  | .prod _ y => y

@[simp]
theorem fst_prod {α : Type u} {p q : Profile} (x : HTuple α p) (y : HTuple α q) :
    fst (.prod x y) = x := rfl

@[simp]
theorem snd_prod {α : Type u} {p q : Profile} (x : HTuple α p) (y : HTuple α q) :
    snd (.prod x y) = y := rfl

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
theorem map_id {α : Type u} {p : Profile} (x : HTuple α p) :
    map id x = x := by
  induction p with
  | leaf =>
      cases x with | leaf value => rfl
  | prod p q hp hq =>
      cases x with | prod fst snd =>
      simp [hp, hq]

@[simp]
theorem map_id_fun {α : Type u} {p : Profile} (x : HTuple α p) :
    map (fun a => a) x = x := by
  simpa only [id_eq] using (map_id x)

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
@[inline] def toFin : {p : Profile} → Index p → Fin p.size
  | .leaf, .leaf => ⟨0, by simp [Profile.size]⟩
  | .prod _ _, .left i => ⟨(toFin i).1, by
      exact Nat.lt_of_lt_of_le i.toFin.isLt (Nat.le_add_right _ _)⟩
  | .prod l _, .right i => ⟨l.size + i.toFin.1, by
      exact Nat.add_lt_add_left i.toFin.isLt l.size⟩

/-- Convert a flat leaf index to a hierarchical tuple leaf selector. -/
@[inline] def ofFin : (p : Profile) → Fin p.size → Index p
  | .leaf, _ => .leaf
  | .prod l r, i =>
      if hlt : i.1 < l.size then
        .left (ofFin l ⟨i.1, hlt⟩)
      else
        .right (ofFin r ⟨i.1 - l.size, by
          have hi : i.1 < l.size + r.size := by simpa [Profile.size] using i.2
          have hle : l.size ≤ i.1 := Nat.le_of_not_gt hlt
          omega⟩)

theorem toFin_ofFin : ∀ {p : Profile} (i : Fin p.size), (ofFin p i).toFin = i
  | .leaf, i => by
      apply Fin.ext
      simp [ofFin, toFin]
  | .prod l r, i => by
      by_cases hlt : i.1 < l.size
      · simp [ofFin, hlt, toFin, toFin_ofFin]
      · apply Fin.ext
        have hle : l.size ≤ i.1 := Nat.le_of_not_gt hlt
        have hright : i.1 - l.size < r.size := by
          have hi : i.1 < l.size + r.size := by simpa [Profile.size] using i.2
          omega
        have hrec : (ofFin r ⟨i.1 - l.size, hright⟩).toFin = ⟨i.1 - l.size, hright⟩ :=
          toFin_ofFin (p := r) ⟨i.1 - l.size, hright⟩
        have hval : (ofFin r ⟨i.1 - l.size, hright⟩).toFin.1 = i.1 - l.size :=
          congrArg Fin.val hrec
        rw [ofFin]
        simp only [dif_neg hlt]
        change l.size + (ofFin r ⟨i.1 - l.size, hright⟩).toFin.1 = i.1
        rw [hval]
        exact Nat.add_sub_of_le hle

theorem ofFin_toFin : ∀ {p : Profile} (i : Index p), ofFin p i.toFin = i
  | .leaf, .leaf => rfl
  | .prod l r, .left i => by
      simp [toFin, ofFin, i.toFin.isLt, ofFin_toFin]
  | .prod l r, .right i => by
      have hnot : ¬ l.size + i.toFin.1 < l.size := by omega
      simp [toFin, ofFin, hnot, ofFin_toFin]

/-- Equivalence between hierarchical leaf selectors and flat finite indices. -/
@[inline] def equivFin (p : Profile) : Index p ≃ Fin p.size where
  toFun := toFin
  invFun := ofFin p
  left_inv := ofFin_toFin
  right_inv := toFin_ofFin

end Index

/-- Build a hierarchical tuple by giving a value for each leaf index. -/
@[inline, specialize] def ofFn {α : Type u} : {p : Profile} → (Index p → α) → HTuple α p
  | .leaf, f => .leaf (f .leaf)
  | .prod _ _, f => .prod (ofFn fun i => f (.left i)) (ofFn fun i => f (.right i))

/-- Read a leaf selected by `HTuple.Index`. -/
@[inline] def get {α : Type u} : {p : Profile} → HTuple α p → Index p → α
  | .leaf, .leaf value, .leaf => value
  | .prod _ _, .prod fst _, .left i => fst.get i
  | .prod _ _, .prod _ snd, .right i => snd.get i

/-- Replace a leaf selected by `HTuple.Index`. -/
@[inline] def set {α : Type u} : {p : Profile} → HTuple α p → Index p → α → HTuple α p
  | .leaf, .leaf _, .leaf, value => .leaf value
  | .prod _ _, .prod fst snd, .left i, value => .prod (fst.set i value) snd
  | .prod _ _, .prod fst snd, .right i, value => .prod fst (snd.set i value)

/-- Modify a leaf selected by `HTuple.Index`. -/
@[inline, specialize] def modify {α : Type u} {p : Profile} (x : HTuple α p) (i : Index p) (f : α → α) : HTuple α p :=
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

/-- Flatten an `HTuple` of `HTuple`s by multiplying their profiles. -/
@[inline] def join {α : Type u} {p : Profile} : {q : Profile} →
    HTuple (HTuple α p) q → HTuple α (p.tmul q)
  | .leaf, .leaf x => x
  | .prod _ _, .prod x₁ x₂ => .prod x₁.join x₂.join

/-- Split an `HTuple` over a product profile into an `HTuple` of `HTuple`s. -/
@[inline] def split {α : Type u} {p : Profile} : {q : Profile} →
    HTuple α (p.tmul q) → HTuple (HTuple α p) q
  | .leaf, x => .leaf x
  | .prod _ _, .prod x₁ x₂ => .prod x₁.split x₂.split

@[simp]
theorem join_leaf {α : Type u} {p : Profile} (x : HTuple α p) :
    join (.leaf x) = x := rfl

@[simp]
theorem join_prod {α : Type u} {p q r : Profile}
    (x : HTuple (HTuple α p) q) (y : HTuple (HTuple α p) r) :
    join (.prod x y) = .prod x.join y.join := rfl

@[simp]
theorem split_leaf {α : Type u} {p : Profile} (x : HTuple α p) :
    split (q := .leaf) x = .leaf x := rfl

@[simp]
theorem split_prod {α : Type u} {p q r : Profile}
    (x : HTuple α (p.tmul q)) (y : HTuple α (p.tmul r)) :
    split (q := .prod q r) (.prod x y) = .prod x.split y.split := rfl

@[simp]
theorem join_split {α : Type u} {p q : Profile} (x : HTuple α (p.tmul q)) :
    join (split (p := p) (q := q) x) = x := by
  induction q with
  | leaf => rfl
  | prod q r hq hr =>
      cases x with | prod x y => simp [hq, hr]

@[simp]
theorem split_join {α : Type u} {p q : Profile} (x : HTuple (HTuple α p) q) :
    split (join x) = x := by
  induction q with
  | leaf => cases x with | leaf x => rfl
  | prod q r hq hr =>
      cases x with | prod x y => simp [hq, hr]

/-- Equivalence between nested tuples and tuples over product profiles. -/
@[simps! apply symm_apply]
def joinEquiv {α : Type u} (p q : Profile) : HTuple (HTuple α p) q ≃ HTuple α (p.tmul q) where
  toFun := join
  invFun := split
  left_inv := split_join
  right_inv := join_split

end HTuple

end NumLean
