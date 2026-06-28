module

public section

namespace NumLean

set_option linter.unnecessarySimpa false

namespace HList

/-- Variadic hierarchical profile. -/
inductive Profile where
  | leaf
  | node (ps : List Profile)
  deriving Repr

/-- Untyped hierarchical list of values. -/
inductive HList (α : Type u) where
  | value (a : α)
  | node (as : List (HList α))
  deriving Repr

namespace Profile

/-- Number of scalar leaves in a profile. -/
def size : Profile → Nat
  | .leaf => 1
  | .node ps => ps.foldl (fun n p => n + p.size) 0

/-- Number of immediate axes in a profile tree. -/
def rank : Profile → Nat
  | .leaf => 0
  | .node ps => ps.length

end Profile

namespace HList

/-- A raw `HList` has a given profile. -/
inductive OfProfile : HList α → Profile → Prop where
  | value (a : α) : OfProfile (.value a) .leaf
  | node_nil : OfProfile (.node []) (.node [])
  | node_cons {t : HList α} {ts : List (HList α)} {p : Profile} {ps : List Profile} :
      OfProfile t p → OfProfile (.node ts) (.node ps) → OfProfile (.node (t :: ts)) (.node (p :: ps))

namespace OfProfile

private theorem value_node_false {a : α} {ps : List Profile} : OfProfile (.value a) (.node ps) → False := by
  intro h
  cases h

private theorem node_leaf_false {as : List (HList α)} : OfProfile (.node as) .leaf → False := by
  intro h
  cases h

private theorem node_nil_cons_false {α : Type u} {p : Profile} {ps : List Profile} :
    OfProfile (α := α) (.node []) (.node (p :: ps)) → False := by
  intro h
  cases h

private theorem node_cons_nil_false {t : HList α} {ts : List (HList α)} :
    OfProfile (.node (t :: ts)) (.node []) → False := by
  intro h
  cases h

theorem node_head {t : HList α} {ts : List (HList α)} {p : Profile} {ps : List Profile} :
    OfProfile (.node (t :: ts)) (.node (p :: ps)) → OfProfile t p
  | .node_cons ht _ => ht

theorem node_tail {t : HList α} {ts : List (HList α)} {p : Profile} {ps : List Profile} :
    OfProfile (.node (t :: ts)) (.node (p :: ps)) → OfProfile (.node ts) (.node ps)
  | .node_cons _ hts => hts

end OfProfile

/-- Flatten leaves left-to-right. -/
def toList : HList α → List α
  | .value a => [a]
  | .node as => as.flatMap toList

/-- Map over every scalar leaf. -/
def map (f : α → β) : HList α → HList β
  | .value a => .value (f a)
  | .node as => .node (as.map (map f))

mutual

/-- Combine two raw hierarchical lists leafwise.

Mismatched raw shapes return an empty node; `map₂_ofProfile` shows this branch is unreachable when
both inputs have the same profile. -/
def map₂ (f : α → β → γ) : HList α → HList β → HList γ
  | .value a, .value b => .value (f a b)
  | .node as, .node bs => .node (map₂List f as bs)
  | _, _ => .node []

/-- Combine two raw node payload lists leafwise. -/
def map₂List (f : α → β → γ) : List (HList α) → List (HList β) → List (HList γ)
  | [], [] => []
  | a :: as, b :: bs => map₂ f a b :: map₂List f as bs
  | _, _ => []

end

/-- Fold over all scalar leaves. -/
def fold (leaf : α → β) (node : List β → β) : HList α → β
  | .value a => leaf a
  | .node as => node (as.map (fold leaf node))

/-- `map` preserves profile proofs. -/
private theorem map_ofProfile (f : α → β) : (t : HList α) → (p : Profile) →
    t.OfProfile p → (t.map f).OfProfile p
  | _, _, .value a => by
      simpa [map] using (OfProfile.value (α := β) (f a))
  | _, _, .node_nil => by
      simpa [map] using (OfProfile.node_nil (α := β))
  | _, _, .node_cons ht hts => by
      have hts' := map_ofProfile f _ _ hts
      simp [map] at hts'
      simpa [map] using
        (OfProfile.node_cons (map_ofProfile f _ _ ht) hts')

/-- `map₂` preserves profile proofs. -/
private theorem map₂_ofProfile (f : α → β → γ) : (t : HList α) → (u : HList β) → (p : Profile) →
    t.OfProfile p → u.OfProfile p → (map₂ f t u).OfProfile p
  | _, _, _, .value a, hu => by
      cases hu with
      | value b => simpa [map₂] using (OfProfile.value (α := γ) (f a b))
  | _, _, _, .node_nil, hu => by
      cases hu with
      | node_nil => simpa [map₂, map₂List] using (OfProfile.node_nil (α := γ))
  | _, _, _, .node_cons ht hts, hu => by
      cases hu with
      | node_cons hu hus =>
          have hs := map₂_ofProfile f _ _ _ hts hus
          simp [map₂] at hs
          simpa [map₂, map₂List] using
            (OfProfile.node_cons (map₂_ofProfile f _ _ _ ht hu) hs)

end HList

/-- Profile-indexed tuple, stored as an untyped value plus a profile proof. -/
structure HPTuple (α : Type u) (p : Profile) where
  val : HList α
  of_profile : val.OfProfile p
  deriving Repr

namespace HPTuple

/-- A selector for one scalar leaf of a variadic hierarchical profile. -/
inductive Index : Profile → Type where
  | leaf : Index .leaf
  | head {p : Profile} {ps : List Profile} : Index p → Index (.node (p :: ps))
  | tail {p : Profile} {ps : List Profile} : Index (.node ps) → Index (.node (p :: ps))
  deriving Repr

structure NodePayload (α : Type u) (ps : List Profile) where
  vals : List (HList α)
  of_profile : (HList.node vals).OfProfile (.node ps)

/-- Leaf constructor. -/
@[match_pattern, inline, expose]
def leaf (a : α) : HPTuple α .leaf where
  val := .value a
  of_profile := .value a

/-- Node constructor from a raw list and matching profile proof. -/
def node {ps : List Profile} (as : List (HList α)) (h : (HList.node as).OfProfile (.node ps)) :
    HPTuple α (.node ps) where
  val := .node as
  of_profile := h

/-- Empty variadic node. -/
@[match_pattern, inline, expose]
def nil : HPTuple α (.node []) where
  val := .node []
  of_profile := .node_nil

/-- Prepend one hierarchical tuple to a variadic node tuple. -/
@[match_pattern, inline, expose]
def cons {p : Profile} {ps : List Profile} (x : HPTuple α p) (xs : HPTuple α (.node ps)) :
    HPTuple α (.node (p :: ps)) where
  val := match xs.val with
    | .node vals => .node (x.val :: vals)
    | .value _ => .node [x.val]
  of_profile := by
    match hxs : xs.val with
    | .node _ =>
        exact .node_cons x.of_profile (by simpa [hxs] using xs.of_profile)
    | .value _ =>
        exact False.elim (HList.OfProfile.value_node_false (by simpa [hxs] using xs.of_profile))

/-- First child of a non-empty variadic node tuple. -/
@[inline]
def head {p : Profile} {ps : List Profile} (x : HPTuple α (.node (p :: ps))) : HPTuple α p :=
  match hval : x.val with
  | .node (t :: _) =>
      { val := t, of_profile := HList.OfProfile.node_head (by simpa [hval] using x.of_profile) }
  | .node [] =>
      False.elim (HList.OfProfile.node_nil_cons_false (α := α) (by simpa [hval] using x.of_profile))
  | .value _ =>
      False.elim (HList.OfProfile.value_node_false (by simpa [hval] using x.of_profile))

/-- Remaining children of a non-empty variadic node tuple. -/
@[inline]
def tail {p : Profile} {ps : List Profile} (x : HPTuple α (.node (p :: ps))) : HPTuple α (.node ps) :=
  match hval : x.val with
  | .node (t :: ts) =>
      { val := .node ts, of_profile := HList.OfProfile.node_tail (t := t) (by simpa [hval] using x.of_profile) }
  | .node [] =>
      False.elim (HList.OfProfile.node_nil_cons_false (α := α) (by simpa [hval] using x.of_profile))
  | .value _ =>
      False.elim (HList.OfProfile.value_node_false (by simpa [hval] using x.of_profile))

mutual

/-- Build a hierarchical tuple by giving a value for each leaf index. -/
@[inline]
def ofFn : {p : Profile} → (Index p → α) → HPTuple α p
  | .leaf, f => leaf (f .leaf)
  | .node ps, f =>
      let payload := ofFnPayload ps f
      { val := .node payload.vals, of_profile := payload.of_profile }

/-- Build the raw payload for a node tuple from indexed values. -/
@[inline]
def ofFnPayload : (ps : List Profile) → (Index (.node ps) → α) → NodePayload α ps
  | [], _ => { vals := [], of_profile := .node_nil }
  | _ :: ps, f =>
      let head := ofFn fun i => f (.head i)
      let tail := ofFnPayload ps fun i => f (.tail i)
      { vals := head.val :: tail.vals,
        of_profile := .node_cons head.of_profile tail.of_profile }

end

/-- Read a scalar leaf selected by `HPTuple.Index`. -/
@[inline]
def get : {p : Profile} → HPTuple α p → Index p → α
  | .leaf, ⟨.value a, _⟩, .leaf => a
  | .leaf, ⟨.node _, h⟩, .leaf => False.elim (HList.OfProfile.node_leaf_false h)
  | .node [], _, i => nomatch i
  | .node (_ :: _), ⟨.value _, h⟩, _ => False.elim (HList.OfProfile.value_node_false h)
  | .node (_ :: _), ⟨.node [], h⟩, _ => False.elim (HList.OfProfile.node_nil_cons_false (α := α) h)
  | .node (p :: _), ⟨.node (t :: _), h⟩, .head i =>
      get (p := p) ⟨t, HList.OfProfile.node_head h⟩ i
  | .node (_ :: ps), ⟨.node (t :: ts), h⟩, .tail i =>
      get (p := .node ps) ⟨.node ts, HList.OfProfile.node_tail (t := t) h⟩ i

/-- Replace a scalar leaf selected by `HPTuple.Index`. -/
@[inline]
def set : {p : Profile} → HPTuple α p → Index p → α → HPTuple α p
  | .leaf, _, .leaf, value => leaf value
  | .node [], _, i, _ => nomatch i
  | .node (_ :: _), ⟨.value _, h⟩, _, _ => False.elim (HList.OfProfile.value_node_false h)
  | .node (_ :: _), ⟨.node [], h⟩, _, _ => False.elim (HList.OfProfile.node_nil_cons_false (α := α) h)
  | .node (p :: _), ⟨.node (t :: ts), h⟩, .head i, value =>
      let head := set (p := p) ⟨t, HList.OfProfile.node_head h⟩ i value
      { val := .node (head.val :: ts),
        of_profile := .node_cons head.of_profile (HList.OfProfile.node_tail (t := t) h) }
  | .node (_ :: ps), ⟨.node (t :: ts), h⟩, .tail i, value =>
      let tail := set (p := .node ps) ⟨.node ts, HList.OfProfile.node_tail (t := t) h⟩ i value
      match htail : tail.val with
      | .node ts' =>
          { val := .node (t :: ts'),
            of_profile := .node_cons (HList.OfProfile.node_head h) (by simpa [htail] using tail.of_profile) }
      | .value _ =>
          False.elim (HList.OfProfile.value_node_false (by simpa [htail] using tail.of_profile))

/-- Modify a scalar leaf selected by `HPTuple.Index`. -/
@[inline]
def modify {p : Profile} (x : HPTuple α p) (i : Index p) (f : α → α) : HPTuple α p :=
  x.set i (f (x.get i))

@[simp]
private theorem get_leaf (a : α) : get (leaf a) Index.leaf = a := rfl

@[simp]
private theorem set_leaf (old value : α) : set (leaf old) Index.leaf value = leaf value := rfl

@[simp]
private theorem ofFn_leaf (f : Index .leaf → α) : ofFn f = leaf (f .leaf) := rfl

@[simp]
private theorem get_ofFn : {p : Profile} → (f : Index p → α) → (i : Index p) → (ofFn f).get i = f i
  | .leaf, _, .leaf => rfl
  | .node (_ :: _), f, .head i => by
      simpa [ofFn, ofFnPayload, get] using get_ofFn (fun i => f (.head i)) i
  | .node (_ :: ps), f, .tail i => by
      simpa [ofFn, ofFnPayload, get] using get_ofFn (p := .node ps) (fun i => f (.tail i)) i

@[simp]
private theorem get_cons_head {p : Profile} {ps : List Profile} (x : HPTuple α p)
    (xs : HPTuple α (.node ps)) (i : Index p) :
    (cons x xs).get (.head i) = x.get i := by
  cases hxs : xs.val with
  | value _ =>
      exact False.elim (HList.OfProfile.value_node_false (by simpa [hxs] using xs.of_profile))
  | node vals =>
      simp [cons, get, hxs]

@[simp]
private theorem get_cons_tail {p : Profile} {ps : List Profile} (x : HPTuple α p)
    (xs : HPTuple α (.node ps)) (i : Index (.node ps)) :
    (cons x xs).get (.tail i) = xs.get i := by
  cases xs with
  | mk val h =>
      cases h with
      | node_nil => nomatch i
      | node_cons ht hts => simp [cons, get]

@[simp]
private theorem head_cons {p : Profile} {ps : List Profile} (x : HPTuple α p)
    (xs : HPTuple α (.node ps)) :
    (cons x xs).head = x := by
  cases xs with
  | mk val h =>
      cases h with
      | node_nil => simp [head]
      | node_cons ht hts => simp [head]

@[simp]
private theorem tail_cons {p : Profile} {ps : List Profile} (x : HPTuple α p)
    (xs : HPTuple α (.node ps)) :
    (cons x xs).tail = xs := by
  cases xs with
  | mk val h =>
      cases h with
      | node_nil => simp [tail]
      | node_cons ht hts => simp [tail]

/-- Flatten leaves left-to-right. -/
@[inline]
def toList {p : Profile} (x : HPTuple α p) : List α :=
  x.val.toList

@[simp]
theorem toList_leaf (a : α) : (leaf a).toList = [a] := by
  simp [leaf, toList, HList.toList]

@[simp]
theorem toList_nil : (nil : HPTuple α (.node [])).toList = [] := by
  simp [nil, toList, HList.toList]

@[simp]
theorem toList_cons {p : Profile} {ps : List Profile} (x : HPTuple α p) (xs : HPTuple α (.node ps)) :
    (cons x xs).toList = x.toList ++ xs.toList := by
  cases hxs : xs.val with
  | value _ =>
      exact False.elim (HList.OfProfile.value_node_false (by simpa [hxs] using xs.of_profile))
  | node vals =>
      simp [cons, toList, HList.toList, hxs]

/-- Map over every scalar leaf. -/
@[inline, specialize]
def map (f : α → β) {p : Profile} (x : HPTuple α p) : HPTuple β p where
  val := x.val.map f
  of_profile := HList.map_ofProfile f x.val p x.of_profile

/-- Combine two tuples leafwise. -/
@[inline, specialize]
def map₂ (f : α → β → γ) {p : Profile} (x : HPTuple α p) (y : HPTuple β p) :
    HPTuple γ p where
  val := HList.map₂ f x.val y.val
  of_profile := HList.map₂_ofProfile f x.val y.val p x.of_profile y.of_profile

abbrev zipWith := @map₂

/-- Fold over all scalar leaves. -/
@[inline, specialize]
def fold (leaf : α → β) (node : List β → β) {p : Profile} (x : HPTuple α p) : β :=
  x.val.fold leaf node

/-- Fold leaves into an additive monoid-like target. -/
@[inline, specialize]
def foldMap [Zero β] [Add β] (f : α → β) {p : Profile} (x : HPTuple α p) : β :=
  x.fold f (List.foldl (· + ·) 0)

/-- Sum a leafwise operation over two hierarchical tuples of the same profile. -/
def innerWith [Zero γ] [Add γ] (f : α → β → γ) {p : Profile}
    (x : HPTuple α p) (y : HPTuple β p) : γ :=
  (x.map₂ f y).foldMap id

/-- Natural semimodule inner product over matching hierarchical tuples. -/
def inner [Zero β] [Add β] [SMul α β] {p : Profile}
    (idx : HPTuple α p) (stride : HPTuple β p) : β :=
  innerWith (fun n d => n • d) idx stride

end HPTuple

end HList

end NumLean
