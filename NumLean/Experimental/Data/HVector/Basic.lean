module

public import NumLean.Data.HTuple.Algebra
public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn
public import Init.Data.Vector.Zip

@[expose] public section

namespace NumLean

/-- Flat representation of a hierarchical tuple shape.

`HVector α p` stores the leaves of an `HTuple α p` in left-to-right order inside a
`Vector α p.size`.  It keeps the same profile-indexed API as `HTuple`, but avoids nested runtime
constructors for the stored coordinates. -/
structure HVector (α : Type u) (p : HTuple.Profile) where
  data : Vector α p.size

namespace HVector

open HTuple

variable {α : Type u} {β : Type v} {γ : Type w}
variable {p q : HTuple.Profile}

/-- Read by flat finite position. -/
@[inline] def getFin (x : HVector α p) (i : Fin p.size) : α :=
  x.data[i.1]

/-- Read by hierarchical leaf selector. -/
@[inline] def get (x : HVector α p) (i : HTuple.Index p) : α :=
  x.getFin i.toFin

/-- Build from a flat finite-indexed function. -/
@[inline] def ofFnFin {p : HTuple.Profile} (f : Fin p.size → α) : HVector α p :=
  ⟨Vector.ofFn f⟩

/-- Build from a hierarchical leaf-indexed function. -/
@[inline] def ofFn {p : HTuple.Profile} (f : HTuple.Index p → α) : HVector α p :=
  ofFnFin fun i => f (HTuple.Index.ofFin p i)

/-- Singleton hierarchical vector. -/
@[inline] def leaf (value : α) : HVector α .leaf :=
  ⟨Vector.singleton value⟩

/-- Product of two hierarchical vectors, stored by concatenating their flat leaves. -/
@[inline] def prod {p q : HTuple.Profile} (x : HVector α p) (y : HVector α q) :
    HVector α (.prod p q) :=
  ⟨x.data ++ y.data⟩

/-- Left component of a product-profile vector. -/
@[inline] def left {p q : HTuple.Profile} (x : HVector α (.prod p q)) : HVector α p :=
  ofFnFin fun i => x.getFin ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _)⟩

/-- Right component of a product-profile vector. -/
@[inline] def right {p q : HTuple.Profile} (x : HVector α (.prod p q)) : HVector α q :=
  ofFnFin fun i => x.getFin ⟨p.size + i.1, by exact Nat.add_lt_add_left i.2 p.size⟩

/-- Convert a flat hierarchical vector to the structural `HTuple` representation. -/
@[inline] def toHTuple : {p : HTuple.Profile} → HVector α p → HTuple α p
  | .leaf, x => .leaf (x.getFin ⟨0, by simp [HTuple.Profile.size]⟩)
  | .prod p q, x => .prod (toHTuple (left (p := p) (q := q) x)) (toHTuple (right (p := p) (q := q) x))

/-- Convert a structural `HTuple` to the flat `HVector` representation. -/
@[inline] def ofHTuple : {p : HTuple.Profile} → HTuple α p → HVector α p
  | _, x => ofFn fun i => x.get i

@[simp] theorem getFin_ofFnFin {p : HTuple.Profile} (f : Fin p.size → α) (i : Fin p.size) :
    (ofFnFin f : HVector α p).getFin i = f i := by
  simp [ofFnFin, getFin]

@[simp] theorem get_ofFn {p : HTuple.Profile} (f : HTuple.Index p → α) (i : HTuple.Index p) :
    (ofFn f : HVector α p).get i = f i := by
  simp [ofFn, get, HTuple.Index.ofFin_toFin]

@[simp] theorem get_left {p q : HTuple.Profile} (x : HVector α (.prod p q))
    (i : HTuple.Index p) :
    (left x).get i = x.get (.left i) := by
  unfold left get
  rw [getFin_ofFnFin]
  apply congrArg x.getFin
  apply Fin.ext
  rfl

@[simp] theorem get_right {p q : HTuple.Profile} (x : HVector α (.prod p q))
    (i : HTuple.Index q) :
    (right x).get i = x.get (.right i) := by
  unfold right get
  rw [getFin_ofFnFin]
  apply congrArg x.getFin
  apply Fin.ext
  rfl

@[simp] theorem get_toHTuple : {p : HTuple.Profile} → (x : HVector α p) →
    (i : HTuple.Index p) → x.toHTuple.get i = x.get i
  | .leaf, x, .leaf => rfl
  | .prod p q, x, .left i => by
      simp [toHTuple, get_toHTuple (p := p)]
  | .prod p q, x, .right i => by
      simp [toHTuple, get_toHTuple (p := q)]

@[simp] theorem get_ofHTuple {p : HTuple.Profile} (x : HTuple α p) (i : HTuple.Index p) :
    (ofHTuple x).get i = x.get i := by
  simp [ofHTuple]

theorem extFin {x y : HVector α p} (h : ∀ i : Fin p.size, x.getFin i = y.getFin i) : x = y := by
  cases x with | mk xdata =>
  cases y with | mk ydata =>
  congr
  apply Vector.ext
  intro i hi
  exact h ⟨i, hi⟩

theorem ext {x y : HVector α p} (h : ∀ i : HTuple.Index p, x.get i = y.get i) : x = y := by
  apply extFin
  intro i
  simpa [get, HTuple.Index.toFin_ofFin] using h (HTuple.Index.ofFin p i)

/-- Equivalence between flat and structural hierarchical representations. -/
@[inline] def equivHTuple (α : Type u) (p : HTuple.Profile) : HVector α p ≃ HTuple α p where
  toFun := toHTuple
  invFun := ofHTuple
  left_inv := by
    intro x
    apply extFin
    intro i
    rw [← HTuple.Index.toFin_ofFin (p := p) i]
    change (ofHTuple x.toHTuple).get (HTuple.Index.ofFin p i) = x.get (HTuple.Index.ofFin p i)
    simp
  right_inv := by
    intro x
    apply HTuple.ext
    intro i
    simp

/-- Map over leaves. -/
@[inline] def map (f : α → β) (x : HVector α p) : HVector β p :=
  ⟨x.data.map f⟩

/-- Zip two vectors of the same profile. -/
@[inline] def map₂ (f : α → β → γ) (x : HVector α p) (y : HVector β p) : HVector γ p :=
  ⟨x.data.zipWith f y.data⟩

abbrev zipWith := @map₂

/-- Fold a hierarchical vector using one operation for leaves and one for products. -/
@[inline, specialize] def fold (leaf : α → β) (prod : β → β → β) :
    {p : HTuple.Profile} → HVector α p → β
  | .leaf, x => leaf (x.getFin ⟨0, by simp [HTuple.Profile.size]⟩)
  | .prod p q, x => prod (fold leaf prod (left (p := p) (q := q) x))
      (fold leaf prod (right (p := p) (q := q) x))

/-- Fold a hierarchical vector into an additive monoid-like target. -/
@[inline, specialize] def foldMap [Zero β] [Add β] (f : α → β) (x : HVector α p) : β :=
  x.fold f (· + ·)

/-- Left-to-right leaf list. -/
@[inline] def toList (x : HVector α p) : List α :=
  x.data.toList

/-- Replace a selected leaf. -/
@[inline] def set (x : HVector α p) (i : HTuple.Index p) (value : α) : HVector α p :=
  ⟨x.data.set i.toFin.1 value i.toFin.2⟩

/-- Modify a selected leaf. -/
@[inline] def modify (x : HVector α p) (i : HTuple.Index p) (f : α → α) : HVector α p :=
  x.set i (f (x.get i))

@[simp] theorem getFin_set (x : HVector α p) (i : HTuple.Index p) (value : α)
    (j : Fin p.size) :
    (x.set i value).getFin j = if j = i.toFin then value else x.getFin j := by
  by_cases h : j = i.toFin
  · subst h
    simp [set, getFin]
  · have hval : j.1 ≠ i.toFin.1 := by
      intro hval
      exact h (Fin.ext hval)
    rw [if_neg h]
    exact Vector.getElem_set_ne (xs := x.data) (x := value)
      (hi := i.toFin.2) (hj := j.2) (h := Ne.symm hval)

@[simp] theorem get_set_same (x : HVector α p) (i : HTuple.Index p) (value : α) :
    (x.set i value).get i = value := by
  simp [get]

@[simp] theorem get_set_ne (x : HVector α p) {i j : HTuple.Index p} (value : α)
    (h : j ≠ i) :
    (x.set i value).get j = x.get j := by
  have hfin : j.toFin ≠ i.toFin := by
    intro hto
    exact h (by simpa [HTuple.Index.ofFin_toFin] using congrArg (HTuple.Index.ofFin p) hto)
  simp [get, hfin]

@[simp] theorem get_leaf (value : α) : get (leaf value) HTuple.Index.leaf = value := rfl

@[simp] theorem get_map (f : α → β) (x : HVector α p) (i : HTuple.Index p) :
    (x.map f).get i = f (x.get i) := by
  simp [map, get, getFin]

@[simp] theorem get_map₂ (f : α → β → γ) (x : HVector α p) (y : HVector β p)
    (i : HTuple.Index p) :
    (map₂ f x y).get i = f (x.get i) (y.get i) := by
  simp [map₂, get, getFin]

@[simp] theorem toList_leaf (value : α) : toList (leaf value) = [value] := rfl

end HVector

end NumLean
