---
name: isomorphic-types
description: Use when designing Lean/mathlib APIs for isomorphic type wrappers, type synonyms, subtype-like injective forgetful maps, coercions, casts, simp/norm_cast normal forms, extensionality, or function-like bundled objects.
---

# Isomorphic And Injective Types In Lean

Use this skill when a Lean API needs ergonomic movement between closely related types, for example:

- Isomorphic wrappers such as `WithLp p V` and `V`, `WithAbs v` and `R`, `WithTopology X t` and `X`, or `HTuple A .leaf` and `A`.
- Bounded or subtype-like types such as `Fin n` and `Nat`, where the forgetful map is injective but not surjective.
- Parallel bounded representations such as `Fin n` and a one-dimensional bounded tuple type.
- Bundled function objects such as `LinearMap`, `ContinuousLinearMap`, homs, embeddings, or affine-map records.

The goal is to make elaboration predictable, `simp` produce stable normal forms, and users avoid manual `change`, `cases`, and coercion archaeology.

## Classify The Relationship

Before adding instances, decide which case you are in.

- Definitional equality: the two types are literally the same after reduction. Prefer `abbrev`, avoid extra coercions, and add little API.
- Type synonym or newtype isomorphism: every value corresponds both ways, but the type has different instances. Examples: `WithLp p V`, `WithAbs v`, `WithTopology X t`, `HTuple A .leaf`. Provide named forward/backward maps and an `Equiv`.
- Subtype-like injection: one type embeds into another but not every target value is valid. Example: `Fin n → Nat`. Provide a forgetful coercion, extensionality by the forgetful value, constructor functions requiring proofs, and `CanLift`.
- Multiple bounded representations: two types are isomorphic only under matching parameters, such as `Fin n` and a bounded one-dimensional tuple. Provide an explicit `Equiv`, coercions only in safe directions, and round-trip simp lemmas.
- Function-like bundle: a structure packages a function plus laws or metadata. Use `FunLike` only if equality of the structure is determined by the coerced function. Otherwise use `CoeFun` and named projection lemmas.

## Choose Normal Forms

Pick one canonical representation for each context.

- For wrapper-to-base expressions, normal form is usually the projection: `x.ofLp`, `x.ofAbs`, `x.ofTopology`, `x.toScalar`, `(i : Nat)`.
- For base-to-wrapper expressions, normal form is usually the constructor only when the expected type is the wrapper: `WithLp.toLp p x`, `WithAbs.toAbs v x`, `WithTopology.toTopology t x`, `HTuple.leaf x`.
- For subtype-like values, preserve the rich type until a scalar operation demands the base type. For `i : Fin n`, arithmetic/order against naturals should see `(i : Nat)`.
- For mixed comparisons, normalize to the base relation when possible: `((i : Fin n) : Nat) < n`, `(x : A) = y`, or `x.ofLp = y`.
- For indexing APIs, normalize richer index wrappers to the container’s native index type: `xs[(i : Fin n)]`, `xs[(i : Nat)]`, or `xs[i.toScalar]`.

## Coercion Policy

Add only coercions that make elaboration more predictable.

- Safe for type synonyms: `Coe` or named constructors from base to wrapper can be okay if there is no loop and the wrapper is intended to be transparent at term level.
- Safe for subtype-like types: use a forgetful `CoeOut` from rich type to base type, such as `Fin n → Nat`.
- Safe for matching bounded representations: a coercion from the specialized rich representation to a standard representation can be useful, such as one-dimensional bounded tuple to `Fin n`.
- Dangerous: global base-to-bounded coercions such as `Nat → Fin n` or `NatCast (Fin n)`. Lean core deliberately keeps `NatCast (Fin n)` scoped, because a global `Nat → Fin n → Nat` loop can make `x < n` elaborate as `x < (n : Fin k)` and introduce modular arithmetic silently.
- Dangerous: symmetric coercions between isomorphic types in both directions if typeclass search or elaboration can loop or choose the wrong side.
- Prefer named constructors with proofs for bounded values: `ofNatLt`, `ofSubtype`, `ofFin`, `mk`, or an equivalence inverse.
- Prefer `CanLift` for proof-directed lifting from a base type into a subtype-like type.

## Type Synonym Pattern

Mathlib’s `WithLp`, `WithAbs`, and `WithTopology` are good models.

Recommended shape:

```lean
structure WithFoo (param : P) (A : Type*) where
  /-- Base-to-wrapper constructor. -/
  toFoo (param) ::
  /-- Wrapper-to-base projection. -/
  ofFoo : A

namespace WithFoo

@[simps]
protected def equiv (param : P) (A : Type*) : WithFoo param A ≃ A where
  toFun := ofFoo
  invFun := toFoo param
  left_inv _ := rfl
  right_inv _ := rfl

lemma ofFoo_toFoo (x : A) : ofFoo (toFoo param x) = x := rfl
@[simp] lemma toFoo_ofFoo (x : WithFoo param A) : toFoo param (ofFoo x) = x := rfl

lemma ofFoo_injective : Function.Injective (@ofFoo param A) :=
  Function.LeftInverse.injective <| toFoo_ofFoo _

end WithFoo
```

Transfer instances through the equivalence when the structures are intentionally identical:

```lean
instance [AddCommGroup A] : AddCommGroup (WithFoo param A) :=
  (WithFoo.equiv param A).addCommGroup
```

Add operation bridge lemmas by reflexivity when possible:

```lean
@[simp] lemma toFoo_add [Add A] (x y : A) :
    WithFoo.toFoo param (x + y) = WithFoo.toFoo param x + WithFoo.toFoo param y := rfl

@[simp] lemma ofFoo_add [Add A] (x y : WithFoo param A) :
    WithFoo.ofFoo (x + y) = x.ofFoo + y.ofFoo := rfl
```

Add `map` and `congr` if users will transport functions and equivalences:

```lean
protected def map (f : A → B) (x : WithFoo param A) : WithFoo param B :=
  WithFoo.toFoo param (f x.ofFoo)

protected def congr (e : A ≃ B) : WithFoo param A ≃ WithFoo param B :=
  (WithFoo.equiv param A).trans <| e.trans <| (WithFoo.equiv param B).symm
```

For pretty printing, consider an `@[app_delab]` rule so constructors do not print as raw structure literals. This is a polish step, not required for correctness.

## Subtype-Like Injection Pattern

Use this for types like `Fin n`, intervals, bounded indices, and dependent records with a proof field.

Recommended shape:

```lean
structure Bounded (n : Nat) where
  val : Nat
  isLt : val < n

instance : CoeOut (Bounded n) Nat := ⟨Bounded.val⟩

@[simp] theorem Bounded.is_lt (i : Bounded n) : (i : Nat) < n := i.isLt

@[ext]
theorem Bounded.ext {i j : Bounded n} (h : (i : Nat) = (j : Nat)) : i = j := by
  cases i; cases j; simp_all

theorem Bounded.val_injective : Function.Injective (fun i : Bounded n => (i : Nat)) :=
  fun _ _ h => Bounded.ext h
```

Provide proof-requiring constructors and `CanLift`:

```lean
def Bounded.ofNatLt (i : Nat) (h : i < n) : Bounded n := ⟨i, h⟩

instance : CanLift Nat (Bounded n) (fun i => (i : Nat)) (fun i => i < n) where
  prf i hi := ⟨⟨i, hi⟩, rfl⟩
```

Add relation simplification lemmas in both constructor and coercion form:

```lean
@[simp] theorem Bounded.mk_lt_mk {i j : Nat} {hi : i < n} {hj : j < n} :
    (⟨i, hi⟩ : Bounded n) < ⟨j, hj⟩ ↔ i < j := Iff.rfl

@[simp, norm_cast] theorem Bounded.coe_lt_coe {i j : Bounded n} :
    (i : Nat) < (j : Nat) ↔ i < j := Iff.rfl
```

Only add `LT`, `LE`, algebra, or order instances if they have the intended semantics. For bounded modular types, arithmetic may be modular; avoid making scalar literals silently coerce into bounded values globally.

## Matching Isomorphic Bounded Types

When two bounded representations are isomorphic for a specific parameter, provide the equivalence first.

Example pattern:

```lean
def leafEquiv (n : Nat) : BoundedTuple h(n) ≃ Fin n where
  toFun i := ⟨i.val.toScalar, by simpa using i.isLt⟩
  invFun i := ⟨leaf i.val, by simpa using i.isLt⟩
  left_inv := by intro i; ext; rfl
  right_inv := by intro i; ext; rfl
```

Then expose named projections and coercions in safe directions:

```lean
def toFin (i : BoundedTuple h(n)) : Fin n := leafEquiv n i
def toNat (i : BoundedTuple h(n)) : Nat := i.toFin

instance : Coe (BoundedTuple h(n)) (Fin n) := ⟨toFin⟩
instance : CoeOut (BoundedTuple h(n)) Nat := ⟨toNat⟩

@[simp, norm_cast] theorem coe_toFin_nat (i : BoundedTuple h(n)) :
    (((i : Fin n) : Nat) = (i : Nat)) := rfl
```

Add representation bridge lemmas:

```lean
@[simp] theorem toNat_eq_val_toScalar (i : BoundedTuple h(n)) :
    i.toNat = i.val.toScalar := by cases i; rfl

def ofFin (i : Fin n) : BoundedTuple h(n) := (leafEquiv n).symm i

@[simp] theorem toFin_ofFin (i : Fin n) : (ofFin i).toFin = i := rfl
@[simp] theorem ofFin_toFin (i : BoundedTuple h(n)) : ofFin i.toFin = i := by ext; rfl
```

Avoid a global coercion from `Fin n` to the alternate bounded type unless elaboration strongly needs it and there is no ambiguity.

## Leaf Wrapper Pattern

For wrappers like `HTuple A .leaf` and `A`, provide both directions and normalize projections.

Recommended API:

```lean
@[coe] def toScalar (x : HTuple A .leaf) : A :=
  match x with | .leaf x => x

instance : CoeOut (HTuple A .leaf) A := ⟨toScalar⟩
instance : Coe A (HTuple A .leaf) := ⟨HTuple.leaf⟩

@[simp] theorem leaf_toScalar (a : A) : (HTuple.leaf a).toScalar = a := rfl
@[simp] theorem leaf_coe_eta (x : HTuple A .leaf) : HTuple.leaf (x : A) = x := by cases x; rfl
theorem toScalar_injective : Function.Injective (toScalar : HTuple A .leaf → A) := by
  intro x y h; cases x; cases y; simp_all
```

If the wrapper has pointwise algebra or order, add leaf bridge lemmas for mixed scalar/wrapper terms:

```lean
@[simp] theorem elementwiseLT_leaf {x y : A} [LT A] :
    ((HTuple.leaf x : HTuple A .leaf) <ₑ HTuple.leaf y) ↔ x < y := Iff.rfl

@[simp] theorem elementwiseLT_leaf_right {x : HTuple A .leaf} {y : A} [LT A] :
    x <ₑ HTuple.leaf y ↔ (x : A) < y := by cases x; rfl
```

For numeric leaf wrappers, add explicit `Nat.cast` or scalar literal bridge lemmas if automation gets stuck unfolding `NatCast`:

```lean
@[simp, norm_cast] theorem coe_natCast_leaf (n : Nat) :
    ((n : HTuple Nat .leaf) : Nat) = n := rfl
```

## `GetElem` And `SetElem`

Elaboration often does not insert coercions in index positions. Add bridge instances when the wrapper is a common index type.

```lean
instance [GetElem C I E dom] :
    GetElem C (HTuple I .leaf) E (fun xs i => dom xs (i : I)) where
  getElem xs i h := xs[(i : I)]'h

@[simp] theorem getElem_leaf [GetElem C I E dom] (xs : C) (i : HTuple I .leaf) (h) :
    xs[i]'h = xs[(i : I)]'h := rfl
```

Mirror the same shape for `SetElem` if the project has mutable/update notation.

Prefer normalizing wrapper indices to the container’s native index rather than forcing every container to learn every wrapper.

## Function-Like Bundles

Copy mathlib’s `LinearMap` and `ContinuousLinearMap` pattern when a structure is determined by its function.

Use `FunLike` when coercion-to-function is injective:

```lean
instance : FunLike (MyHom A B) A B where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[ext] theorem MyHom.ext {f g : MyHom A B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp] theorem MyHom.coe_mk (f : A → B) (laws) :
    ((MyHom.mk f laws : MyHom A B) : A → B) = f := rfl
```

Add a class if there will be generic lemmas over many bundled map types:

```lean
class MyHomClass (F : Type*) (A B : outParam Type*) [FunLike F A B] : Prop where
  map_op : ∀ f : F, PreservesOp f
```

Use `initialize_simps_projections` for nontrivial structures so generated lemmas mention application rather than internals:

```lean
initialize_simps_projections MyHom (toFun → apply)
```

Use only `CoeFun` when the structure is not determined by evaluation:

```lean
instance : CoeFun (AffineData A B) (fun _ => A → B) := ⟨AffineData.eval⟩
```

Do not use `FunLike` for affine records, maps with cached metadata, bounded maps over an empty domain, or anything where two different records can evaluate identically.

## Attribute Checklist

Use `@[simp]` for wrapper-eliminating or constructor-eliminating facts:

- `ofFoo (toFoo x) = x`.
- `toFoo (ofFoo x) = x`.
- `(mk x h).val = x`.
- `(x : Base)` projections.
- Operation projections like `ofFoo (x + y) = ofFoo x + ofFoo y`.
- `GetElem`/`SetElem` bridge lemmas.

Use `@[norm_cast]` for coercion movement through equality/order/arithmetic:

- `((i : Fin n) : Nat) = i.val`.
- `(i : Nat) < (j : Nat) ↔ i < j` when the bounded order is inherited from the base.
- Scalar comparisons between a wrapper and its base type.

Use `@[ext]` for extensionality:

- Type synonyms: ext by projection if useful.
- Subtype-like types: ext by forgetful value.
- Function-like types: ext by pointwise equality.

Use `@[simps]` on equivalences and constructors that should generate projection lemmas, especially `Equiv`, `AddEquiv`, `LinearEquiv`, `RingEquiv`, and `Homeomorph` definitions.

Use custom tactic attributes only for domain-specific automation. Keep them pointed at small bridge lemmas, not large recursive definitions.

## Regression Tests

For every related-type API, add tests that exercise elaboration and simplification.

Examples:

```lean
example (x : WithFoo p A) : WithFoo.toFoo p x.ofFoo = x := by simp

example (i : Fin n) : ((i : Nat) < n) := by simpa using i.isLt

example (i : AltFin n) : (((i : Fin n) : Nat) = (i : Nat)) := by simp

example (x : HTuple Nat .leaf) (n : Nat) :
    (x <ₑ (n : HTuple Nat .leaf)) ↔ (x : Nat) < n := by simp

example (xs : Vector A n) (i : AltFin n) :
    xs[i] = xs[(i : Fin n)] := by rfl
```

Also test negative design constraints when important, for example that base-to-bounded coercions are not available globally.

## Decision Checklist

When implementing or reviewing such an API, verify these points:

- The relationship is correctly classified as defeq, isomorphic, injective/subtype-like, or function-like.
- There is one documented normal form for each common expression class.
- Coercions are one-directional unless bidirectionality is known not to create loops or ambiguous elaboration.
- Bounded constructors require proofs or are explicitly scoped if they wrap/mod values.
- There are named equivalences for isomorphic types.
- There are projection, round-trip, injectivity, and extensionality lemmas.
- `simp` can remove wrappers in goals and hypotheses without unfolding large definitions.
- `norm_cast` handles mixed coercion comparisons where appropriate.
- Index notation works through `GetElem`/`SetElem` bridge instances.
- Function-like records use `FunLike` only when coercion-to-function is injective.
- Type synonyms transfer instances through an equivalence and expose `map`/`congr` when users need functorial transport.
