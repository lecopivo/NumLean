# Tangent Derivative API Plan

This plan defines a first, minimal API for differentiability between fibered additive torsors. It
intentionally avoids adding a separate fiber-base or quotient typeclass for now.

Reference implementation for ordinary torsors:

```text
~/Documents/SciLean/SciLean/Analysis/Calculus/HasTorsorFDeriv.lean
```

That file defines `HasTorsorFDerivAt f f' p` as

```lean
HasFDerivAt (fun v => f (v +ᵥ p) -ᵥ f p) f' 0
```

and proves the basic chain rule and common calculus rules. The fibered torsor API should mirror this
where possible; the only essential extra ingredient is eventual target-fiber consistency.

## Core Idea

For a map `f : X -> Y` between fibered additive torsors modeled on additive groups `E` and `F`, the
tangent derivative at `x : X` is the Frechet derivative at `0 : E` of the displacement-coordinate map

```lean
fun v : E => f (v +ᵥ x) -ᵥ f x
```

The definition must also require that `f` is locally fiber-preserving near `x`; otherwise the
displacement map can ignore discontinuous jumps in the fiber/base direction.

## New File

Create:

```text
NumLean/Mathlib/Calculus/TDeriv.lean
```

Imports:

```lean
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import NumLean.Mathlib.FiberedAddTorsor
```

## Definitions

### `HasTDerivWithinAt`

```lean
def HasTDerivWithinAt
    {𝕜 E F X Y : Type*}
    [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [TopologicalSpace X] [TopologicalSpace Y]
    [FiberedAddTorsor E X] [FiberedAddTorsor F Y]
    (f : X -> Y) (f' : E →L[𝕜] F) (s : Set X) (x : X) : Prop :=
  (∀ᶠ y in 𝓝[s] x, FiberedAddTorsor.fiber (f y) (f x)) ∧
    HasFDerivWithinAt
      (fun v : E => f (v +ᵥ x) -ᵥ f x)
      f'
      ((fun v : E => v +ᵥ x) ⁻¹' s)
      0
```

### `HasTDerivAt`

```lean
def HasTDerivAt
    (f : X -> Y) (f' : E →L[𝕜] F) (x : X) : Prop :=
  HasTDerivWithinAt f f' Set.univ x
```

## Basic Projection Lemmas

Add destructors for the conjunction so downstream proofs do not unfold definitions manually.

```lean
theorem HasTDerivWithinAt.eventually_fiber
    (hf : HasTDerivWithinAt f f' s x) :
    ∀ᶠ y in 𝓝[s] x, FiberedAddTorsor.fiber (f y) (f x)

theorem HasTDerivWithinAt.hasFDerivWithinAt
    (hf : HasTDerivWithinAt f f' s x) :
    HasFDerivWithinAt
      (fun v : E => f (v +ᵥ x) -ᵥ f x)
      f'
      ((fun v : E => v +ᵥ x) ⁻¹' s)
      0
```

## Derived Operators

Do not add these in the very first commit unless needed, but keep the naming aligned with SciLean:

```lean
noncomputable def tderiv
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (f : X -> Y) (x : X) : E →L[𝕜] F :=
  fderiv 𝕜 (fun v : E => f (v +ᵥ x) -ᵥ f x) 0
```

Expected theorem once `tderiv` exists:

```lean
theorem HasTDerivAt.tderiv (hf : HasTDerivAt f f' x) :
    tderiv 𝕜 f x = f'
```

This is the fibered analogue of SciLean's `HasTorsorFDerivAt.torsorFDeriv`.

For `HasTDerivAt`, expose the simplified derivative statement at `0`.

```lean
theorem HasTDerivAt.eventually_fiber
    (hf : HasTDerivAt f f' x) :
    ∀ᶠ y in 𝓝 x, FiberedAddTorsor.fiber (f y) (f x)

theorem HasTDerivAt.hasFDerivAt_displacement
    (hf : HasTDerivAt f f' x) :
    HasFDerivAt
      (fun v : E => f (v +ᵥ x) -ᵥ f x)
      f'
      0
```

## Topological Compatibility

Keep `FiberedAddTorsor` algebraic. Add only local hypotheses to theorems first, rather than adding a
global topological torsor class immediately.

Useful local assumptions:

```lean
ContinuousAt (fun v : E => v +ᵥ x) 0
ContinuousAt (fun w : F => w +ᵥ f x) 0
```

For continuity of `f : X -> Y`, also require that points near `x` are eventually in the same domain
fiber as `x`:

```lean
∀ᶠ y in 𝓝 x, FiberedAddTorsor.fiber y x
```

This avoids baking assumptions about the quotient/base topology into the first API.

## Continuity Theorems

### Displacement Continuity

Differentiability implies continuity of the displacement-coordinate map.

```lean
theorem HasTDerivAt.continuousAt_displacement
    (hf : HasTDerivAt f f' x) :
    ContinuousAt (fun v : E => f (v +ᵥ x) -ᵥ f x) 0
```

This should follow directly from `hf.hasFDerivAt_displacement.continuousAt`.

### Continuity of the Coordinate Representative

Using the eventual target-fiber condition, reconstruct `f (v +ᵥ x)` from its displacement.

```lean
theorem HasTDerivAt.continuousAt_vadd
    (hf : HasTDerivAt f f' x)
    (hvaddY : ContinuousAt (fun w : F => w +ᵥ f x) 0) :
    ContinuousAt (fun v : E => f (v +ᵥ x)) 0
```

Proof idea:

1. `hf.continuousAt_displacement` gives continuity of `v ↦ f (v +ᵥ x) -ᵥ f x` at `0`.
2. Compose with `w ↦ w +ᵥ f x`.
3. Use eventual target-fiber consistency to rewrite
   ```lean
   (f (v +ᵥ x) -ᵥ f x) +ᵥ f x = f (v +ᵥ x)
   ```
   eventually near `0`.

### Continuity of `f`

This needs a domain-side local fiber condition, because the derivative only controls the fiber
coordinate chart through `x`.

```lean
theorem HasTDerivAt.continuousAt
    (hf : HasTDerivAt f f' x)
    (hdom : ∀ᶠ y in 𝓝 x, FiberedAddTorsor.fiber y x)
    (hvsubX : Tendsto (fun y : X => y -ᵥ x) (𝓝 x) (𝓝 0))
    (hvaddY : ContinuousAt (fun w : F => w +ᵥ f x) 0) :
    ContinuousAt f x
```

Proof idea:

1. Use `hdom` to rewrite `(y -ᵥ x) +ᵥ x = y` eventually near `x`.
2. Pull `continuousAt_vadd` back along `y ↦ y -ᵥ x`.
3. Replace the coordinate expression by `f y` eventually.

## Composition Theorem

Target statement:

```lean
theorem HasTDerivAt.comp
    (hg : HasTDerivAt g g' (f x))
    (hf : HasTDerivAt f f' x)
    (hf_cont : ContinuousAt f x) :
    HasTDerivAt (fun x => g (f x)) (g'.comp f') x
```

Proof outline:

1. Fiber part:
   - `hg.eventually_fiber` holds near `f x`.
   - Pull it back along `hf_cont`.
   - This gives eventual fiber consistency for `fun x => g (f x)`.

2. Derivative part:
   Define displacement maps conceptually:
   ```lean
   Fdisp v := f (v +ᵥ x) -ᵥ f x
   Gdisp w := g (w +ᵥ f x) -ᵥ g (f x)
   ```

   `hf` gives `HasFDerivAt Fdisp f' 0`.
   `hg` gives `HasFDerivAt Gdisp g' 0`.
   Mathlib composition gives:
   ```lean
   HasFDerivAt (fun v => Gdisp (Fdisp v)) (g'.comp f') 0
   ```

3. Use eventual fiber consistency of `f` to rewrite:
   ```lean
   Fdisp v +ᵥ f x = f (v +ᵥ x)
   ```
   eventually near `0`.

4. Conclude the derivative statement for:
   ```lean
   fun v => g (f (v +ᵥ x)) -ᵥ g (f x)
   ```

Comparison with SciLean:

In ordinary `AddTorsor`, the key composition equality is global:

```lean
(fun v => g (f (v +ᵥ x)) -ᵥ g (f x))
  = (fun w => g (w +ᵥ f x) -ᵥ g (f x)) ∘
      (fun v => f (v +ᵥ x) -ᵥ f x)
```

The proof is just `funext v; simp [vsub_vadd]`. In the fibered setting this equality is only
eventual near `0`, because the rewrite

```lean
(f (v +ᵥ x) -ᵥ f x) +ᵥ f x = f (v +ᵥ x)
```

requires `fiber (f (v +ᵥ x)) (f x)`. Therefore the composition proof should use an eventual equality
congruence theorem for `HasFDerivAt` after deriving this eventual equality from
`hf.eventually_fiber` and continuity/tendsto of `v ↦ v +ᵥ x`.

## First-Pass Calculus Rules

After the definition, projections, continuity, and composition theorem, add a small rule set modeled
on `HasTorsorFDerivAt`.

### Constant Map

Requires target fiber consistency, which is automatic by reflexivity.

```lean
theorem hasTDerivAt_const (y : Y) (x : X) :
    HasTDerivAt (fun _ : X => y) (0 : E →L[𝕜] F) x
```

### Identity Map

```lean
theorem hasTDerivAt_id (x : X) :
    HasTDerivAt (fun x : X => x) (ContinuousLinearMap.id 𝕜 E) x
```

This should use `vadd_vsub` for the displacement derivative and `fiber_vadd_left` for the fiber
condition.

### Product Pairing

Once product instances are imported:

```lean
theorem HasTDerivAt.prod
    (hf : HasTDerivAt f f' x) (hg : HasTDerivAt g g' x) :
    HasTDerivAt (fun x => (f x, g x)) (f'.prod g') x
```

The target-fiber condition follows componentwise from `hf.eventually_fiber` and
`hg.eventually_fiber`. The derivative proof mirrors SciLean's `HasTorsorFDerivAt.prod`.

`FiberedAddTorsor` should have only the fully fibered product-shaped instance:

```lean
FiberedAddTorsor (G × H) (P × Q)
```

Discrete primitive types can be made into torsors over `Unit`, so products involving those types use
the same generic product instance instead of specialized `P × I` or `I × P` instances.

```lean
theorem HasTDerivAt.prodMk
    (hf : HasTDerivAt f f' x) (hg : HasTDerivAt g g' x) :
    HasTDerivAt (fun x => (f x, g x)) (f'.prod g') x

theorem hasTDerivAt_fst (x : P × Q) :
    HasTDerivAt (Prod.fst : P × Q -> P) (ContinuousLinearMap.fst 𝕜 G H) x

theorem hasTDerivAt_snd (x : P × Q) :
    HasTDerivAt (Prod.snd : P × Q -> Q) (ContinuousLinearMap.snd 𝕜 G H) x
```

### Vector-Space-Valued Bridge

When the codomain is the model vector space itself, the fiber condition is trivial and the derivative
can be related to the ordinary derivative of `fun v => c (v +ᵥ x)`.

```lean
theorem hasTDerivAt_iff_comp_vadd {c : X -> F} {c' : E →L[𝕜] F} {x : X} :
    HasTDerivAt c c' x ↔ HasFDerivAt (fun v : E => c (v +ᵥ x)) c' 0
```

This is the analogue of SciLean's `hasTorsorFDerivAt_iff_comp_vadd`. It unlocks ordinary add/sub
rules for functions into vector spaces.

### Add/Sub/Neg Rules For Vector-Space Codomains

These should be derived through `hasTDerivAt_iff_comp_vadd`:

```lean
theorem HasTDerivAt.add
theorem HasTDerivAt.sub
theorem HasTDerivAt.neg
```

Only add these once the bridge theorem is working.

## Compatibility With Ordinary Derivatives

For model spaces viewed as fibered torsors over themselves, prove the analogue of SciLean's
`hasTorsorFDerivAt_iff_hasFDerivAt`:

```lean
theorem hasTDerivAt_iff_hasFDerivAt {f : E -> F} {f' : E →L[𝕜] F} {x : E} :
    HasTDerivAt f f' x ↔ HasFDerivAt f f' x
```

The fiber condition is trivial because the `FiberedAddTorsor G G` instance has `fiber _ _ := True`.
The derivative part is the same translation argument used in SciLean.

## Non-Goals for First Pass

Do not add these yet:

- quotient/base typeclass
- `tderivWithin` computable operator
- strict derivative variants
- global topological torsor class

These can be added once the minimal predicate API is useful in examples.
