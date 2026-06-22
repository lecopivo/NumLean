# Algebra Interfaces

NumLean splits algebraic interfaces into three layers:

1. `*Ops`: computational operations used by programs.
2. `LawfulData*Ops`: extra data needed to state lawfulness, usually noncomputable.
3. `Lawful*Ops`: propositions proving that the operations satisfy the expected laws.

The goal is to let users write executable, polymorphic code against small operation classes, then
prove properties only when those operations are known to be lawful.

For example, a program can be written with assumptions like:

```lean
{R : Type} [ROps R]
```

Theorems about that program can add the lawful assumptions:

```lean
{R : Type} [ROps R] [LawfulDataROps R] [LawfulROps R]
```

This keeps computational code independent from proof-only structure while still allowing theorem
statements to recover the usual mathematical meaning.

## Why Three Layers?

### `*Ops`

The `*Ops` classes contain the operations that programs actually call: addition, multiplication,
norms, scalar multiplication, real functions, complex functions, and so on.

These classes should be usable for concrete computational types such as machine floats, custom array
types, or other efficient representations. They should not require proofs or noncomputable structure
just to run a program.

### `LawfulData*Ops`

Some laws need extra data before they can even be stated. This data is often noncomputable or
mathematical rather than operational. Examples include:

- an equivalence with `ℝ` used to interpret a computational real type;
- functions into `ℝ` used to state real and complex semantics;
- topology, distance, norm, or completeness data;
- decidable equality or other auxiliary structure needed by a mathlib class.

This layer is intentionally narrow. It should contain data needed to state the laws, not a whole
mathlib structure when smaller data is enough.

### `Lawful*Ops`

The `Lawful*Ops` classes are proof-only propositions. They say that the operations from `*Ops`,
interpreted through the data from `LawfulData*Ops`, satisfy the expected algebraic and analytic laws.

This includes laws such as associativity, distributivity, compatibility of norms, real/complex
semantics, and compatibility with scalar actions.

## Mathlib Bridges

For the main algebraic concepts, NumLean provides bridges between the NumLean interface and the
corresponding mathlib class:

```lean
Ops + LawfulDataOps + LawfulOps  <->  mathlib concept
```

For example, lawful NumLean structures can be turned into mathlib structures such as rings, fields,
normed fields, normed algebras, and `RCLike`-style structures. Conversely, existing mathlib
structures can be used to populate the corresponding NumLean operations and laws.

These bridges are important because they give confidence that the operations in `*Ops` mean what the
user expects. If a type has operations, lawful data, and lawful proofs, then those operations can be
viewed as an instance of the corresponding standard mathlib concept. In the other direction, standard
mathlib models, especially `ℝ` and `ℂ`, induce NumLean operations with the expected behavior.

This does not prove that every computational approximation is exact mathematics. It does provide a
clear contract: programs are written against operations, and theorems are proved only under lawful
assumptions that connect those operations to standard mathematical structures.

## Programming And Proving

The intended workflow is:

1. Write programs polymorphic in the base type using `*Ops`.
2. Instantiate those operations for concrete computational backends.
3. Prove properties of the programs under `LawfulData*Ops` and `Lawful*Ops` assumptions.
4. Use the mathlib bridges when standard mathematical theorems are needed.

This lets the same program be used with multiple numeric representations while keeping the proof
story explicit. A theorem does not silently assume that arbitrary operations are mathematically valid;
it asks for the corresponding lawful structure.

For real-like models, this pattern is expressed by classes such as `ROps`, `LawfulDataROps`, and
`LawfulROps`, and by higher-level bundles such as `RealModelOps` and `LawfulRealModelOps`. Users can
write programs against `RealModelOps`, then prove their properties assuming the corresponding lawful
real model.

At minimum, the standard real numbers provide the reference model. This anchors the hierarchy: there
is at least one model where the operations behave exactly as expected, and other implementations can
state and prove the same contract when appropriate.
