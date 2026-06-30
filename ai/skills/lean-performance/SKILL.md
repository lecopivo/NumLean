---
name: lean-performance
description: Use when Lean files elaborate slowly, profiler output shows expensive typeclass/simp/grind/tactic work, automation annotations need tuning, or a proof/API design causes costly elaboration while source code should remain readable.
---

# Lean Performance, Profiling, And Automation Tuning

Use this skill when Lean code has bad elaboration performance, slow tactic proofs, expensive `simp`/`grind`, repeated typeclass search, or readability-preserving performance work is needed.

The goal is not to replace readable source code with explicit proof plumbing. The goal is to identify why Lean takes expensive paths, then improve the library’s automation, annotations, instances, or elaborators so concise code elaborates quickly.

## Core Principles

- Preserve user-facing readability. Avoid fixes that turn simple notation into explicit indices, proof terms, or low-level elaborator artifacts unless creating a temporary minimized repro.
- Measure before changing. Use profiler output to find the dominant category and command, then minimize that exact shape.
- Treat automation as an API. `simp`, `grind`, typeclass search, and custom tactics need curated theorem annotations and fast paths.
- Prefer narrow fast paths before broad automation. If a common indexing or coercion goal has a deterministic proof, add a lemma/elaborator/tactic branch for it before falling back to `grind`, `simp_all`, `omega`, or `nlinarith`.
- Keep annotations intentional. A theorem marked `[simp]` or `[grind]` affects global search behavior; bad annotations can silently make unrelated files slower.
- Avoid “just add more theorems” to automation sets. Every extra theorem may increase matching, instantiation, simplification, or normalization cost.

## First Triage

Run a full build first so imports and dependencies are ready:

```bash
lake build NumLean Tests
```

Profile one file:

```bash
lake env lean --profile -Dprofiler.threshold=0 --root=. path/to/File.lean
```

Collect project-wide data with the local profiler:

```bash
scripts/profile_lean_project.py
```

Use this as a sweep tool, not as the inner iteration loop. Run it once to find the
hot files and commands, then consume `perf/profile-data/latest.json`,
`perf/profile-data/logs/**`, and `perf/history.jsonl` while deciding what to
minimize. For targeted work, profile the specific file or repro directly with
`lake env lean --profile`; avoid repeatedly rerunning the project profiler unless
you need a fresh repo-wide sweep.

If the first sweep is too expensive, use a small slice only to get initial signal:

```bash
scripts/profile_lean_project.py --skip-build --limit 5 --skip-trace-profiler
```

Use trace profiling when command-level information is not enough:

```bash
lake env lean -Dtrace.profiler=true -Dtrace.profiler.output=/tmp/lean.trace --root=. path/to/File.lean
```

Use lower-noise single-file comparisons for candidate fixes:

```bash
lake env lean --profile -Dprofiler.threshold=0 --root=. perf/repros/MyRepro.lean
```

## Reading Profiler Output

Common cumulative categories and what they usually mean:

- `import`: file imports too much or imports expensive modules. Optimize dependency boundaries before proof code.
- `typeclass inference`: ordinary instance search is expensive. Look for ambiguous instances, missing expected types, expensive out-params, reducible wrappers, or overloaded notation.
- `sym typeclass inference`: symbolic automation, especially `grind`, is synthesizing many classes while exploring terms. Look for broad `[grind]` rules, generic proofs inside `get_elem_tactic`, or goals involving overloaded algebra/order.
- `simp`: simplifier is rewriting too much or looping through broad simp lemmas. Inspect simp sets and normal forms.
- `grind`, `grind simp`, `grind ematch`: `grind` is doing heavy search or E-matching. Inspect annotations, patterns, and generated instances.
- `tactic execution`: tactic itself is slow. Minimize the proof and inspect tactic-specific diagnostics.
- `elaboration` or `do element elaborator`: syntax/elaborator expansion is slow. Look at macros, notation elaborators, generated proof obligations, and repeated synthesis.
- `blocked (unaccounted)`: parallel tasks/imports or unclassified time. Compare with single-threaded and smaller repros.

Do not focus only on the single slowest line. Repeated medium-cost entries are often worse. Group profiler entries by problem name and inspect `count`, `total`, `min`, `max`, `mean`, and deviation.

## Minimize Correctly

Create repro files under `perf/repros/` or another non-imported location.

A good repro keeps:

- The same notation or tactic shape as the real slow code.
- The same imports, then progressively removes imports to isolate the source.
- The same expected types and implicit arguments.
- The same automation path: if real code uses `xs[map i]`, do not only test explicit `getElem` unless comparing hypotheses.

Compare variants that preserve readability:

- Original concise syntax.
- Same syntax with type ascriptions.
- Same syntax with local instances.
- Same syntax after changing a tactic fast path.
- Same syntax after changing theorem annotations.

Use explicit proofs only to understand what the fast path should prove. Do not leave explicit proof plumbing in library code just to improve speed.

## Diagnosing `get_elem_tactic` And Indexing Costs

Indexing notation often creates hidden goals such as:

```lean
(map i : HTuple Nat .leaf).toScalar < n
```

If the default proof is `by get_elem_tactic`, the tactic may fall back to broad automation. In NumLean, `get_tensor_elem_tactic` currently uses `grind` with the `grind_htuple_order` set. This can trigger symbolic typeclass inference for `LE`, `LT`, `OfNat`, `HAdd`, `HSMul`, `Lean.Grind.*`, and algebraic structures.

Good fix pattern:

- Identify the deterministic lemma that proves the common goal, for example a layout bound lemma.
- Add a narrow fast path in the tactic/elaborator before `grind`.
- Make the helper lemma’s conclusion match the generated goal as exactly as possible.
- Scan local hypotheses, including anonymous/internal loop membership proofs if needed.
- Fall back to the old broad tactic only when the fast path fails.

Bad fix pattern:

- Replacing readable `xs[map i]` with explicit `Nat` indices and proof terms everywhere.
- Adding global `[simp]` or `[grind]` annotations to many theorems without measuring instantiations.
- Calling `grind` earlier or with a larger theorem set.

When the cost is before the final proof tactic, inspect instance synthesis for `GetElem`, `SetElem`, coercions, and notation elaboration. A faster proof tactic will not help if Lean already spent time choosing generic instances or elaborating coercions.

## `simp` Annotations

Use `[simp]` for canonical normalization, not for arbitrary useful facts.

Good `[simp]` lemmas usually:

- Reduce projections after constructors: `fst (mk a b) = a`.
- Normalize wrapper/base round trips in one chosen direction.
- Push operations through transparent wrappers when that is the chosen normal form.
- Remove impossible or trivial branches.
- Are terminating and reduce syntactic complexity.

Avoid `[simp]` when:

- Both directions could be useful.
- The RHS is larger or introduces new redexes repeatedly.
- It unfolds expensive definitions globally.
- It performs domain-specific reasoning better left to a named theorem or local `simp [lemma]`.
- It causes coercion ping-pong between isomorphic types.

Directional simp variants used in Lean/mathlib-style APIs:

- `[simp]`: ordinary global simplification lemma.
- `[simp ↑]`: use when simplifying upward through coercions/projections in contexts that support upward/downward simp directions.
- `[simp ↓]`: use when simplifying downward through coercions/projections in contexts that support upward/downward simp directions.

Choose one normal form and annotate only the lemmas that move toward it. For isomorphic wrappers, this is usually projection-to-base for expressions and constructor form only when the expected type forces the wrapper.

Debug `simp` locally:

```lean
set_option trace.Meta.Tactic.simp true in
example ... := by
  simp
```

Other useful traces can include:

```lean
set_option trace.Meta.Tactic.simp.rewrite true
set_option trace.Meta.Tactic.simp.discharge true
```

Use trace output to find rewrite loops, unexpectedly used lemmas, or costly discharge tactics.

## `grind` Annotations

`grind` is powerful, but its performance depends heavily on annotations. The important question is not “can `grind` solve it?” but “how much search did it do, and did annotations guide it to the intended proof?”

Common annotation forms:

- `[grind]`: make theorem available to `grind` with default behavior.
- `[grind =]`: equality/congruence-style theorem used for normalization or equation reasoning.
- `[grind ←]`: use theorem right-to-left.
- `[grind →]`: use theorem left-to-right.
- `[grind .]`: expose a constructor/projector/discriminator-style theorem or generated theorem in the current namespace style.
- `[grind =_]`: oriented equality pattern where the left side is the relevant trigger side.
- `[grind _=_]`: equality pattern with both sides relevant as triggers.

Exact semantics depend on the Lean version; always verify with `#check`, `#print`, diagnostics, and profiler output in the current toolchain.

Use `[grind]` when:

- The theorem is broadly useful for first-order reasoning.
- It has stable, selective trigger patterns.
- It does not instantiate on every common term of a large type.
- It reduces a common proof obligation without broadening search too much.

Avoid `[grind]` when:

- The theorem has many unconstrained variables.
- It combines multiple domains and can trigger cascades.
- It needs arithmetic or typeclass-heavy side conditions for most instantiations.
- A local `grind [lemma]` is enough.

Prefer a narrow grind set for custom domains:

```lean
attribute [grind =] my_normal_form_lemma
attribute [grind ←] my_backward_rule
attribute [grind →] my_forward_rule
```

Use local theorem lists for experiments:

```lean
example ... := by
  grind [lemma₁, lemma₂]
```

Use diagnostics to see what happened:

```lean
set_option diagnostics true in
example ... := by
  grind
```

If available in the toolchain, use grind linting to inspect instantiation behavior:

```lean
#grind_lint check
#grind_lint check (min := 10) (detailed := 50)
#grind_lint check in MyNamespace
#grind_lint inspect MyNamespace.someLemma
```

Use the lint output as a reward signal: good annotations solve goals with fewer useless instantiations.

## Trigger Patterns And Constraints

For quantified lemmas, good trigger patterns are the difference between useful automation and combinatorial explosion.

Unconstrained pattern example:

```lean
axiom fMono : x ≤ y → f x ≤ f y
grind_pattern fMono => f x, f y
```

This can instantiate on many pairs. Add constraints when supported:

```lean
grind_pattern fMono => f x, f y where
  guard x ≤ y
  x =/= y
```

Use constraints to:

- Require a relevant side condition already exists.
- Avoid symmetric or reflexive duplicates.
- Prevent instantiating on terms that cannot contribute to the goal.
- Bound matching cascades.

When tuning patterns, measure both success and instantiation count. A proof that closes after thousands of instantiations may be worse than a local named proof.

## Typeclass Search Performance

When profiler output shows repeated `typeclass inference` or `sym typeclass inference`:

- Add expected types near overloaded literals and operators only in repros first; if it helps, consider API-level expected types or notation elaborator changes.
- Check instance priorities and out-parameters.
- Avoid overlapping generic instances that compete with common specialized instances.
- Prefer specialized high-priority instances for hot notation paths only if they are coherent and predictable.
- Avoid reducible wrappers that cause instance search to explore many equivalent representations.
- Ensure classes have `outParam`s only where the output is genuinely determined by inputs.

If adding a specialized instance helps only marginally, the main cost is probably proof automation or generated goals, not instance selection.

## Tactic Diagnostics

Useful options and traces vary by Lean version, but start with:

```lean
set_option profiler true
set_option trace.profiler true
set_option diagnostics true
```

For tactic-specific traces, try targeted `trace.Meta.Tactic.*` options, for example:

```lean
set_option trace.Meta.Tactic.simp true
set_option trace.Meta.Tactic.simp.rewrite true
set_option trace.Meta.Tactic.simp.discharge true
```

For `grind`, prefer diagnostics and linting when available:

```lean
set_option diagnostics true in
example ... := by
  grind
```

Do not enable broad traces globally in large files unless necessary. They can produce huge logs and change timing behavior.

## Optimization Workflow

1. Run profiler on the slow file and identify the dominant category.
2. Group entries by name and count repeated medium-cost problems.
3. Create a minimized repro preserving the same syntax/tactic shape.
4. Test hypotheses one at a time:
   - Expected types.
   - Specialized instances.
   - Narrow tactic fast path.
   - Annotation changes.
   - Import reduction.
5. Keep only changes that improve the concise form, not just explicit proof variants.
6. Verify the original file and a representative downstream file.
7. If changing annotations, run focused proof/tactic tests and inspect instantiation behavior.
8. Record findings in `perf/repros/` or notes if the fix is non-obvious.

## Common Recommendations

- For indexing APIs, build direct elaborator/tactic support for common validity proofs.
- For `simp`, maintain stable normal forms and avoid bidirectional wrapper simplification.
- For `grind`, add annotations sparingly and measure instantiation counts.
- For custom notation, avoid expanding to broad automation if a deterministic lemma applies.
- For slow tests, separate library API performance problems from intentionally expensive proof/tactic benchmarks.
- For imports, split heavy theorem modules away from data/notation modules when possible.

## Anti-Patterns

- “Fixing” performance by making all user code explicit and unreadable.
- Adding `[simp]` to every theorem that helped once.
- Adding `[grind]` to a theorem with unconstrained variables without checking instantiations.
- Replacing a small deterministic proof with `grind` or `simp_all`.
- Optimizing a minimized variant that no longer uses the real slow notation.
- Treating import time as a local command problem.

## What To Report

When summarizing performance work, include:

- The slow file and command(s).
- Baseline cumulative categories.
- Minimized repro location.
- Hypotheses tested and whether they helped.
- The accepted fix and why it preserves readability.
- Before/after timings for the original file and a smaller repro.
- Remaining risks, especially changed automation annotations or instance priorities.
