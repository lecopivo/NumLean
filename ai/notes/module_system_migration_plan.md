# NumLean Module System Migration Plan

## Goal

Move NumLean to Lean's module system without changing program or proof content.

The intended mechanical migration pattern is:

```lean
module

public import Some.Dependency
public import Another.Dependency

@[expose] public section
```

For files that need implementation details from an imported module, add a local non-public `import all` for that module as needed:

```lean
public import Batteries.Data.FloatArray
import all Batteries.Data.FloatArray
```

`public import all M` is not valid syntax. Use `public import M` plus `import all M` when both public API import and local implementation access are needed.

## Hard Constraints

Do not make these changes:

- Do not change function definitions.
- Do not rewrite theorem/proof bodies to different proof terms unless explicitly requested.
- Do not replace proofs with `sorry`.
- Do not add axioms or bridge declarations to avoid fixing visibility/import issues.
- Do not change semantics to satisfy the module checker.

Allowed changes:

- Add `module` at the top of Lean source files.
- Change ordinary `import` declarations to `public import` when the dependency is part of the file's public API.
- Add `@[expose] public section` after imports.
- Remove `private` from declarations that are used by public declarations in the same file.
- Add local `import all M` when a proof or definition relies on implementation details from `M` that are not available through `public import M`.
- Mark definitions, sections, or imports as `meta` when used from meta code.
- Split runtime and meta sections if a file contains both runtime declarations and meta-only declarations.

## What Was Learned

Lean's module system distinguishes several concepts that old files often blurred:

- Visibility of a declaration name.
- Availability of a declaration body for unfolding/reduction.
- Whether an import is re-exported to downstream importers.
- Whether a declaration can be referenced from public declarations.
- Whether code is runtime code or meta code.

`public section` makes declarations public, but public declarations are not automatically exposed for unfolding by downstream modules. `@[expose] public section` is the right default for this project because many existing proofs and definitions expect old-style unfolding behavior.

Private declarations cannot be referenced from public declarations under the new rules unless compatibility options are enabled. Since the goal is to remove `backward.*`, helpers used by public declarations must not be `private`.

Some imported names are public, but their bodies are not available for reduction. If an existing proof relies on unfolding an imported implementation, the correct migration is to add a local `import all M`, not to rewrite or weaken the proof.

Meta declarations and runtime declarations need correct section/import annotations. Errors around using runtime declarations in meta code or vice versa can often be fixed by `meta section`, `public meta section`, or `public meta import`, depending on the dependency direction.

## Known Issue Classes And Fixes

### Private Declaration Used In Public Declaration

Typical error:

```text
Unknown identifier somePrivateHelper
```

or a module-system diagnostic mentioning private declarations in public declarations.

Safe fix:

- Remove the `private` annotation from the helper.
- Do not change the helper's definition.
- If several related helpers are private and used by a public declaration, remove `private` from all required helpers.

Example encountered:

- `NumLean/Meta/Deriving/Algebra.lean`
- Helpers such as `checkSupported`, `hasPropField`, and `checkNoPropFields` were private but referenced by public/meta deriving code.

### Imported Implementation Body Not Available

Typical symptom:

- A proof that used to close by `simp`, `rfl`, or reduction now fails.
- The name exists, but its body is opaque from the importing file.

Safe fix:

- Add `import all M` for the specific dependency whose implementation body is needed.
- Keep the existing proof unchanged first.
- Only if the exact same proof still fails, inspect whether another imported module also needs `import all`.

Example encountered:

- `FloatArray.size` and related FloatArray operations from `Batteries.Data.FloatArray` are public names, but their implementation bodies may not be unfoldable through ordinary public import.
- If NumLean proofs rely on unfolding them, add:

```lean
public import Batteries.Data.FloatArray
import all Batteries.Data.FloatArray
```

### Public Import Versus Local Import All

Use this pattern:

```lean
public import M
import all M
```

Meaning:

- `public import M` re-exports the public API dependency to downstream users.
- `import all M` gives the current file access to implementation details from `M`.
- The `import all` is local; it does not make private implementation details part of this module's public API.

Do not use:

```lean
public import all M
```

Lean rejects this syntax.

### Meta Code Errors

Typical symptoms:

- A declaration used only by elaborator/tactic code is rejected because it is not in a meta context.
- A meta declaration depends on imports that were only imported for runtime use.

Safe fixes:

- Put meta declarations in `meta section` or `public meta section`.
- Mark individual declarations `meta def` when only one declaration needs it.
- Use `public meta import M` if downstream meta code needs the imported module through this file.
- Split files into runtime and meta sections if necessary.

Do not rewrite the meta function bodies while doing this.

### Backward Compatibility Options

The migration should remove all of these rather than rely on them:

```lean
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn true
set_option backward.proofsInPublic true
```

Safe replacements:

- For `backward.privateInPublic`: remove `private` from declarations used by public declarations.
- For `backward.proofsInPublic`: expose declarations with `@[expose] public section` and add local `import all` where imported proof bodies/implementation bodies are needed.

## Retry Workflow After Revert

1. Revert the previous migration attempt.
2. Generate a topological import order for the NumLean files before editing.
3. Make a mechanical pass over Lean files in import order:
   - Add `module` before imports.
   - Convert imports to `public import`.
   - Add `@[expose] public section` after the imports.
4. Do not touch any function/proof bodies in the mechanical pass.
5. Rebuild incrementally in the same order instead of repeatedly rebuilding the whole project.
6. For each failure, classify it before editing:
   - Private helper used publicly: remove `private` only.
   - Missing imported implementation body: add local `import all` only.
   - Meta/runtime mismatch: add/split `meta` annotations/sections/imports only.
   - Real theorem/proof failure unrelated to visibility: stop and inspect; do not replace with `sorry`.
7. Re-run the smallest relevant build target after each small batch of related fixes.
8. Search for forbidden changes before considering the migration complete:
   - `sorry` additions.
   - New axioms.
   - Modified function/proof bodies beyond visibility/import/meta annotations.
   - Remaining `set_option backward.` usages.

## Topological Order Strategy

Mathlib has a helper script that prints modules in import-DAG order:

```text
.lake/packages/mathlib/scripts/topological_sort.py
```

The mathlib scripts README explains how to use these tools in downstream repositories. The relevant point is that scripts depend on sibling helper files in the same directory. For robust downstream use, copy at least these files into a local `scripts/` directory if direct execution from `.lake/packages/mathlib/scripts` is inconvenient:

```text
topological_sort.py
dag_traversal.py
```

Other backward-compatibility migration scripts also use `set_option_utils.py`, but `topological_sort.py` itself only imports `dag_traversal.py`.

The script uses `DAG.from_directories(Path("."))`, so run or adapt it from the project root. It prints dependencies before importers by default: if `A` imports `B`, then `B` appears before `A`. That is the right order for migration because lower-level files can be converted and checked before files that import them.

If the script assumes Mathlib-specific paths or module names, copy or minimally adapt it for NumLean. The important behavior is:

- Build the import graph from the current directory.
- Sort leaves-last so imported modules come before importing modules.
- Optionally filter stdin to only the files/modules being migrated.

Useful command shape:

```bash
python .lake/packages/mathlib/scripts/topological_sort.py
```

If Python cannot find `dag_traversal`, run it with the mathlib scripts directory on `PYTHONPATH`:

```bash
PYTHONPATH=.lake/packages/mathlib/scripts python .lake/packages/mathlib/scripts/topological_sort.py
```

The README notes that module-name derivation assumes a Mathlib-style layout where `Foo/Bar.lean` maps to module `Foo.Bar`, with no `srcDir` indirection. NumLean appears to follow this style for `NumLean/...`, so this should work. If a nonstandard source directory is involved, adapt the directory roots passed to the DAG construction or use `dag_traversal.py` with directory options where supported.

`dag_traversal.py` can also run a command directly over the import graph. Its README usage is:

```bash
scripts/dag_traversal.py --forward 'lake build {}'
scripts/dag_traversal.py --backward --module 'echo {}'
scripts/dag_traversal.py --forward -j4 'my_script {}'
```

For this migration, the useful direction is forward/root-first: imported modules are processed before importers. If using the copied scripts locally, an adapted command could be:

```bash
scripts/dag_traversal.py --forward 'lake env lean {}'
```

Use `stop_on_failure` behavior when invoking from Python, or run with low parallelism manually, so the first failing module is easy to inspect and fix.

After getting a module name such as `NumLean.Foo.Bar`, build just that module:

```bash
lake env lean NumLean/Foo/Bar.lean
```

or, if a Lake target exists for the module:

```bash
lake build NumLean.Foo.Bar
```

This keeps the migration tight: edit the next file in dependency order, check that file or module, fix only visibility/import/meta issues, then continue.

## Verification Commands

Use these checks during the retry:

```bash
lake build
```

```bash
rg 'set_option backward\.' NumLean test
```

```bash
rg '\bsorry\b' NumLean test
```

The `sorry` search must be compared against the reverted baseline, because some existing files may already contain `sorry`. The migration must not introduce new placeholders.

## Files And Areas Already Identified As Sensitive

- `NumLean/Meta/Deriving/Algebra.lean`: private helpers used by public/meta deriving code.
- `NumLean/Data/Scalars/Float64/*`: proofs may depend on FloatArray implementation details; prefer local `import all Batteries.Data.FloatArray` rather than proof rewrites.
- `NumLean/Data/HTuple/RangeNotation.lean`: contains syntax/meta pieces and may require runtime/meta section separation.
- `NumLean/Tactic/ApplyRuleSets/*.lean`: tactic code likely needs `meta` sections/imports.
- `NumLean/Meta/HierarchyGraph.lean`: meta-heavy file; check import and section annotations carefully.

## Important Reminder

The safe migration is mostly a visibility/import/meta-annotation migration. If a build failure appears to require changing a function definition or replacing a proof, stop and look for a missing `import all`, missing `@[expose]`, missing `public`, or invalid `private` reference first.
