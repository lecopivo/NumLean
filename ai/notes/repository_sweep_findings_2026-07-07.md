# Repository Sweep Findings - 2026-07-07

This is a repository-wide API and organization sweep. It focuses on inconsistencies, missing API, missing functions/theorems, misplaced definitions/tests, naming issues, and general library cleanup opportunities.

## Highest Priority

### [DONE] Fix broken self-update theorem statements before proving them

- `NumLean/Data/Vector/TensorType.lean:97-106` declares `Vector.getElem_copySliceSelf` as `proof_wanted`, but the statement uses undeclared variable `i` in the RHS while the quantified index is `j`.
- `NumLean/Data/Vector/TensorType.lean:113-124` declares `Vector.getElem_swapSliceSelf` as `proof_wanted`, but the statement uses undeclared variable `k` while the quantified index is `j`.
- These should be corrected before proof work starts; otherwise downstream interface lemmas cannot be proved cleanly.

### [DONE] Complete the self-update theorem API

- `NumLean/Interfaces/TensorType.lean:101-110` has `proof_wanted TensorType.get_copySliceSelf`.
- `NumLean/Interfaces/TensorType.lean:113-124` has `proof_wanted TensorType.get_swapSliceSelf`.
- `NumLean/Data/Vector/TensorAlgebra/Lemmas.lean:52-61` has `proof_wanted Vector.getElem_tensorAxpySelf`.
- `NumLean/Interfaces/TensorAlgebra.lean:249-260` has `proof_wanted TensorRingOps.get_tensorAxpySelf`.
- These are conspicuous gaps because the non-self versions are already proved and marked simp, e.g. `TensorType.get_copySlice` and `TensorRingOps.get_tensorAxpy`.

### [DONE] Make tensor/vector/product aggregate imports match user expectations

- `NumLean/Data/Tensor.lean:3-6` imports only `Index`, `Layout`, `Rank`, and `Shape`; it does not import `Tensor.Basic`, `Tensor.Ops`, `Tensor.Algebra`, `Tensor.Notation`, `Tensor.View`, or slice notation.
- `NumLean/Data/Vector.lean:3-7` omits `Vector.LayoutMap`, `Vector.TensorType`, `Vector.TensorType.CopySlice`, and `Vector.TensorAlgebra`.
- `NumLean/Data/Prod.lean:3-4` omits product algebra modules under `NumLean/Data/Prod/Algebra/*`.
- Root `NumLean.lean` imports many omitted leaves individually, which suggests the local aggregators are incomplete rather than intentionally minimal.

### [DONE] Expose or intentionally retire `Tensor.Algebra.Equiv`

- `NumLean/Data/Tensor/Algebra/Equiv.lean:1-2` uses plain `import`, lacks the usual `module` header and `@[expose] public section`.
- It is not imported by `NumLean/Data/Tensor/Algebra.lean:3-5` or by the root `NumLean.lean` tensor section.
- It contains useful API such as `finvecEquiv`, `getElem_matVecMul_fin`, `getElem_vecMatMul_fin`, and `getElem_matMul_fin` at `NumLean/Data/Tensor/Algebra/Equiv.lean:107`, `159`, `183`, and `208`.
- Decide whether this is public API. If yes, add the module boilerplate and import it from `Tensor/Algebra.lean`; if no, move it to tests/notes/scratch.

### [SKIPPED] Provide a lawful Float64 tensor algebra instance, or document why not

- `NumLean/Data/Scalars/Float64/TensorAlgebra.lean:117-126` defines `TensorRingOps Float64Vector Float`.
- No `LawfulTensorRingOps Float64Vector Float` instance was found under `NumLean/Data`.
- High-level tensor algebra theorems in `NumLean/Data/Tensor/Algebra/Lawful.lean` require `[LawfulTensorRingOps Ks K]`, so Float64 has executable optimized operations but apparently lacks proof-facing simp/theorem support.

### Fill the multiplicative fold/product API

- `NumLean/Data/Vector/TensorAlgebra/Lemmas.lean:118-123` comments out `tensorProd_eq_prod` because a variant of `Fold.fold_eq_sum` is missing.
- Existing roadmap `ai/notes/fold_range_api_roadmap.md:205-218` already proposes `Fold.fold_eq_fin_prod` and `Fold.prod_entries_eq_fin_prod`.
- This blocks a natural theorem for `tensorProd`, currently defined in `NumLean/Data/Vector/TensorAlgebra/Core.lean:65-70`.

## Fold And Range API

### [DONE] Promote finite range conveniences from notes to API

- `NumLean/Interfaces/Fold/Fin.lean` has the core `FinRangeView`, but several planned conveniences remain absent.
- `ai/notes/fold_range_api_roadmap.md:196-216` lists missing public helpers: `Fold.FinRangeView.entries_eq_finRange`, `toFin_fromFin`, `fromFin_toFin`, `rangeIsoFin`, `Fold.fold_eq_fin_sum`, `Fold.fold_eq_fin_prod`, `Fold.sum_entries_eq_fin_sum`, and `Fold.prod_entries_eq_fin_prod`.
- Tests cover core finite rewrites in `Tests/FoldFin.lean`, but not the full proposed big-operator wrapper suite.

### Replace entry-indexed fallback views with closed-form views where feasible

- `NumLean/Interfaces/Fold/Fin.lean:187-192` notes that the Int range finite view should expose `(hi - lo).toNat` and `lo + i` instead of the current enough-to-rewrite fallback.
- `NumLean/Data/Prod/Fold.lean:167-179` uses an entry-indexed, noncomputable product finite view with `DecidableEq`.
- `NumLean/Data/FinHTuple/Fold.lean:139-147` similarly uses an entry-indexed zero-range HTuple view.
- This overlaps with `ai/notes/fold_range_api_roadmap.md:254-316`.

### Keep interface aggregates free of concrete data imports

- `NumLean/Interfaces/Fold.lean:3-11` imports `NumLean.Data.Prod.Fold` from inside an `Interfaces` aggregate.
- If product fold instances are meant to be standard interface exports, document that boundary. Otherwise, move the import to a data aggregate or split an interface-only fold aggregate from a standard-instances aggregate.

### Normalize product/HTuple fold theorem names

- `ai/notes/fold_range_api_roadmap.md:327-333` proposes names like `Fold.fold_htuple_pair_eq_fold_htuple_prod` and `Fold.entries_htuple_pair_eq_entries_htuple_prod`.
- Current public theorem naming in `NumLean/Data/HTuple/Fold.lean:299-312` is oriented as `fold_htuple_prod_eq_pair`.
- Consider aliases in both directions with stable public names so users do not have to remember which orientation was implemented first.

### [DONE] Deduplicate subtype/list extensional helpers

- Similar private list/subtype extensionality helpers appear in `NumLean/Interfaces/Fold/Fin.lean:84-100` and `NumLean/Data/FinHTuple/Fold.lean:17-35`.
- A small shared helper would reduce duplicated proof infrastructure.

### Revisit stale fold notes

- `ai/notes/fold_reasoning.md:166-181` refers to `FinHTuple.zeroRangeRangeIsoFin`.
- Actual code appears to have `zeroRangeEquivFin` and `zeroRangeRangeEquivFin` in `NumLean/Data/FinHTuple/Fold.lean:85-95`; no `zeroRangeRangeIsoFin` was found.
- Either add the ordered `RangeIso` or update the note.

## Tensor And Layout API

### [DONE] Split reshape/reindexing out of `Tensor.Basic`

- `NumLean/Data/Tensor/Basic.lean:254-303` contains `indexTypeOfShape`, `IndexTypeOfShape`, `valid_reshape_tactic`, and `Tensor.reshape`.
- This is useful API but conceptually separate from core tensor storage/get/set/extensionality. Consider `Tensor/Reshape.lean` or `Tensor/Reindex.lean`.
- `NumLean/Data/Tensor/Basic.lean:301` already notes a missing `.reindex` API that directly gives the new index type `J`.

### Clarify `Tensor.Ops`

- `NumLean/Data/Tensor/Ops.lean:3-5` only imports `Tensor.Algebra.Lawful` and exposes no definitions.
- The operational definitions live in `NumLean/Data/Tensor/Algebra/Ops.lean`; the current `Tensor.Ops` name is likely misleading.

### Fix row/column layout shape ergonomics

- `NumLean/Data/Tensor/Layout.lean:76-86` notes that `Layout.row` and `Layout.col` currently return singleton-product source shapes (`h(1).prod cols` and `rows.prod h(1)`).
- The TODO says they should produce `Layout cols (rows.prod cols)` and `Layout rows (rows.prod cols)`.
- This matters for ergonomic row/column views and downstream proofs.

### Promote `Layout.map` through the right aggregate

- `NumLean/Data/Vector/LayoutMap.lean:21-40` defines useful `Tensor.Layout.map` and `getElem_map`.
- It is not imported by `NumLean/Data/Vector.lean`; it only comes in indirectly via tensor algebra core.
- If this is public vector/layout API, import it from the vector aggregate or move it under `Tensor/Layout` if the namespace is the stronger signal.

### Improve tensor view docs and ownership wording

- `NumLean/Data/Tensor/View.lean:15-18` has awkward wording about slicing and ownership, plus a TODO saying it applies more to `InjectiveView` than plain `View`.
- Clarify the intended mutation/aliasing discipline for plain views vs injective views.

## Scalar And Flat Representation API

### Decide scalar parity goals across Float32/Float64/Complex/UInt8

- `NumLean/Data/Scalars/Float64.lean:9-10` imports `TensorType` and `TensorAlgebra`.
- `NumLean/Data/Scalars/Float32.lean:3-8`, `Complex32.lean:3-7`, `Complex64.lean:3-7`, and `UInt8.lean:3-7` do not import comparable tensor type/algebra support.
- This may be intentional because only Float64 has optimized operations, but it is an API inconsistency users will notice.

### Complete Complex flat representations or mark them explicitly experimental

- `NumLean/Data/Scalars/Complex32/HasFlatRepr.lean:12-18` comments out default and alternate representations, including `HasFlatRepr Complex32 Float32Vector 2` and `HasFlatRepr Complex32 ByteVector 8`.
- `NumLean/Data/Scalars/Complex64/HasFlatRepr.lean:15-17` similarly has commented representation targets.
- Existing plan `ai/notes/basic_scalar_and_vector_flat_repr_plan.md` overlaps with this area.

### Finish or remove stale commented vector/scalar instances

- `NumLean/Data/Scalars/UInt8/VectorType.lean:10` comments out `VectorType ByteVector UInt8`.
- `NumLean/Data/Scalars/UInt8/HasFlatRepr.lean:10` comments out `HasDefaultFlatRepr UInt8 ByteVector 1`.
- `NumLean/Data/Scalars/Float64/HasFlatRepr.lean:10-12` comments out Float default and byte representations.
- These comments should become issues/notes, real code, or be deleted if obsolete.

### Clarify `HasDefaultFlatRepr` resolution behavior

- `NumLean/Interfaces/HasFlatRepr/Basic.lean:65-66` has `HasDefaultFlatRepr` as a marker class.
- `NumLean/Interfaces/HasFlatRepr/Sigma.lean:13` and `Prod.lean:71` have TODOs about better placement/inference and representation layout.
- Add docs or examples showing the intended instance search story once scalar/vector targets mature.

## Interfaces And Algebra Organization

### Add an aggregate for `Interfaces.VectorType`

- `NumLean/Interfaces/VectorType/Basic.lean` exists, but no `NumLean/Interfaces/VectorType.lean` aggregate was found.
- Most other interface families have both an aggregate and leaf modules (`Algebra`, `Module`, `HasFlatRepr`, `Fold`).
- Add `NumLean/Interfaces/VectorType.lean` or document why `Basic` is the only public entry point.

### Move `RealModel` examples out of the interface module

- `NumLean/Interfaces/RealModel.lean:39-53` contains a TODO about moving `NatCast`/`IntCast` to `*Ops` and several inference examples.
- Examples belong better in tests or notes; the interface module should stay focused on declarations and laws.

### Review large commented API blocks

- `NumLean/Interfaces/VectorType/Basic.lean:119-153` comments out useful `uget`/`uset` theorems.
- `NumLean/Interfaces/Fold/Filter.lean:78-89` comments out an alternate affector lemma.
- If these are still desired, turn them into explicit roadmap items; otherwise remove stale commented declarations.

## Experimental And Compiler API

### Remove tests from the experimental library aggregate

- `NumLeanExperimental.lean:13` imports `NumLean.Experimental.Data.DyadicInterval.Tests`.
- The file itself is a test/example namespace (`NumLean/Experimental/Data/DyadicInterval/Tests.lean:9-58`).
- Test-only modules should be imported from `Tests`, not by the library aggregate.

### Simplify `NumLeanExperimental.lean` imports

- `NumLeanExperimental.lean:3-42` imports both aggregate modules and individual leaves.
- Prefer importing aggregates only, then ensure the aggregates themselves expose their intended public leaves. This reduces duplication and avoids accidentally pulling test modules.

### Extend C compiler executable semantics to cover declared IR types/ops

- `NumLean/Experimental/Meta/CCompiler/IR.lean:16-17` includes `float64` and `float32` types.
- `NumLean/Experimental/Meta/CCompiler/IR.lean:61-66` includes unary `sqrt`, `abs`, and casts.
- `NumLean/Experimental/Meta/CCompiler/Semantics.lean:139-177` evaluates Nat/int/bool binops and int unary ops, but not float arithmetic or `sqrt`.
- `Tests/CCompilerIRSemantics.lean` currently covers usize/fill/copy-style cases, not float IR semantics.

### Avoid source-tree mutation from `@[extern_c]`

- `NumLean/Experimental/Meta/CCompiler/Extern.lean:191-197` creates directories and writes generated C files during elaboration.
- Generated outputs currently exist under `c/generated/extern_fill.c` and `c/generated/extern_scalar.c`.
- This is surprising for an attribute and can dirty the repo during tests. Consider routing through Lake build directories, requiring an explicit generation command, or documenting the side effect prominently.

### Clean up C compiler docs

- `NumLean/Experimental/Meta/CCompiler/Readme.md:4-6` has spelling/grammar issues.
- The generated C example in that readme reportedly has an extra closing brace around line 37.
- The warning should mention that `@[extern_c]` writes into `c/` during elaboration.

### Decide the fate of `IdxP`

- `NumLean/Experimental/Data/IdxP.lean:148-219` and later blocks through about line 639 contain large commented-out APIs for decidability, coercions, extensionality, finiteness, product merge/div/mod, and sum encode/decode.
- This is either missing API or stale design. It should be split into active implementation, roadmap note, or removed.

### Complete interval law coverage consistently

- `NumLean/Experimental/Interfaces/Interval/Lawful.lean:38-39` defines `LawfulNatPow`.
- `NumLean/Experimental/Data/RatInterval/Basic.lean:82-86` and `216-220` define `NatPow`/`Pow Int` and grouped lawful instances, but no `LawfulNatPow` instance was found there.
- `NumLean/Experimental/Data/DyadicInterval/Basic.lean:301-384` proves `LawfulNatPow`, but the interval hierarchy also has `Inv`/`Div`/`GroupOps`/`FieldOps` classes without corresponding DyadicInterval instances in that file.

### Move experimental examples to tests where they are smoke tests

- Candidate example blocks include `NumLean/Experimental/Data/HList/Ops.lean:105-111`, `HList/Notation.lean:160-170`, `HList/RangeIterator.lean:419-448`, `KernelExpr/HasKernelExpr.lean:279-298`, and `FloatP.lean:52-62`.
- Keeping examples in library modules is fine when they document API, but smoke tests should live under `Tests` to keep library files lean.

## Tests, Lake, And CI

### Remove stale Lake test targets

- `lakefile.lean:65-68` declares `Tests.TensorIndexRangeIterators` and `Tests.TensorIndexIteratorCompiler`.
- No matching `Tests/TensorIndexRangeIterators.lean` or `Tests/TensorIndexIteratorCompiler.lean` files were found.
- Either add the files or remove the targets.

### Make the test driver run more than one runtime test

- `Tests.lean:3-31` imports many tests, but `main` only runs `NumLean.Tests.Float64TensorAlgebraEval.run` at `Tests.lean:35-37`.
- Many files are compile-time example tests, which is fine, but runtime/eval tests should be called from `main` or documented as compile-only.

### Add proof-facing tensor algebra tests

- `Tests/Float64TensorAlgebraEval.lean` covers runtime eval for add/sub/smul/dot/matvec/matmul/strided views.
- Add proof tests for API such as `Tensor.getElem_add`, `Tensor.getElem_smul`, `getElem_matVecMul_fin`, `getElem_vecMatMul_fin`, and `getElem_matMul_fin` once `Tensor.Algebra.Equiv` is exposed.
- Add tests demonstrating that Float64 tensor algebra theorems work through `[LawfulTensorRingOps Float64Vector Float]` once that instance exists.

### Add parity tests for scalar tensor/vector APIs

- Once Float32/Complex32/Complex64 tensor or flat representation support exists, add tests mirroring Float64 coverage.
- Current coverage is heavily Float64-oriented.

### Normalize unusual test imports

- `Tests/HVector.lean:3-5` mixes `public import`, `public meta import`, and `import all` for the same family.
- `Tests/BTupleFold.lean:3-5` similarly mixes `public import`, `import all`, and `public meta import`.
- Other tests use `public meta import` where ordinary imports may suffice. This may be harmless, but it makes dependency intent hard to read.

### Treat high-heartbeat typeclass tests as performance contracts

- `Tests/TypeclassPerformance.lean` uses many `set_option maxHeartbeats` values, including very high bounds.
- If these are intended performance regressions tests, document the expected budget and what scenario each block protects.

## Tactics And Meta

### Harden or reframe `TBounds`

- `NumLean/Tactic/TBounds.lean:7-11` explicitly says the tactic is AI-generated and spec-by-test.
- It contains typos (`Discusting`, `effectivelly`) and hard-coded row-major lemmas up to rank 4 (`row_lt`, `row3_lt`, `row4_lt`) at `NumLean/Tactic/TBounds.lean:19-48`.
- Consider a recursive strategy for rank greater than 4, or document the rank coverage and keep tests aligned.

### Fix linter warning wording

- `NumLean/Meta/GetElemSetElemLinter.lean:52-53` says: `The left-hand side ... get or set element syntax...` and `writting`.
- Suggested wording: `The left-hand side of equality theorem ... uses get/set element syntax in a non simp-normal form... writing ...`.

### Review `import all` and `public meta import` usage

- Grep found `import all` in normal library files such as `NumLean/Data/Scalars/Float64/Float64Array.lean`, `Float64Vector.lean`, `Float64/VectorType.lean`, `Float64/TensorType.lean`, and `NumLean/Experimental/Data/HList/*`.
- Some `public meta import` occurrences are appropriate for elaborators/tactics, but some tests and data files may not need public/meta exposure.
- A pass to make imports ordinary/private/public/meta only where needed would improve compile boundaries.

## Repository Hygiene And Naming

### Clean scratch and local artifacts

- `git status --short --untracked-files=all` reports untracked root scratch files: `Power.lean`, `Power2.lean`, `ScratchGemmProof.lean`, `ScratchGemmRewriteProbe.lean`, `todos.org`, and many `perf/repros/*.lean` files.
- `ScratchGemmRewriteProbe.lean:155` and `Power.lean:47,60` contain `sorry` in local scratch code.
- Decide which should become tests/perf repros and which should be ignored or moved out of the repo root.

### Remove or justify tracked non-source artifacts

- `Pasted image.png` is tracked by git. If it is documentation material, move it under a documented assets directory; otherwise remove it from version control.
- `ProbeRowMajor.lean` is tracked at the repository root. If it is still useful, move it under `Tests`, `perf/repros`, or `Scratch`/`Examples`; otherwise retire it.

### Keep ignored backup/autosave files out of searches

- `.gitignore:3-5` already ignores `*~`, `#*`, and `*#`.
- The working tree still contains many ignored backup/autosave files visible to file searches, such as `NumLean/Data/#Float32Array.lean#`, `Tests/#CCompiler.lean#`, and `Benchmarks/#ForAllBenchmark.lean#`.
- These are not tracked, but removing local copies would make repository-wide searches cleaner.

### Fix `.gitignore` duplication

- `.gitignore:1-2` repeats `/.lake` twice.

### Improve README and note naming consistency

- `README.md:3` says `aimling`; fix to `aiming` and consider expanding the README beyond one sentence.
- Existing notes use mixed naming styles: `TDerivPlan.md`, `TensorSliceMapPlan.md`, lower_snake_case notes, and the typo `fold_extensional_resoning.md`.
- Consider normalizing note names to lower-kebab-case or lower-snake-case and fixing `resoning` to `reasoning` if links allow.

### Fix typos in comments and docs

- `NumLean/Interfaces/TensorType.lean:50` says `infrastracture`.
- `NumLean/Data/Tensor/Basic.lean:301` says `direcly`.
- `NumLean/Interfaces/SetElem.lean:123` says `remplate`.
- `NumLean/Tactic/TBounds.lean:7-10` has `Discusting` and `effectivelly`.
- `NumLean/Meta/GetElemSetElemLinter.lean:53` has `writting`.

## Existing Notes That Overlap

- `ai/notes/fold_range_api_roadmap.md` already covers many fold/range API gaps and should remain the primary roadmap for finite views and big-operator wrappers.
- `ai/notes/fold_extensional_resoning.md` captures the intended proof style for self-update/swap/copy-slice proofs; it directly overlaps with the `proof_wanted` self-update gaps.
- `ai/notes/tensor_algebra_fold_bridge_plan.md` overlaps with tensor algebra fold bridge work.
- `ai/notes/basic_scalar_and_vector_flat_repr_plan.md` overlaps with scalar/vector flat representation gaps.
- `ai/notes/module_system_migration_plan.md` may overlap with import/public/meta cleanup.

## Suggested First Batch

1. Correct the broken `j`/`i` and `j`/`k` self-update theorem statements.
2. Prove vector self-update lemmas, then lift them to `TensorType` and `TensorRingOps` interface lemmas.
3. Fix public aggregates: `Tensor`, `Vector`, `Prod`, add `Interfaces.VectorType`, and expose or retire `Tensor.Algebra.Equiv`.
4. Add the missing fold product wrappers needed by `tensorProd_eq_prod`.
5. Remove stale Lake targets and move `DyadicInterval.Tests` out of `NumLeanExperimental.lean`.
6. Decide whether Float64 optimized tensor algebra should be lawful now; if yes, add `LawfulTensorRingOps Float64Vector Float` and proof tests.
