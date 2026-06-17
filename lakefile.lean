import Lake
open System Lake DSL

package «NumLean» where
  version := v!"0.1.0"
  keywords := #["math"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

target libNumLeanNative pkg : Dynlib := do
  let entries ← (pkg.dir / "c").readDir
  let cFiles := entries.filterMap fun entry =>
    if entry.path.extension == some "c" then
      some entry.path
    else
      none
  let objJobs ← cFiles.mapM fun cFile => do
    let srcJob ← inputFile cFile true
    let oFile := (pkg.buildDir / "c" / cFile.fileName.get!).withExtension "o"
    buildO oFile srcJob #["-I", (← getLeanIncludeDir).toString] #["-fPIC"] "cc" getLeanTrace
  buildSharedLib "NumLeanNative" (pkg.sharedLibDir / nameToSharedLib "NumLeanNative")
    objJobs #[] #[] #[] "cc" getLeanTrace

@[default_target]
lean_lib NumLean where

lean_lib NumLean.Data.Float32Array where
  moreLinkLibs := #[libNumLeanNative]
  precompileModules := true

lean_lib NumLean.Data.FloatArray.TensorOps where
  moreLinkLibs := #[libNumLeanNative]
  precompileModules := true

lean_exe floatArrayTensorBenchmark where
  root := `Benchmarks.FloatArrayTensorBenchmark
  supportInterpreter := true
  moreLinkLibs := #[libNumLeanNative]

lean_exe forAllBenchmark where
  root := `Benchmarks.ForAllBenchmark
  supportInterpreter := true

@[test_driver]
lean_exe tests where
  root := `Tests
  supportInterpreter := true
  moreLinkLibs := #[libNumLeanNative]

lean_lib Tests.Float32ArrayEval where
  precompileModules := true

lean_lib Tests.TensorIndexRangeIterators where

lean_lib Tests.TensorIndexIteratorCompiler where

lean_lib Tests.HTupleRangeIterators where

lean_lib Tests.HVector where

lean_lib Tests.VectorRangeIterators where

lean_lib Tests.TupleOrderNotation where

lean_lib Tests.ForAllNotation where

lean_lib Tests where
