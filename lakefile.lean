import Lake
open System Lake DSL

partial def collectCFiles (dir : FilePath) : IO (Array FilePath) := do
  let entries ← dir.readDir
  let mut files := #[]
  for entry in entries do
    if (← entry.path.isDir) then
      files := files ++ (← collectCFiles entry.path)
    else if entry.path.extension == some "c" then
      files := files.push entry.path
  return files

package «NumLean» where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`backward.do.legacy, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

target libNumLeanNative pkg : Dynlib := do
  let cFiles ← collectCFiles (pkg.dir / "c")
  let objJobs ← cFiles.mapM fun cFile => do
    let srcJob ← inputFile cFile true
    let oFile := (pkg.buildDir / "c" / cFile.fileName.get!).withExtension "o"
    buildO oFile srcJob #["-I", (← getLeanIncludeDir).toString] #["-fPIC"] "cc" getLeanTrace
  buildSharedLib "NumLeanNative" (pkg.sharedLibDir / nameToSharedLib "NumLeanNative")
    objJobs #[] #[] #[] "cc" getLeanTrace

lean_lib NumLean where

lean_lib NumLeanExperimental where

@[default_target]
lean_lib NumLeanAll where

lean_lib NumLean.Data.Scalars.Float32.Float32Array where
  moreLinkLibs := #[libNumLeanNative]
  precompileModules := true

lean_lib NumLean.Data.Scalars.Float64.Float64Array where
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

lean_lib Tests.CCompiler where

lean_lib Tests where
