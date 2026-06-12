import Lake
open System Lake DSL

package «NumLean» where
  version := v!"0.1.0"
  keywords := #["math"]
  moreLinkArgs := #["-L.lake/build/lib", "-lNumLeanNative"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

lean_lib NumLean where
  extraDepTargets := #[`NumLeanNative]

lean_exe floatArrayTensorOpsTest where
  root := `Tests.FloatArrayTensorOps
  extraDepTargets := #[`NumLeanNative]
  supportInterpreter := true

extern_lib NumLeanNative pkg := do
  let srcJob ← inputFile (pkg.dir / "c" / "float_array_tensor_ops.c") true
  let lean ← getLeanInstall
  let oJob ← buildO
    (pkg.buildDir / "c" / "float_array_tensor_ops.o")
    srcJob
    #["-I", lean.includeDir.toString]
    #["-fPIC"]
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "NumLeanNative") #[oJob]
