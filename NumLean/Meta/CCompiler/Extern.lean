import NumLean.Meta.CCompiler.Compile

namespace NumLean.Meta.CCompiler

open Lean Elab Command Lean.Compiler

def setFunctionName (fn : CFunction) (name : String) : CFunction :=
  { fn with name }

def pathStemName (path : String) : String :=
  let noExt :=
    if path.endsWith ".c" then
      String.ofList (path.toList.take (path.length - 2))
    else
      path
  noExt.map fun c => if c.isAlphanum then c else '_'

def ffiNameForPath (path : String) : String :=
  "numlean_" ++ pathStemName path

def validateExternInPath (path : String) : Except String Unit := do
  if path.startsWith "/" || (path.splitOn "/" |>.any (· == "..")) then
    throw "extern_c path must be relative to `c/` and must not contain `..`"
  if !path.endsWith ".c" then
    throw "extern_c path must end in `.c`"

partial def dropForallResult (n : Nat) (e : Expr) : Expr :=
  match n, e.consumeMData with
  | 0, e => e
  | n + 1, .forallE _ _ body _ => dropForallResult n body
  | _, e => e

def scalarKindOfRetTy (ty : CType) : Option ScalarKind :=
  match ty with
  | .sizeT => some .usize
  | .int32 => some .int32
  | .int64 => some .int64
  | .double => some .float
  | .float => some .float32
  | _ => none

def scalarAbiParamType : ScalarKind → String
  | .usize => "size_t"
  | .int32 => "uint32_t"
  | .int64 => "uint64_t"
  | .float => "double"
  | .float32 => "float"

def scalarAbiReturnType : ScalarKind → String
  | .usize => "size_t"
  | .int32 => "uint32_t"
  | .int64 => "uint64_t"
  | .float => "double"
  | .float32 => "float"

def scalarKindRawCast (k : ScalarKind) (name : String) : String :=
  match k with
  | .usize | .float | .float32 => name
  | .int32 => s!"(int32_t){name}"
  | .int64 => s!"(int64_t){name}"

def scalarReturnExpr (k : ScalarKind) (name : String) : String :=
  match k with
  | .usize | .float | .float32 => name
  | .int32 => s!"(uint32_t){name}"
  | .int64 => s!"(uint64_t){name}"

def arrayPtrExpr (a : ArrayParam) : String :=
  match a.elem with
  | .double => s!"lean_float_array_cptr({a.name})"
  | .float => s!"(float*)lean_sarray_cptr({a.name})"
  | .int32 => s!"(int32_t*)lean_sarray_cptr({a.name})"
  | .int64 => s!"(int64_t*)lean_sarray_cptr({a.name})"
  | .sizeT => s!"(size_t*)lean_sarray_cptr({a.name})"
  | _ => a.name

def arraySizeExpr (a : ArrayParam) : String :=
  match a.elem with
  | .double => s!"lean_sarray_size({a.name})"
  | .float => s!"lean_sarray_size({a.name}) / sizeof(float)"
  | .int32 => s!"lean_sarray_size({a.name}) / sizeof(int32_t)"
  | .int64 => s!"lean_sarray_size({a.name}) / sizeof(int64_t)"
  | .sizeT => s!"lean_sarray_size({a.name}) / sizeof(size_t)"
  | _ => s!"lean_sarray_size({a.name})"

def arrayCopyFn? : CType → Option String
  | .double => some "lean_copy_float_array"
  | .float => some "lean_copy_float32_array"
  | .int32 => some "lean_copy_int32_array"
  | .int64 => some "lean_copy_int64_array"
  | .sizeT => some "lean_copy_usize_array"
  | _ => none

def ensureExclusiveArrayLines (a : ArrayParam) : Except String (Array String) := do
  if !a.mutable then
    return #[]
  let some copyFn := arrayCopyFn? a.elem
    | throw s!"extern_c error: unsupported mutable array element type `{a.elem.render}` for parameter `{a.name}`; cannot generate a Lean ownership-safe copy before exposing a mutable pointer"
  return #[
    "if (!lean_is_exclusive(" ++ a.name ++ ")) {",
    "  " ++ a.name ++ " = " ++ copyFn ++ "(" ++ a.name ++ ");",
    "}"
  ]

def returnedArrayRoots : Val → Std.HashSet String
  | .array root _ => ({} : Std.HashSet String).insert root
  | .tuple fields =>
      fields.foldl (init := {}) fun acc v =>
        (returnedArrayRoots v).toList.foldl (init := acc) fun acc root => acc.insert root
  | _ => {}

partial def wrapperReturnExpr (v : Val) : Except String (String × Array String) :=
  match v with
  | .array root _ => return (root, #[])
  | .tuple fields =>
      if fields.size != 2 then
        throw s!"extern_c error: unsupported return type tuple arity {fields.size}; only scalar returns, scalar-array returns, and pairs of scalar arrays are supported"
      else do
        let aResult ← wrapperReturnExpr fields[0]!
        let bResult ← wrapperReturnExpr fields[1]!
        let a := aResult.1
        let aLines := aResult.2
        let b := bResult.1
        let bLines := bResult.2
        let lines := aLines ++ bLines ++ #[
          "lean_object* _ret = lean_alloc_ctor(0, 2, 0);",
          s!"lean_ctor_set(_ret, 0, {a});",
          s!"lean_ctor_set(_ret, 1, {b});"
        ]
        return ("_ret", lines)
  | _ => throw s!"extern_c error: unsupported return shape `{valKind v}`; expected scalar, scalar array, or pair of scalar arrays"

def renderWrapperSignature (retTy name : String) (params : Array String) : String :=
  match params.toList with
  | [] => "LEAN_EXPORT " ++ retTy ++ " " ++ name ++ "()"
  | p :: ps =>
      let rec go : List String → String
        | [] => ""
        | [p] => "\n    " ++ p
        | p :: ps => "\n    " ++ p ++ "," ++ go ps
      "LEAN_EXPORT " ++ retTy ++ " " ++ name ++ "(" ++ p ++ (if ps.isEmpty then "" else "," ++ go ps) ++ ")"

def wrapperFor (decl : LCNF.Decl .pure) (fn : CFunction) (ffiName : String) : Except String String := do
  let mut wrapperParams := #[]
  let mut kernelArgs := #[]
  let mut preLines := #[]
  let mut cleanupLines := #[]
  let returned := returnedArrayRoots fn.retVal
  for p in decl.params do
    let name := binderNameToC p.binderName
    if let some k := scalarKindOfType? p.type then
      wrapperParams := wrapperParams.push s!"{scalarAbiParamType k} {name}"
      kernelArgs := kernelArgs.push (scalarKindRawCast k name)
    else if let some elem := arrayElemOfType? p.type then
      wrapperParams := wrapperParams.push s!"lean_object* {name}"
      let a : ArrayParam := { name, elem, mutable := fn.arrayParams.any fun a => a.name == name && a.mutable }
      preLines := preLines ++ (← ensureExclusiveArrayLines a)
      kernelArgs := kernelArgs.push (arrayPtrExpr a)
      kernelArgs := kernelArgs.push (arraySizeExpr a)
      if !returned.contains name then
        cleanupLines := cleanupLines.push s!"lean_dec_ref({name});"
    else
      throw s!"extern_c error: unsupported parameter type for `{p.binderName}`: `{p.type}`; supported extern_c ABI types are USize, Int32, Int64, Float, Float32, FloatArray, Float32Array, Int32Array, Int64Array, and USizeArray; Nat and Int are intentionally rejected at the raw C ABI boundary"
  let call := fn.name ++ "(" ++ String.intercalate ", " kernelArgs.toList ++ ")"
  let resultType := dropForallResult decl.params.size decl.type
  let resultKind? := (scalarKindOfType? resultType).orElse fun _ => scalarKindOfRetTy fn.retTy
  let (retTy, callLines, retExpr) ←
    match fn.retVal with
    | .scalar .. =>
        let some k := resultKind? | throw s!"extern_c error: unsupported scalar return type `{resultType}`; supported scalar returns are USize, Int32, Int64, Float, and Float32; Nat and Int are intentionally rejected at the raw C ABI boundary"
        let rawRetTy := fn.retTy.render
        pure (scalarAbiReturnType k, preLines.push s!"{rawRetTy} _ret = {call};", scalarReturnExpr k "_ret")
    | .array .. | .tuple .. =>
        let (retExpr, retLines) ← wrapperReturnExpr fn.retVal
        pure ("lean_object*", preLines.push (call ++ ";") ++ retLines, retExpr)
    | _ => throw s!"extern_c error: unsupported return shape `{valKind fn.retVal}`; expected scalar, scalar array, or pair of scalar arrays"
  let bodyLines := callLines ++ cleanupLines ++ #[s!"return {retExpr};"]
  return renderWrapperSignature retTy ffiName wrapperParams ++ " {\n" ++ renderBody bodyLines ++ "\n}"

def fileHeader : String :=
  "#include <lean/lean.h>\n#include <stddef.h>\n#include <stdint.h>\n#include <math.h>\n\n" ++
  "LEAN_EXPORT lean_obj_res lean_copy_float32_array(lean_obj_arg a);\n" ++
  "LEAN_EXPORT lean_obj_res lean_copy_int32_array(lean_obj_arg a);\n" ++
  "LEAN_EXPORT lean_obj_res lean_copy_int64_array(lean_obj_arg a);\n" ++
  "LEAN_EXPORT lean_obj_res lean_copy_usize_array(lean_obj_arg a);\n\n"

def writeExternInFile (relPath : String) (content : String) : CoreM System.FilePath := do
  let cwd ← IO.currentDir
  let path := cwd / "c" / System.FilePath.mk relPath
  let some parent := path.parent | throwError "invalid extern_c path `{relPath}`"
  IO.FS.createDirAll parent
  IO.FS.writeFile path content
  return path

syntax (name := Lean.Parser.Attr.extern_c) "extern_c " str : attr

initialize
  registerBuiltinAttribute {
    name := .str .anonymous "extern_c"
    descr := "compile a supported Lean declaration to raw C in c/<path> and attach a C extern wrapper"
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun declName stx kind => do
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `extern_c kind
      let some relPath := stx[1].isStrLit? | throwErrorAt stx "extern_c expects a string literal path"
      match validateExternInPath relPath with
      | .error e => throwError e
      | .ok _ => pure ()
      let ffiName := ffiNameForPath relPath
      let decl ← LCNF.CompilerM.run (LCNF.toDecl declName)
      let fn ←
        match compileDeclFunction decl with
        | .ok fn => pure (setFunctionName fn (ffiName ++ "_kernel"))
        | .error e => throwError e
      let kernelC := renderFunction fn
      traceCompilation declName fn kernelC
      let wrapper ←
        match wrapperFor decl fn ffiName with
        | .ok wrapper => pure wrapper
        | .error e => throwError e
      let c := fileHeader ++ kernelC ++ "\n\n" ++ wrapper ++ "\n"
      trace[NumLean.Meta.CCompiler.extern_c] "generated extern_c C for `{declName}` at `c/{relPath}`:\n{c}"
      let path ← writeExternInFile relPath c
      let data : ExternAttrData := { entries := [ExternEntry.standard `all ffiName] }
      match ParametricAttribute.setParam externAttr (← getEnv) declName data with
      | .ok env => setEnv env
      | .error e => throwError e
    erase := fun _ => throwError "cannot erase extern_c"
  }

end NumLean.Meta.CCompiler
