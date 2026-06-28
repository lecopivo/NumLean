module

public import NumLean.Experimental.Meta.CCompiler.Basic

@[expose] public section

namespace NumLean.Experimental.Meta.CCompiler

open Lean Elab Command Lean.Compiler

inductive ConstAction where
  | mprodMk
  | rangeMk
  | scalarArraySet
  | idRun
  | scalarArraySize
  | unaryC (cName : String) (retTy : CType)
  | identity (retTy : CType)
  | cast (retTy : CType)
  | ofNat (retTy : CType)
  | applyOfNat
  | scientific (retTy : CType)
  | scientificInst (retTy : CType)
  | applyScientific
  | bool (value : Bool)
  | op (op : Op)
  | erased
deriving Inhabited

structure ConstRule where
  name : String
  action : ConstAction

def constTranslationTable : Array ConstRule := #[
  { name := "MProd.mk", action := .mprodMk },
  { name := "Std.Rco.mk", action := .rangeMk },
  { name := "FloatArray.set!", action := .scalarArraySet },
  { name := "NumLean.Float32Array.set!", action := .scalarArraySet },
  { name := "NumLean.Int32Array.set!", action := .scalarArraySet },
  { name := "NumLean.Int64Array.set!", action := .scalarArraySet },
  { name := "NumLean.USizeArray.set!", action := .scalarArraySet },
  { name := "Id.run", action := .idRun },
  { name := "FloatArray.size", action := .scalarArraySize },
  { name := "NumLean.Float32Array.size", action := .scalarArraySize },
  { name := "NumLean.Int32Array.size", action := .scalarArraySize },
  { name := "NumLean.Int64Array.size", action := .scalarArraySize },
  { name := "NumLean.USizeArray.size", action := .scalarArraySize },
  { name := "FloatArray.usize", action := .scalarArraySize },
  { name := "NumLean.Float32Array.usize", action := .scalarArraySize },
  { name := "NumLean.Int32Array.usize", action := .scalarArraySize },
  { name := "NumLean.Int64Array.usize", action := .scalarArraySize },
  { name := "NumLean.USizeArray.usize", action := .scalarArraySize },
  { name := "Float.sqrt", action := .unaryC "sqrt" .double },
  { name := "Float.abs", action := .unaryC "fabs" .double },
  { name := "Float.decLt", action := .op .lt },
  { name := "Float.decLe", action := .op .le },
  { name := "Int32.decLt", action := .op .lt },
  { name := "Int32.decLe", action := .op .le },
  { name := "Int64.decLt", action := .op .lt },
  { name := "Int64.decLe", action := .op .le },
  { name := "USize.decLt", action := .op .lt },
  { name := "USize.decLe", action := .op .le },
  { name := "USize.toNat", action := .identity .sizeT },
  { name := "Nat.toUSize", action := .identity .sizeT },
  { name := "USize.ofNat", action := .identity .sizeT },
  { name := "Nat.toFloat", action := .cast .double },
  { name := "Float.ofNat", action := .cast .double },
  { name := "Nat.toFloat32", action := .cast .float },
  { name := "Float32.ofNat", action := .cast .float },
  { name := "Nat.toInt32", action := .cast .int32 },
  { name := "Int32.ofNat", action := .cast .int32 },
  { name := "Nat.toInt64", action := .cast .int64 },
  { name := "Int64.ofNat", action := .cast .int64 },
  { name := "Int32.toInt64", action := .cast .int64 },
  { name := "Int64.toInt32", action := .cast .int32 },
  { name := "Int32.toFloat", action := .cast .double },
  { name := "Int64.toFloat", action := .cast .double },
  { name := "USize.toFloat", action := .cast .double },
  { name := "Int32.toFloat32", action := .cast .float },
  { name := "Int64.toFloat32", action := .cast .float },
  { name := "USize.toFloat32", action := .cast .float },
  { name := "Float.toFloat32", action := .cast .float },
  { name := "Float32.toFloat", action := .cast .double },
  { name := "instOfNatNat", action := .ofNat .sizeT },
  { name := "instOfNatFloat", action := .ofNat .double },
  { name := "instOfNatFloat32", action := .ofNat .float },
  { name := "Int32.instOfNat", action := .ofNat .int32 },
  { name := "Int64.instOfNat", action := .ofNat .int64 },
  { name := "USize.instOfNat", action := .ofNat .sizeT },
  { name := "OfNat.ofNat", action := .applyOfNat },
  { name := "Float.ofScientific", action := .scientific .double },
  { name := "Float32.ofScientific", action := .scientific .float },
  { name := "instOfScientificFloat", action := .scientificInst .double },
  { name := "instOfScientificFloat32", action := .scientificInst .float },
  { name := "OfScientific.ofScientific", action := .applyScientific },
  { name := "Bool.true", action := .bool true },
  { name := "Bool.false", action := .bool false },
  { name := "Id.instMonad", action := .erased },
  { name := "NumLean.instFoldRcoNative", action := .op .fold },
  { name := "Array.instGetElem?NatLtSize", action := .op .getElem },
  { name := "instAddNat", action := .op .add }
]

def constAction? (declName : Name) : Option ConstAction := do
  let rule ← constTranslationTable.find? fun rule => rule.name == nameStr declName
  return rule.action

def cCast (ty : CType) (code : String) : String :=
  if ty == .sizeT then code else s!"({ty.render})({code})"

def indentText (text : String) : String :=
  text.splitOn "\n" |>.map (fun l => if l.isEmpty then l else "  " ++ l) |>.intersperse "\n" |>.foldl (· ++ ·) ""

def compileOfNat (ty : CType) (vals : Array Val) : CompileM Val := do
  match vals.back? with
  | some v => return .scalar (← scalarCode v) ty
  | none => return .ofNat ty

def compileApplyOfNat (vals : Array Val) : CompileM Val := do
  let some lit := vals.back? | unsupportedValue "OfNat.ofNat expects a numeric literal argument"
  let some inst := vals.find? (fun v => match v with | .ofNat .. => true | _ => false)
    | unsupportedType "OfNat.ofNat instance is not supported by the C compiler; supported raw numeric types are USize, Float, Float32, Int32, and Int64; Nat and Int are intentionally rejected at the ABI boundary"
  match inst with
  | .ofNat ty => return .scalar (← scalarCode lit) ty
  | _ => unreachable!

def scientificLiteral (ty : CType) (mantissa : String) (exponentSign : Bool) (exponent : String) : String :=
  let suffix := if ty == .float then "f" else ""
  if exponentSign then
    s!"{mantissa}e-{exponent}{suffix}"
  else
    s!"{mantissa}e{exponent}{suffix}"

def compileScientific (ty : CType) (vals : Array Val) : CompileM Val := do
  let some (mantissa, exponentSign, exponent) := getLast3? vals
    | unsupportedValue "OfScientific.ofScientific expects mantissa, exponent sign, and exponent"
  let sign ←
    match exponentSign with
    | .bool b => pure b
    | _ => unsupportedValue s!"OfScientific.ofScientific expects a boolean exponent sign, got `{valKind exponentSign}`"
  return .scalar (scientificLiteral ty (← scalarCode mantissa) sign (← scalarCode exponent)) ty

def compileApplyScientific (vals : Array Val) : CompileM Val := do
  let some inst := vals.find? (fun v => match v with | .scientific .. => true | _ => false)
    | unsupportedType "OfScientific.ofScientific instance is not supported by the C compiler; supported scientific literal types are Float and Float32"
  match inst with
  | .scientific ty => compileScientific ty vals
  | _ => unreachable!

def compileBinaryOp (op : Op) (vals : Array Val) : CompileM Val := do
  let some sym := binOpSymbol op | unsupportedOperation s!"operator `{repr op}` is not lowered to C"
  let some (a, b) := getLast2? vals | unsupportedOperation s!"binary operator `{repr op}` expects two scalar arguments, got {vals.size} argument(s)"
  let ty := match a with | .scalar _ ty => ty | _ => .sizeT
  pushEvent s!"lower operation `{repr op}` to `{sym}`"
  return .scalar s!"({← scalarCode a} {sym} {← scalarCode b})" ty

def compileConstAction (declName : Name) (action : ConstAction) (vals : Array Val) : CompileM Val := do
  match action with
  | .mprodMk =>
      let some fields := getLast? vals 2 | unsupportedOperation "MProd.mk expects exactly two values"
      return .tuple fields
  | .rangeMk =>
      let some (lo, hi) := getLast2? vals | unsupportedOperation "Std.Rco.mk expects lower and upper bounds"
      return .range (← scalarCode lo) (← scalarCode hi)
  | .scalarArraySet =>
      let some (arr, idx, val) := getLast3? vals | unsupportedOperation s!"{nameStr declName} expects array, index, and value"
      match arr with
      | .array root elem =>
          markMutable root
          pushLine s!"{root}[{← scalarCode idx}] = {← scalarCode val};"
          return .array root elem
      | _ => unsupportedType s!"{nameStr declName} receiver must be a supported scalar array, got `{valKind arr}`"
  | .idRun =>
      match vals.back? with
      | some v => return v
      | none => unsupportedFunction "Id.run expects an argument"
  | .scalarArraySize =>
      match vals.back? with
      | some (.array root _) => return .scalar s!"{root}_size" .sizeT
      | some v => unsupportedType s!"{nameStr declName} expects a supported scalar array, got `{valKind v}`"
      | none => unsupportedFunction s!"{nameStr declName} expects an array argument"
  | .unaryC cName retTy =>
      match vals.back? with
      | some x => return .scalar s!"{cName}({← scalarCode x})" retTy
      | none => unsupportedFunction s!"{nameStr declName} expects one scalar argument"
  | .identity retTy =>
      match vals.back? with
      | some x => return .scalar (← scalarCode x) retTy
      | none => unsupportedFunction s!"{nameStr declName} expects one scalar argument"
  | .cast retTy =>
      match vals.back? with
      | some x => return .scalar (cCast retTy (← scalarCode x)) retTy
      | none => unsupportedFunction s!"{nameStr declName} expects one scalar argument"
  | .ofNat retTy => compileOfNat retTy vals
  | .applyOfNat => compileApplyOfNat vals
  | .scientific retTy => compileScientific retTy vals
  | .scientificInst retTy => return .scientific retTy
  | .applyScientific => compileApplyScientific vals
  | .bool value => return .bool value
  | .op op =>
      if !vals.isEmpty && (binOpSymbol op).isSome then
        compileBinaryOp op vals
      else do
        return .op op
  | .erased => return .erased

def translateConst (declName : Name) (vals : Array Val) : CompileM Val := do
  if let some action := constAction? declName then
    pushEvent s!"translate supported function `{nameStr declName}`"
    compileConstAction declName action vals
  else if let some op := opFromConstName? declName then
    pushEvent s!"translate supported operation dictionary `{nameStr declName}`"
    return .op op
  else
    -- Most instance dictionaries are only used through projections; keep them erased until projected.
    pushEvent s!"erase unsupported-or-runtime-only constant `{nameStr declName}` while compiling; this is allowed only if it is never called directly"
    return .erased

def altCtorName? : LCNF.Alt .pure → Option Name
  | .alt ctorName .. => some ctorName
  | .default .. => none

def altIsTrue (alt : LCNF.Alt .pure) : Bool :=
  match altCtorName? alt with
  | some n =>
      let s := nameStr n
      s == "Bool.true" || s == "Decidable.isTrue" || s == "isTrue"
  | none => false

def altIsFalse (alt : LCNF.Alt .pure) : Bool :=
  match altCtorName? alt with
  | some n =>
      let s := nameStr n
      s == "Bool.false" || s == "Decidable.isFalse" || s == "isFalse"
  | none => false

def bindAltParams (alt : LCNF.Alt .pure) : CompileM Unit := do
  for p in alt.getParams do
    setVar p.fvarId .erased

partial def mergeCaseResult (cond : String) (thenVal elseVal : Val) : CompileM Val := do
  match thenVal, elseVal with
  | .scalar t ty, .scalar e _ =>
      if t == e then
        return thenVal
      else
        return .scalar s!"({cond} ? {t} : {e})" ty
  | .tuple ts, .tuple es =>
      if ts.size != es.size then
        unsupportedControl s!"case branches return tuples with different arity ({ts.size} vs {es.size})"
      let mut fields := #[]
      for i in [0:ts.size] do
        fields := fields.push (← mergeCaseResult cond ts[i]! es[i]!)
      return .tuple fields
  | .array r elem, .array r' _ =>
      if r == r' then return .array r elem else unsupportedControl s!"case branches return different arrays (`{r}` vs `{r'}`); array joins must preserve one array root"
  | .erased, .erased => return .erased
  | _, _ => unsupportedControl s!"case branches return incompatible values `{valKind thenVal}` and `{valKind elseVal}`"

end NumLean.Experimental.Meta.CCompiler
