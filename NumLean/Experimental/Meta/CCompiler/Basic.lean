import Lean
import Lean.Compiler.LCNF.ToDecl
import Batteries.Data.FloatArray
import NumLean.Data.Scalars.Float32.Float32Array
import NumLean.Data.ScalarArrays
import NumLean.Meta.ForAll

namespace NumLean.Experimental.Meta.CCompiler

open Lean Elab Command Lean.Compiler

initialize registerTraceClass `NumLean.Experimental.Meta.CCompiler
initialize registerTraceClass `NumLean.Experimental.Meta.CCompiler.extern_c


inductive CType where
  | void
  | sizeT
  | int32
  | int64
  | double
  | float
deriving BEq, Inhabited, Repr

namespace CType

def render : CType → String
  | .void => "void"
  | .sizeT => "size_t"
  | .int32 => "int32_t"
  | .int64 => "int64_t"
  | .double => "double"
  | .float => "float"

end CType

inductive Op where
  | add
  | sub
  | mul
  | div
  | mod
  | lt
  | le
  | eq
  | ne
  | getElem
  | setElem
  | fold
  | pure
  | bind
deriving BEq, Repr

inductive ScalarKind where
  | usize
  | int32
  | int64
  | float
  | float32
deriving BEq, Repr

inductive Val where
  | scalar (code : String) (ty : CType := .sizeT)
  | array (root : String) (elem : CType)
  | tuple (fields : Array Val)
  | range (lo hi : String)
  | op (op : Op)
  | ofNat (ty : CType)
  | scientific (ty : CType)
  | bool (value : Bool)
  | funDecl (decl : LCNF.FunDecl .pure)
  | erased
deriving Inhabited

structure ArrayParam where
  name : String
  elem : CType
  mutable : Bool := false
deriving Inhabited, Repr

structure ScalarParam where
  name : String
  ty : CType
deriving Inhabited, Repr

inductive ParamPart where
  | scalar (p : ScalarParam)
  | array (name : String)
deriving Inhabited, Repr

structure Ctx where
  vars : Std.HashMap FVarId Val := {}
  declared : Std.HashSet String := {}
  arrays : Std.HashMap String ArrayParam := {}
  arrayOrder : Array String := #[]
  scalarParams : Array ScalarParam := #[]
  paramOrder : Array ParamPart := #[]
  lines : Array String := #[]
  events : Array String := #[]
deriving Inhabited

structure CFunction where
  name : String
  retTy : CType
  params : Array String
  lines : Array String
  events : Array String
  hasArrayParam : Bool
  retVal : Val
  scalarParams : Array ScalarParam
  arrayParams : Array ArrayParam
  paramOrder : Array ParamPart
deriving Inhabited

abbrev CompileM := ExceptT String (StateM Ctx)

def fail {α} (msg : String) : CompileM α :=
  throw s!"C compiler error: {msg}"

def unsupportedType {α} (msg : String) : CompileM α :=
  fail s!"unsupported type: {msg}"

def unsupportedFunction {α} (msg : String) : CompileM α :=
  fail s!"unsupported function: {msg}"

def unsupportedOperation {α} (msg : String) : CompileM α :=
  fail s!"unsupported operation: {msg}"

def unsupportedValue {α} (msg : String) : CompileM α :=
  fail s!"unsupported value: {msg}"

def unsupportedControl {α} (msg : String) : CompileM α :=
  fail s!"unsupported control flow: {msg}"

def sanitizeName (n : Name) : String :=
  let s := n.eraseMacroScopes.toString
  s.map fun c => if c.isAlphanum || c == '_' then c else '_'

def binderNameToC (n : Name) : String :=
  sanitizeName n

def pushLine (line : String) : CompileM Unit :=
  modify fun s => { s with lines := s.lines.push line, events := s.events.push s!"emit C: {line}" }

def pushEvent (event : String) : CompileM Unit :=
  modify fun s => { s with events := s.events.push event }

def withLinesSnapshot (x : CompileM α) : CompileM (α × Array String) := do
  let before ← get
  modify fun s => { s with lines := #[] }
  let a ← x
  let after ← get
  modify fun _ => { after with lines := before.lines }
  return (a, after.lines)

def setVar (f : FVarId) (v : Val) : CompileM Unit :=
  modify fun s => { s with vars := s.vars.insert f v }

def getVar (f : FVarId) : CompileM Val := do
  match (← get).vars[f]? with
  | some v => return v
  | none => fail s!"unknown LCNF variable `{f.name}`"

def markMutable (root : String) : CompileM Unit :=
  modify fun s =>
    match s.arrays[root]? with
    | some a => { s with arrays := s.arrays.insert root { a with mutable := true } }
    | none => s

def declareScalarOrAssign (name expr : String) (ty : CType) : CompileM Unit := do
  let s ← get
  if s.declared.contains name then
    if name != expr then
      pushLine s!"{name} = {expr};"
  else
    modify fun s => { s with declared := s.declared.insert name }
    pushLine s!"{ty.render} {name} = {expr};"

def exprName? : Expr → Option Name
  | .const n _ => some n
  | .app f _ => exprName? f
  | .mdata _ e => exprName? e
  | _ => none

def isConstName (e : Expr) (n : Name) : Bool :=
  exprName? e == some n

partial def compileType (e : Expr) : Option (Except CType CType) :=
  let e := e.consumeMData
  if isConstName e ``USize then some (.ok .sizeT)
  else if isConstName e ``Int32 then some (.ok .int32)
  else if isConstName e ``Int64 then some (.ok .int64)
  else if isConstName e ``Float then some (.ok .double)
  else if isConstName e ``Float32 then some (.ok .float)
  else if isConstName e ``FloatArray then some (.error .double)
  else if isConstName e ``Float32Array then some (.error .float)
  else if isConstName e ``Int32Array then some (.error .int32)
  else if isConstName e ``Int64Array then some (.error .int64)
  else if isConstName e ``USizeArray then some (.error .sizeT)
  else
    none

def scalarTyOfType (e : Expr) : CType :=
  match compileType e with
  | some (.ok ty) => ty
  | _ => .sizeT

def scalarKindOfType? (e : Expr) : Option ScalarKind :=
  let e := e.consumeMData
  if isConstName e ``USize then some .usize
  else if isConstName e ``Int32 then some .int32
  else if isConstName e ``Int64 then some .int64
  else if isConstName e ``Float then some .float
  else if isConstName e ``Float32 then some .float32
  else none

def arrayElemOfType? (e : Expr) : Option CType :=
  let e := e.consumeMData
  if isConstName e ``FloatArray then some .double
  else if isConstName e ``Float32Array then some .float
  else if isConstName e ``Int32Array then some .int32
  else if isConstName e ``Int64Array then some .int64
  else if isConstName e ``USizeArray then some .sizeT
  else none

def valKind : Val → String
  | .scalar .. => "scalar"
  | .array .. => "array"
  | .tuple .. => "tuple"
  | .range .. => "range"
  | .op op => s!"op {repr op}"
  | .ofNat .. => "OfNat translator"
  | .scientific .. => "OfScientific translator"
  | .bool .. => "bool"
  | .funDecl .. => "function"
  | .erased => "erased"

def addParam (p : LCNF.Param .pure) : CompileM Unit := do
  let name := binderNameToC p.binderName
  match compileType p.type with
  | some (.ok ty) =>
      pushEvent s!"parameter `{p.binderName}`: scalar `{name}` as {ty.render}"
      modify fun s =>
        { s with
          scalarParams := s.scalarParams.push { name, ty }
          paramOrder := s.paramOrder.push (.scalar { name, ty })
          declared := s.declared.insert name }
      setVar p.fvarId (.scalar name ty)
  | some (.error elem) =>
      pushEvent s!"parameter `{p.binderName}`: scalar array `{name}` elements as {elem.render}"
      modify fun s =>
        { s with
          arrays := s.arrays.insert name { name, elem }
          arrayOrder := s.arrayOrder.push name
          paramOrder := s.paramOrder.push (.array name)
          declared := s.declared.insert name }
      setVar p.fvarId (.array name elem)
  | none => unsupportedType s!"parameter `{p.binderName}` has type `{p.type}`; supported ABI types are USize, Int32, Int64, Float, Float32, FloatArray, Float32Array, Int32Array, Int64Array, and USizeArray; Nat and Int are intentionally rejected at the raw C ABI boundary"

def scalarCode : Val → CompileM String
  | .scalar c _ => return c
  | .array root _ => return root
  | v => unsupportedType s!"expected a scalar expression that can be emitted as C, got `{valKind v}`"

def lastFVarVals (args : Array (LCNF.Arg .pure)) : CompileM (Array Val) := do
  let mut vals := #[]
  for a in args do
    match a with
    | .fvar f => vals := vals.push (← getVar f)
    | .erased | .type .. => pure ()
  return vals

def getLast? (xs : Array α) (n : Nat) : Option (Array α) :=
  if n ≤ xs.size then some (xs.extract (xs.size - n) xs.size) else none

def getLast2? (xs : Array α) : Option (α × α) := do
  let ys ← getLast? xs 2
  let a ← ys[0]?
  let b ← ys[1]?
  return (a, b)

def getLast3? (xs : Array α) : Option (α × α × α) := do
  let ys ← getLast? xs 3
  let a ← ys[0]?
  let b ← ys[1]?
  let c ← ys[2]?
  return (a, b, c)

def nameStr (n : Name) : String := n.eraseMacroScopes.toString

def opFromConstName? (n : Name) : Option Op :=
  match nameStr n with
  | "instHAdd" => some .add
  | "instHSub" => some .sub
  | "instHMul" => some .mul
  | "instHDiv" => some .div
  | "instHMod" => some .mod
  | "Nat.decLt" => some .lt
  | "Nat.decLe" => some .le
  | _ => none

def opFromProj? (typeName : Name) (idx : Nat) : Option Op :=
  match nameStr typeName, idx with
  | "HAdd", 0 => some .add
  | "HSub", 0 => some .sub
  | "HMul", 0 => some .mul
  | "HDiv", 0 => some .div
  | "HMod", 0 => some .mod
  | "LT", 0 => some .lt
  | "LE", 0 => some .le
  | "GetElem?", 2 => some .getElem
  | "NumLean.Fold", 0 => some .fold
  | "Monad", 0 => some .pure
  | "Monad", 1 => some .bind
  | "Applicative", 1 => some .pure
  | "Pure", 0 => some .pure
  | "Bind", 0 => some .bind
  | _, _ => none

def binOpSymbol : Op → Option String
  | .add => some "+"
  | .sub => some "-"
  | .mul => some "*"
  | .div => some "/"
  | .mod => some "%"
  | .lt => some "<"
  | .le => some "<="
  | .eq => some "=="
  | .ne => some "!="
  | _ => none

end NumLean.Experimental.Meta.CCompiler
