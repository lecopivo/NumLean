import NumLean.Meta.CCompiler.Translate

namespace NumLean.Meta.CCompiler

open Lean Elab Command Lean.Compiler

mutual

partial def compileAltFrom (saved : Ctx) (alt : LCNF.Alt .pure) : CompileM (Val × Array String × Ctx) := do
  modify fun _ => { saved with lines := #[] }
  bindAltParams alt
  let result ← compileCode alt.getCode
  let st ← get
  return (result, st.lines, st)

partial def compileBoolCases (cases : LCNF.Cases .pure) : CompileM Val := do
  let cond ← scalarCode (← getVar cases.discr)
  let some trueAlt := cases.alts.find? altIsTrue
    | unsupportedControl "Bool/Decidable case split is missing a true branch"
  let falseAlt? := cases.alts.find? altIsFalse
  let defaultAlt? := cases.alts.find? fun alt => (altCtorName? alt).isNone
  let some falseAlt := falseAlt?.orElse fun _ => defaultAlt?
    | unsupportedControl "Bool/Decidable case split is missing a false/default branch"
  let saved ← get
  let (thenVal, thenLines, thenCtx) ← compileAltFrom saved trueAlt
  let (elseVal, elseLines, elseCtx) ← compileAltFrom saved falseAlt
  let result ← mergeCaseResult cond thenVal elseVal
  let arrays :=
    saved.arrayOrder.foldl (init := saved.arrays) fun arrays name =>
      match arrays[name]? with
      | none => arrays
      | some a =>
          let mutable := a.mutable
            || (thenCtx.arrays[name]? |>.map (·.mutable) |>.getD false)
            || (elseCtx.arrays[name]? |>.map (·.mutable) |>.getD false)
          arrays.insert name { a with mutable }
  modify fun _ => { saved with arrays }
  let thenText := indentText (String.intercalate "\n" thenLines.toList)
  let elseText := indentText (String.intercalate "\n" elseLines.toList)
  if elseLines.isEmpty then
    pushLine ("if (" ++ cond ++ ") {\n" ++ thenText ++ "\n}")
  else
    pushLine ("if (" ++ cond ++ ") {\n" ++ thenText ++ "\n} else {\n" ++ elseText ++ "\n}")
  return result

partial def compileFunApply (fn : Val) (args : Array Val) : CompileM Val := do
  match fn with
  | .op .pure =>
      match args.back? with
      | some v => return v
      | none => unsupportedFunction "pure application has no value argument"
  | .op .bind =>
      let some (x, k) := getLast2? args | unsupportedFunction "bind expects a value and continuation"
      match k with
      | .funDecl f => applyFun f #[x]
      | _ => unsupportedFunction s!"bind continuation must be a local function, got `{valKind k}`"
  | .op .getElem =>
      let some (arr, idx) := getLast2? args | unsupportedFunction "array get expects array and index"
      match arr with
      | .array root elem => return .scalar s!"{root}[{← scalarCode idx}]" elem
      | _ => unsupportedType s!"array get receiver must be a supported scalar array, got `{valKind arr}`"
  | .op .fold =>
      let some (range, init, body) := getLast3? args | unsupportedFunction "Fold.fold expects range, initial state, and body"
      match range, body with
      | .range lo hi, .funDecl f => compileFold lo hi init f
      | _, _ => unsupportedOperation s!"Fold.fold expects a supported range and local function body, got `{valKind range}` and `{valKind body}`"
  | .op op =>
      compileBinaryOp op args
  | .ofNat ty => compileOfNat ty args
  | .scientific ty => compileScientific ty args
  | .funDecl f => applyFun f args
  | _ => unsupportedFunction s!"LCNF free-variable application target has unsupported value kind `{valKind fn}`"

partial def compileLetValue (value : LCNF.LetValue .pure) : CompileM Val := do
  match value with
  | .erased => return .erased
  | .lit (.nat n) => return .scalar (toString n) .sizeT
  | .lit v => unsupportedValue s!"literal `{v.toExpr}` is not supported; supported literals are natural-number numerals plus Float/Float32 scientific literals through OfScientific"
  | .fvar f args =>
      let fn ← getVar f
      if args.isEmpty then
        return fn
      else
        compileFunApply fn (← lastFVarVals args)
  | .proj typeName idx f =>
      if nameStr typeName == "MProd" then
        match ← getVar f with
        | .tuple fields =>
            match fields[idx]? with
            | some v => return v
            | none => unsupportedOperation s!"MProd projection index {idx} is out of bounds for tuple of arity {fields.size}"
        | v => unsupportedType s!"MProd projection expected a tuple value, got `{valKind v}`"
      else if nameStr typeName == "OfNat" then
        return ← getVar f
      else if nameStr typeName == "OfScientific" then
        return ← getVar f
      else if let some op := opFromProj? typeName idx then
        return .op op
      else
        unsupportedOperation s!"projection `{typeName}.{idx}` is not supported by the C compiler"
  | .const declName _ args =>
      let vals ← lastFVarVals args
      translateConst declName vals

partial def compileLet (decl : LCNF.LetDecl .pure) : CompileM Unit := do
  let v ← compileLetValue decl.value
  let name := binderNameToC decl.binderName
  pushEvent s!"lower let `{decl.binderName}` as `{name}` ({valKind v})"
  match v with
  | .scalar code ty =>
      if name.startsWith "_x" || name.startsWith "__" then
        setVar decl.fvarId v
      else
        declareScalarOrAssign name code ty
        setVar decl.fvarId (.scalar name ty)
  | .array root elem =>
      if name.startsWith "_x" || name.startsWith "__" || name == root then
        setVar decl.fvarId (.array root elem)
      else
        unsupportedOperation s!"array alias `let {name} := {root}` is not supported; mutable arrays must use the standard `let mut xs := xs; xs := xs.set! ...` handoff pattern"
  | .tuple .. | .range .. | .op .. | .ofNat .. | .scientific .. | .bool .. | .funDecl .. | .erased =>
      setVar decl.fvarId v

partial def compileCode (code : LCNF.Code .pure) : CompileM Val := do
  match code with
  | .let decl k =>
      compileLet decl
      compileCode k
  | .fun decl k _ =>
      setVar decl.fvarId (.funDecl decl)
      compileCode k
  | .jp decl k =>
      setVar decl.fvarId (.funDecl decl)
      compileCode k
  | .jmp f args =>
      match ← getVar f with
      | .funDecl decl => applyFun decl (← lastFVarVals args)
      | v => unsupportedControl s!"jump target must be a local join point, got `{valKind v}`"
  | .cases cases =>
      let typeName := nameStr cases.typeName
      if typeName == "Bool" || typeName == "Decidable" then
        compileBoolCases cases
      else
        unsupportedControl s!"case split on `{cases.typeName}` is not supported; only Bool/Decidable conditionals are supported"
  | .unreach .. => unsupportedControl "unreachable code appears in generated LCNF"
  | .return f => getVar f

partial def applyFun (f : LCNF.FunDecl .pure) (args : Array Val) : CompileM Val := do
  let params := f.params
  if args.size > params.size then
    unsupportedFunction s!"local function `{f.binderName}` received too many arguments ({args.size} > {params.size})"
  pushEvent s!"inline local function `{f.binderName}` with {args.size} argument(s)"
  let saved ← get
  for i in [0:args.size] do
    setVar params[i]!.fvarId args[i]!
  let result ← compileCode f.value
  -- Preserve declarations and emitted code, but discard temporary local bindings from the function body.
  let after ← get
  modify fun _ => { after with vars := saved.vars, declared := after.declared, arrays := after.arrays, arrayOrder := after.arrayOrder, scalarParams := after.scalarParams, paramOrder := after.paramOrder, lines := after.lines }
  return result

partial def bindStateParam (stateParam : LCNF.Param .pure) (state : Val) : CompileM Unit :=
  setVar stateParam.fvarId state

partial def compileFold (lo hi : String) (init : Val) (body : LCNF.FunDecl .pure) : CompileM Val := do
  if body.params.size < 3 then
    unsupportedOperation s!"fold body `{body.binderName}` has too few parameters ({body.params.size}); expected index, unused proof/value, and state"
  pushEvent s!"lower fold/range loop from `{lo}` to `{hi}`"
  let iParam := body.params[0]!
  let stateParam := body.params[2]!
  let iName := binderNameToC iParam.binderName
  let saved ← get
  modify fun s => { s with lines := #[] }
  setVar iParam.fvarId (.scalar iName .sizeT)
  bindStateParam stateParam init
  let result ← compileCode body.value
  let bodyState ← get
  let bodyLines := bodyState.lines
  modify fun _ => { bodyState with vars := saved.vars, lines := saved.lines, declared := saved.declared, scalarParams := saved.scalarParams, arrayOrder := saved.arrayOrder, paramOrder := saved.paramOrder }
  let bodyText := String.intercalate "\n" bodyLines.toList
  let indented := bodyText.splitOn "\n" |>.map (fun l => if l.isEmpty then l else "  " ++ l) |>.intersperse "\n" |>.foldl (· ++ ·) ""
  pushLine ("for (size_t " ++ iName ++ " = " ++ lo ++ "; " ++ iName ++ " < " ++ hi ++ "; ++" ++ iName ++ ") {\n" ++ indented ++ "\n}")
  return result

end

def cParams (ctx : Ctx) : Array String := Id.run do
  let mut out := #[]
  for part in ctx.paramOrder do
    match part with
    | .scalar p =>
        out := out.push s!"{p.ty.render} {p.name}"
    | .array name =>
        if let some a := ctx.arrays[name]? then
          let ptr := if a.mutable then s!"{a.elem.render} * restrict {a.name}" else s!"const {a.elem.render} * restrict {a.name}"
          out := out.push ptr
          out := out.push s!"size_t {a.name}_size"
  out

def renderBody (lines : Array String) : String :=
  let body := String.intercalate "\n" lines.toList
  body.splitOn "\n" |>.map (fun l => if l.isEmpty then l else "  " ++ l) |>.intersperse "\n" |>.foldl (· ++ ·) ""

def renderSignature (retTy : CType) (name : String) (params : Array String) : String :=
  match params.toList with
  | [] => retTy.render ++ " " ++ name ++ "()"
  | p :: ps =>
      let rec go : List String → String
        | [] => ""
        | [p] => "\n    " ++ p
        | p :: ps => "\n    " ++ p ++ "," ++ go ps
      retTy.render ++ " " ++ name ++ "(" ++ p ++ (if ps.isEmpty then "" else "," ++ go ps) ++ ")"

def compileDeclFunction (decl : LCNF.Decl .pure) : Except String CFunction :=
  let action : CompileM Val := do
    for p in decl.params do
      addParam p
    match decl.value with
    | .code c => compileCode c
    | .extern .. => unsupportedFunction s!"declaration `{decl.name}` is already extern; only Lean definitions with supported LCNF bodies can be compiled to raw C"
  let (res, ctx) := action.run {}
  match res with
  | .error e => .error e
  | .ok ret =>
      let (retTy, lines) :=
        match ret with
        | .scalar code ty =>
            (ty, ctx.lines.push s!"return {code};")
        | .array .. =>
            (CType.void, ctx.lines)
        | _ =>
            (CType.void, ctx.lines)
      let retTy :=
        retTy
      .ok {
        name := sanitizeName decl.name
        retTy
        params := cParams ctx
        lines
        hasArrayParam := !ctx.arrayOrder.isEmpty
        retVal := ret
        scalarParams := ctx.scalarParams
        arrayParams := ctx.arrayOrder.filterMap fun name => ctx.arrays[name]?
        paramOrder := ctx.paramOrder
        events := ctx.events.push s!"finish `{decl.name}` with C return type `{retTy.render}`"
      }

def renderFunction (fn : CFunction) : String :=
  renderSignature fn.retTy fn.name fn.params ++ " {\n" ++ renderBody fn.lines ++ "\n}"

def traceCompilation (declName : Name) (fn : CFunction) (c : String) : CoreM Unit := do
  trace[NumLean.Meta.CCompiler] "C compilation for `{declName}` produced `{fn.name}`"
  for event in fn.events do
    trace[NumLean.Meta.CCompiler] "{event}"
  trace[NumLean.Meta.CCompiler] "generated kernel C for `{declName}`:\n{c}"

def compileDecl (decl : LCNF.Decl .pure) : Except String String := do
  return renderFunction (← compileDeclFunction decl)

end NumLean.Meta.CCompiler
