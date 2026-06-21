import NumLean.Experimental.Meta.CCompiler.Semantics

set_option linter.unusedSimpArgs false

namespace Tests.CCompilerIRSemantics

open NumLean.Experimental.Meta.CCompiler.IR

@[simp] theorem except_ok_bind {ε α β} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

@[simp] theorem except_ok_map {ε α β} (x : α) (f : α → β) :
    f <$> (Except.ok x : Except ε α) = Except.ok (f x) := rfl

def scalarAddIR : Function :=
  { name := "scalarAdd"
    params := [{ name := "x", ty := .usize }, { name := "y", ty := .usize }]
    arrays := []
    body := .skip
    result := .scalar (.binop .add (.var "x") (.var "y")) }

def scalarAddInput (x y : Nat) : State :=
  { locals := [("x", .usize x), ("y", .usize y)] }

def scalarAddLean (x y : Nat) : Nat :=
  x + y

theorem scalarAddIR_correct (x y : Nat) :
    runFunctionWithFuel 1 scalarAddIR (scalarAddInput x y) =
      .ok (.scalar (.usize (scalarAddLean x y))) := by
  simp [runFunctionWithFuel, scalarAddIR, scalarAddInput, scalarAddLean, execStmtFuel, evalResult, evalExpr,
    State.getLocal, Assoc.get?, evalBinOp, evalNatBinOp, Except.bind, Except.map]

def fillBody : Stmt :=
  .forLoop "i" (.lit (.usize 0)) (.var "n")
    (.store "dst" (.var "i") (.var "x"))

def fillIR : Function :=
  { name := "fill"
    params := [{ name := "n", ty := .usize }, { name := "x", ty := .usize }]
    arrays := [{ name := "dst", elem := .usize, mutable := true }]
    body := fillBody
    result := .array "dst" }

def fillInput (n : Nat) (dst : Array Value) (x : Nat) : State :=
  { locals := [("n", .usize n), ("x", .usize x)]
    arrays := [("dst", { elemTy := .usize, data := dst })] }

def fillLean (n : Nat) (dst : Array Value) (x : Nat) : Except String ArrayValue :=
  (List.range' 0 n).foldlM
    (fun dst i => dst.write i (.usize x))
    ({ elemTy := .usize, data := dst } : ArrayValue)

example :
    fillLean 3 #[.usize 0, .usize 0, .usize 0] 7 =
      .ok { elemTy := .usize, data := #[.usize 7, .usize 7, .usize 7] } := by
  rfl

example :
    runFunctionWithFuel 5 fillIR (fillInput 3 #[.usize 0, .usize 0, .usize 0] 7) =
      .ok (.array { elemTy := .usize, data := #[.usize 7, .usize 7, .usize 7] }) := by
  simp [runFunctionWithFuel, fillIR, fillInput, fillBody, execStmtFuel, execForFuel,
    evalResult, evalExpr, State.getLocal, State.getArray, State.setLocal, State.setArray,
    Assoc.get?, Assoc.set, Value.asUSize, ArrayValue.write, ensureTy, Except.bind,
    Except.map, List.range', Value.ty]

example :
    runFunctionWithFuel 5 fillIR (fillInput 3 #[.usize 0, .usize 0, .usize 0] 7) =
      match fillLean 3 #[.usize 0, .usize 0, .usize 0] 7 with
      | .ok dst => .ok (.array dst)
      | .error err => .error err := by
  simp [runFunctionWithFuel, fillIR, fillInput, fillBody, fillLean, execStmtFuel, execForFuel,
    evalResult, evalExpr, State.getLocal, State.getArray, State.setLocal, State.setArray,
    Assoc.get?, Assoc.set, Value.asUSize, ArrayValue.write, ensureTy, Except.bind,
    Except.map, List.foldlM, List.range', Value.ty]

def copyBody : Stmt :=
  .forLoop "i" (.lit (.usize 0)) (.var "n")
    (.store "dst" (.var "i") (.index "src" (.var "i")))

def copyIR : Function :=
  { name := "copy"
    params := [{ name := "n", ty := .usize }]
    arrays := [
      { name := "src", elem := .usize },
      { name := "dst", elem := .usize, mutable := true }]
    body := copyBody
    result := .array "dst" }

def copyInput (n : Nat) (src dst : Array Value) : State :=
  { locals := [("n", .usize n)]
    arrays := [
      ("src", { elemTy := .usize, data := src }),
      ("dst", { elemTy := .usize, data := dst })] }

def copyLean (n : Nat) (src dst : Array Value) : Except String ArrayValue := do
  let srcArray : ArrayValue := { elemTy := .usize, data := src }
  (List.range' 0 n).foldlM
    (fun dst i => do
      let value ← srcArray.read i
      dst.write i value)
    ({ elemTy := .usize, data := dst } : ArrayValue)

example :
    copyLean 3 #[.usize 4, .usize 5, .usize 6] #[.usize 0, .usize 0, .usize 0] =
      .ok { elemTy := .usize, data := #[.usize 4, .usize 5, .usize 6] } := by
  rfl

example :
    runFunctionWithFuel 5 copyIR
        (copyInput 3 #[.usize 4, .usize 5, .usize 6] #[.usize 0, .usize 0, .usize 0]) =
      match copyLean 3 #[.usize 4, .usize 5, .usize 6] #[.usize 0, .usize 0, .usize 0] with
      | .ok dst => .ok (.array dst)
      | .error err => .error err := by
  simp [runFunctionWithFuel, copyIR, copyInput, copyBody, copyLean, execStmtFuel, execForFuel,
    evalResult, evalExpr, State.getLocal, State.getArray, State.setLocal, State.setArray,
    Assoc.get?, Assoc.set, Value.asUSize, ArrayValue.read, ArrayValue.write, ensureTy,
    Except.bind, Except.map, List.foldlM, List.range', Value.ty]

end Tests.CCompilerIRSemantics
