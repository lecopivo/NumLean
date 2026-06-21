import NumLean.Experimental.Meta.CCompiler.IR

namespace NumLean.Experimental.Meta.CCompiler.IR

structure ArrayValue where
  elemTy : Ty
  data : Array Value
  deriving Repr, Inhabited

structure State where
  locals : List (String × Value) := []
  arrays : List (String × ArrayValue) := []
  deriving Repr, Inhabited

inductive Output where
  | unit
  | scalar (value : Value)
  | array (value : ArrayValue)
  | pair (fst snd : Output)
  deriving Repr, Inhabited

namespace Assoc

def get? [DecidableEq α] (key : α) : List (α × β) → Option β
  | [] => none
  | (key', value) :: rest => if key = key' then some value else get? key rest

def set [DecidableEq α] (key : α) (value : β) : List (α × β) → List (α × β)
  | [] => [(key, value)]
  | (key', value') :: rest =>
      if key = key' then (key, value) :: rest else (key', value') :: set key value rest

@[simp] theorem get?_set_same [DecidableEq α] (key : α) (value : β) (xs : List (α × β)) :
    get? key (set key value xs) = some value := by
  induction xs with
  | nil => simp [get?, set]
  | cons head rest ih =>
      rcases head with ⟨key', value'⟩
      by_cases h : key = key'
      · simp [get?, set, h]
      · simp [get?, set, h, ih]

@[simp] theorem get?_set_ne [DecidableEq α] {key other : α} (h : key ≠ other) (value : β)
    (xs : List (α × β)) :
    get? key (set other value xs) = get? key xs := by
  induction xs with
  | nil => simp [get?, set, h]
  | cons head rest ih =>
      rcases head with ⟨key', value'⟩
      by_cases hOther : other = key'
      · have hKey : key ≠ key' := by
          intro hKey
          exact h (hKey.trans hOther.symm)
        simp [get?, set, hOther, hKey]
      · by_cases hKey : key = key'
        · simp [get?, set, hOther, hKey]
        · simp [get?, set, hOther, hKey, ih]

end Assoc

def State.getLocal (s : State) (name : String) : Except String Value :=
  match Assoc.get? name s.locals with
  | some value => .ok value
  | none => .error s!"unknown local `{name}`"

def State.setLocal (s : State) (name : String) (value : Value) : State :=
  { s with locals := Assoc.set name value s.locals }

def State.getArray (s : State) (name : String) : Except String ArrayValue :=
  match Assoc.get? name s.arrays with
  | some value => .ok value
  | none => .error s!"unknown array `{name}`"

def State.setArray (s : State) (name : String) (value : ArrayValue) : State :=
  { s with arrays := Assoc.set name value s.arrays }

def Value.asBool : Value → Except String Bool
  | .bool value => .ok value
  | value => .error s!"expected Bool, got `{repr value.ty}`"

def Value.asUSize : Value → Except String Nat
  | .usize value => .ok value
  | value => .error s!"expected USize, got `{repr value.ty}`"

def ensureTy (expected : Ty) (value : Value) : Except String Unit :=
  if value.ty = expected then .ok () else .error s!"expected `{repr expected}`, got `{repr value.ty}`"

def ArrayValue.read (array : ArrayValue) (idx : Nat) : Except String Value := do
  let some value := array.data[idx]?
    | .error s!"array index {idx} is out of bounds for size {array.data.size}"
  ensureTy array.elemTy value
  return value

def ArrayValue.write (array : ArrayValue) (idx : Nat) (value : Value) : Except String ArrayValue := do
  let some _ := array.data[idx]?
    | .error s!"array index {idx} is out of bounds for size {array.data.size}"
  ensureTy array.elemTy value
  return { array with data := array.data.set! idx value }

def evalNatBinOp (op : BinOp) (lhs rhs : Nat) : Except String Value :=
  match op with
  | .add => .ok (.usize (lhs + rhs))
  | .sub => .ok (.usize (lhs - rhs))
  | .mul => .ok (.usize (lhs * rhs))
  | .div => if rhs = 0 then .error "division by zero" else .ok (.usize (lhs / rhs))
  | .mod => if rhs = 0 then .error "modulo by zero" else .ok (.usize (lhs % rhs))
  | .lt => .ok (.bool (lhs < rhs))
  | .le => .ok (.bool (lhs ≤ rhs))
  | .eq => .ok (.bool (lhs = rhs))
  | .ne => .ok (.bool (lhs != rhs))
  | _ => .error s!"operation `{repr op}` is not supported for USize"

def evalIntBinOp (ty : Ty) (op : BinOp) (lhs rhs : Int) : Except String Value :=
  let scalar value := if ty = .int32 then Value.int32 value else Value.int64 value
  match op with
  | .add => .ok (scalar (lhs + rhs))
  | .sub => .ok (scalar (lhs - rhs))
  | .mul => .ok (scalar (lhs * rhs))
  | .div => if rhs = 0 then .error "division by zero" else .ok (scalar (lhs / rhs))
  | .mod => if rhs = 0 then .error "modulo by zero" else .ok (scalar (lhs % rhs))
  | .lt => .ok (.bool (lhs < rhs))
  | .le => .ok (.bool (lhs ≤ rhs))
  | .eq => .ok (.bool (lhs = rhs))
  | .ne => .ok (.bool (lhs != rhs))
  | _ => .error s!"operation `{repr op}` is not supported for integers"

def evalBoolBinOp (op : BinOp) (lhs rhs : Bool) : Except String Value :=
  match op with
  | .and => .ok (.bool (lhs && rhs))
  | .or => .ok (.bool (lhs || rhs))
  | .eq => .ok (.bool (lhs = rhs))
  | .ne => .ok (.bool (lhs != rhs))
  | _ => .error s!"operation `{repr op}` is not supported for Bool"

def evalBinOp (op : BinOp) (lhs rhs : Value) : Except String Value :=
  match lhs, rhs with
  | .usize lhs, .usize rhs => evalNatBinOp op lhs rhs
  | .int32 lhs, .int32 rhs => evalIntBinOp .int32 op lhs rhs
  | .int64 lhs, .int64 rhs => evalIntBinOp .int64 op lhs rhs
  | .bool lhs, .bool rhs => evalBoolBinOp op lhs rhs
  | _, _ => .error s!"type mismatch in binary operation `{repr op}`"

def castValue (ty : Ty) : Value → Except String Value
  | .usize value =>
      match ty with
      | .usize => .ok (.usize value)
      | .int32 => .ok (.int32 value)
      | .int64 => .ok (.int64 value)
      | _ => .error s!"unsupported cast from USize to `{repr ty}`"
  | .int32 value =>
      match ty with
      | .int32 => .ok (.int32 value)
      | .int64 => .ok (.int64 value)
      | .usize => .ok (.usize value.toNat)
      | _ => .error s!"unsupported cast from Int32 to `{repr ty}`"
  | .int64 value =>
      match ty with
      | .int64 => .ok (.int64 value)
      | .int32 => .ok (.int32 value)
      | .usize => .ok (.usize value.toNat)
      | _ => .error s!"unsupported cast from Int64 to `{repr ty}`"
  | value =>
      if value.ty = ty then .ok value else .error s!"unsupported cast from `{repr value.ty}` to `{repr ty}`"

def evalUnOp (op : UnOp) (arg : Value) : Except String Value :=
  match op, arg with
  | .not, .bool value => .ok (.bool (!value))
  | .neg, .int32 value => .ok (.int32 (-value))
  | .neg, .int64 value => .ok (.int64 (-value))
  | .abs, .int32 value => .ok (.int32 (Int.natAbs value))
  | .abs, .int64 value => .ok (.int64 (Int.natAbs value))
  | .cast ty, value => castValue ty value
  | _, _ => .error s!"unsupported unary operation `{repr op}` on `{repr arg.ty}`"

def evalExpr (expr : Expr) (state : State) : Except String Value := do
  match expr with
  | .var name => state.getLocal name
  | .lit value => return value
  | .binop op lhs rhs => evalBinOp op (← evalExpr lhs state) (← evalExpr rhs state)
  | .unop op arg => evalUnOp op (← evalExpr arg state)
  | .index array idx =>
      let idx ← (← evalExpr idx state).asUSize
      (← state.getArray array).read idx
  | .size array =>
      return .usize (← state.getArray array).data.size

mutual

def execStmtFuel : Nat → Stmt → State → Except String State
  | 0, _, _ => .error "out of fuel"
  | fuel + 1, stmt, state => do
      match stmt with
      | .skip => return state
      | .letDecl name ty rhs =>
          let value ← evalExpr rhs state
          ensureTy ty value
          return state.setLocal name value
      | .assign name rhs =>
          let value ← evalExpr rhs state
          return state.setLocal name value
      | .store array idx val =>
          let idx ← (← evalExpr idx state).asUSize
          let value ← evalExpr val state
          let arrayValue ← (← state.getArray array).write idx value
          return state.setArray array arrayValue
      | .seq stmts => execStmtsFuel fuel stmts state
      | .ite cond thenBranch elseBranch =>
          if ← (← evalExpr cond state).asBool then
            execStmtFuel fuel thenBranch state
          else
            execStmtFuel fuel elseBranch state
      | .forLoop idx lo hi body =>
          let lo ← (← evalExpr lo state).asUSize
          let hi ← (← evalExpr hi state).asUSize
          execForFuel fuel idx body (List.range' lo (hi - lo)) state
      | .assert cond msg =>
          if ← (← evalExpr cond state).asBool then return state else .error msg

def execStmtsFuel : Nat → List Stmt → State → Except String State
  | _, [], state => .ok state
  | fuel, stmt :: stmts, state => do
      let state ← execStmtFuel fuel stmt state
      execStmtsFuel fuel stmts state

def execForFuel : Nat → String → Stmt → List Nat → State → Except String State
  | _, _, _, [], state => .ok state
  | 0, _, _, _ :: _, _ => .error "out of fuel"
  | fuel + 1, idx, body, i :: is, state => do
      let state ← execStmtFuel fuel body (state.setLocal idx (.usize i))
      execForFuel fuel idx body is state

end

def execStmt (stmt : Stmt) (state : State) : Except String State :=
  execStmtFuel 10000 stmt state

def evalResult (result : Result) (state : State) : Except String Output := do
  match result with
  | .unit => return .unit
  | .scalar expr => return .scalar (← evalExpr expr state)
  | .array name => return .array (← state.getArray name)
  | .pair fst snd => return .pair (← evalResult fst state) (← evalResult snd state)

def runFunction (fn : Function) (state : State) : Except String Output := do
  evalResult fn.result (← execStmt fn.body state)

def runFunctionWithFuel (fuel : Nat) (fn : Function) (state : State) : Except String Output := do
  evalResult fn.result (← execStmtFuel fuel fn.body state)

end NumLean.Experimental.Meta.CCompiler.IR
