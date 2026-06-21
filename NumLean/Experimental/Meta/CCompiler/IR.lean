import Lean

namespace NumLean.Experimental.Meta.CCompiler.IR

/-- Scalar and array types in the standalone CCompiler IR. -/
inductive Ty where
  | unit
  | bool
  | usize
  | int32
  | int64
  | float64
  | float32
  | array (elem : Ty)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Runtime values used by the executable semantics. -/
inductive Value where
  | unit
  | bool (value : Bool)
  | usize (value : Nat)
  | int32 (value : Int)
  | int64 (value : Int)
  | float64 (value : Float)
  | float32 (value : Float32)
  deriving Repr, Inhabited

namespace Value

def ty : Value → Ty
  | .unit => .unit
  | .bool _ => .bool
  | .usize _ => .usize
  | .int32 _ => .int32
  | .int64 _ => .int64
  | .float64 _ => .float64
  | .float32 _ => .float32

end Value

/-- Binary operations supported by the standalone IR. -/
inductive BinOp where
  | add
  | sub
  | mul
  | div
  | mod
  | lt
  | le
  | eq
  | ne
  | and
  | or
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Unary operations supported by the standalone IR. -/
inductive UnOp where
  | neg
  | not
  | sqrt
  | abs
  | cast (toTy : Ty)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure expressions. Variables refer to local scalar bindings, while arrays live in memory. -/
inductive Expr where
  | var (name : String)
  | lit (value : Value)
  | binop (op : BinOp) (lhs rhs : Expr)
  | unop (op : UnOp) (arg : Expr)
  | index (array : String) (idx : Expr)
  | size (array : String)
  deriving Repr, Inhabited

/-- Effectful statements. `forLoop i lo hi body` is a half-open loop over `lo ≤ i < hi`. -/
inductive Stmt where
  | skip
  | letDecl (name : String) (ty : Ty) (rhs : Expr)
  | assign (name : String) (rhs : Expr)
  | store (array : String) (idx val : Expr)
  | seq (stmts : List Stmt)
  | ite (cond : Expr) (thenBranch elseBranch : Stmt)
  | forLoop (idx : String) (lo hi : Expr) (body : Stmt)
  | assert (cond : Expr) (msg : String)
  deriving Repr, Inhabited

structure Param where
  name : String
  ty : Ty
  deriving Repr, Inhabited

structure ArrayParam where
  name : String
  elem : Ty
  mutable : Bool := false
  deriving Repr, Inhabited

/-- Observable function result. -/
inductive Result where
  | unit
  | scalar (expr : Expr)
  | array (name : String)
  | pair (fst snd : Result)
  deriving Repr, Inhabited

/-- Standalone IR function. This is intentionally not connected to the current C compiler. -/
structure Function where
  name : String
  params : List Param
  arrays : List ArrayParam
  body : Stmt
  result : Result
  deriving Repr, Inhabited

end NumLean.Experimental.Meta.CCompiler.IR
