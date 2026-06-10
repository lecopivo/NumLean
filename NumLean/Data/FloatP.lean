
namespace NumLean

inductive Float.Precision
  | single | double

/-- `Float[p]` is floating point number with precision `p`.

  - `Float[32]` or `Float[.single]` - 32-bit floating point number
  - `Float[64]` or `Float[.double]` - 64-bit floating point number
  - `Float[p]` - floating point number with variable precision `p : Float.Precision`

Note: `Float[p]` is just a notation for `FloatP p` and `p : Float.Precision` with a special
support for `Float[32]` and `Float[64]`. Arbitrary number like `Float[1234]` is not valid. -/
def FloatP (p : Float.Precision) : Type :=
  match p with
  | .single => Float32
  | .double => Float

@[inherit_doc FloatP]
macro "Float[" p:term "]" : term => do
  if let some n := p.raw.isNatLit? then
    if n == 32 then
      `(FloatP .single)
    else if n == 64 then
      `(FloatP .double)
    else
      Lean.Macro.throwUnsupported
  else
    `(FloatP $p)

open Lean PrettyPrinter in
@[app_unexpander FloatP]
def floatPUnexpander : Unexpander
 | `($_ Float.Precision.single) => `(Float[32])
 | `($_ Float.Precision.double) => `(Float[64])
 | `($_ $p) => `(Float[$p])
 | _ => throw ()

unif_hint (prec : Float.Precision) where
  prec =?= .double
  ⊢ FloatP prec =?= Float

unif_hint (prec : Float.Precision) where
  prec =?= .single
  ⊢ FloatP prec =?= Float32

/-- info: Float[32] : Type -/
#guard_msgs in
#check Float[32]

/-- info: Float[64] : Type -/
#guard_msgs in
#check Float[64]

/-- info: fun p ↦ Float[p] : Float.Precision → Type -/
#guard_msgs in
#check fun p => Float[p]


section Instances

instance {p} : ToString Float[p] :=
  match p with
  | .single => inferInstanceAs (ToString Float32)
  | .double => inferInstanceAs (ToString Float)

instance {p} : LT Float[p] :=
  match p with
  | .single => inferInstanceAs (LT Float32)
  | .double => inferInstanceAs (LT Float)

instance {p} : LE Float[p] :=
  match p with
  | .single => inferInstanceAs (LE Float32)
  | .double => inferInstanceAs (LE Float)

instance {p} : BEq Float[p] :=
  match p with
  | .single => inferInstanceAs (BEq Float32)
  | .double => inferInstanceAs (BEq Float)

-- instance {p} : DecidableEq Float[p] :=
--   match p with
--   | .single => inferInstanceAs (DecidableEq Float32)
--   | .double => inferInstanceAs (DecidableEq Float)

instance {p} : DecidableLT Float[p] :=
  match p with
  | .single => inferInstanceAs (DecidableLT Float32)
  | .double => inferInstanceAs (DecidableLT Float)

instance {p} : DecidableLE Float[p] :=
  match p with
  | .single => inferInstanceAs (DecidableLE Float32)
  | .double => inferInstanceAs (DecidableLE Float)

instance {p} : Zero Float[p] :=
  match p with
  | .single => inferInstanceAs (Zero Float32)
  | .double => inferInstanceAs (Zero Float)

instance {p} : Add Float[p] :=
  match p with
  | .single => inferInstanceAs (Add Float32)
  | .double => inferInstanceAs (Add Float)

instance {p} : Neg Float[p] :=
  match p with
  | .single => inferInstanceAs (Neg Float32)
  | .double => inferInstanceAs (Neg Float)

instance {p} : Sub Float[p] :=
  match p with
  | .single => inferInstanceAs (Sub Float32)
  | .double => inferInstanceAs (Sub Float)

instance {p} : Mul Float[p] :=
  match p with
  | .single => inferInstanceAs (Mul Float32)
  | .double => inferInstanceAs (Mul Float)

instance {p} : Div Float[p] :=
  match p with
  | .single => inferInstanceAs (Div Float32)
  | .double => inferInstanceAs (Div Float)

-- instance {p} : Inv Float[p] :=
--   match p with
--   | .single => inferInstanceAs (Inv Float32)
--   | .double => inferInstanceAs (Inv Float)


end Instances
