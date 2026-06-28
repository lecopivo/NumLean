module

public import NumLean.Experimental.Data.DyadicInterval.Dyadic

@[expose] public section

namespace NumLean

inductive ExtDyadic where
  | negInf
  | finite (x : Dyadic)
  | posInf
deriving DecidableEq

namespace ExtDyadic

def le : ExtDyadic → ExtDyadic → Prop
  | .negInf, _ => True
  | .finite _, .negInf => False
  | .finite x, .finite y => x ≤ y
  | .finite _, .posInf => True
  | .posInf, .posInf => True
  | .posInf, _ => False

instance : LE ExtDyadic := ⟨le⟩

instance (x y : ExtDyadic) : Decidable (x ≤ y) := by
  cases x <;> cases y <;> simp [LE.le, le] <;> infer_instance

def min (x y : ExtDyadic) : ExtDyadic :=
  if x ≤ y then x else y

def max (x y : ExtDyadic) : ExtDyadic :=
  if x ≤ y then y else x

def ofLower? : Option Dyadic → ExtDyadic
  | none => .negInf
  | some x => .finite x

def ofUpper? : Option Dyadic → ExtDyadic
  | none => .posInf
  | some x => .finite x

def lowerBounds (e : ExtDyadic) (x : ℝ) : Prop :=
  match e with
  | .negInf => True
  | .finite a => (a : ℝ) ≤ x
  | .posInf => False

def upperBounds (e : ExtDyadic) (x : ℝ) : Prop :=
  match e with
  | .negInf => False
  | .finite a => x ≤ (a : ℝ)
  | .posInf => True

def finiteSignMulNegInf (x : Dyadic) : ExtDyadic :=
  if x ≤ 0 then
    if (0 : Dyadic) ≤ x then .finite 0 else .posInf
  else
    .negInf

def finiteSignMulPosInf (x : Dyadic) : ExtDyadic :=
  if x ≤ 0 then
    if (0 : Dyadic) ≤ x then .finite 0 else .negInf
  else
    .posInf

def mul : ExtDyadic → ExtDyadic → ExtDyadic
  | .negInf, .negInf => .posInf
  | .negInf, .finite x => finiteSignMulNegInf x
  | .negInf, .posInf => .negInf
  | .finite x, .negInf => finiteSignMulNegInf x
  | .finite x, .finite y => .finite (x * y)
  | .finite x, .posInf => finiteSignMulPosInf x
  | .posInf, .negInf => .negInf
  | .posInf, .finite x => finiteSignMulPosInf x
  | .posInf, .posInf => .posInf

instance : Mul ExtDyadic := ⟨mul⟩

def min4 (a b c d : ExtDyadic) : ExtDyadic :=
  min (min a b) (min c d)

def max4 (a b c d : ExtDyadic) : ExtDyadic :=
  max (max a b) (max c d)

def mulLower (a b c d : ExtDyadic) : ExtDyadic :=
  min4 (a * c) (a * d) (b * c) (b * d)

def mulUpper (a b c d : ExtDyadic) : ExtDyadic :=
  max4 (a * c) (a * d) (b * c) (b * d)

def toLower? (prec : Option Int) : ExtDyadic → Option Dyadic
  | .finite x => some (x.roundDown? prec)
  | _ => none

def toUpper? (prec : Option Int) : ExtDyadic → Option Dyadic
  | .finite x => some (x.roundUp? prec)
  | _ => none

end ExtDyadic

end NumLean
