import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import NumLean.Algebra.Instances
import NumLean.Algebra.Ops
import NumLean.Experimental.Interfaces.Interval

namespace NumLean

/-- Dyadic intervals `[lo * 2^exp, hi * 2^exp]` over `ℝ`.

`none` lower/upper endpoints represent `-∞`/`+∞`, respectively.

The optional `bits` parameter bounds the number of binary digits kept in finite
endpoint integers `lo` and `hi`. It is part of the interval representation type,
not part of the mathematical interval semantics.

`bits = none` means unlimited endpoint precision. `bits = some n` means operations
may conservatively round endpoints and bump `exp` to keep endpoint integers within
roughly `n` bits. -/
structure DyadicInterval (bits : Option Nat := none) where
  lo : Option Int
  hi : Option Int
  exp : Int
deriving Repr, DecidableEq

namespace DyadicInterval

def top {bits : Option Nat} : DyadicInterval bits := ⟨none, none, 0⟩

instance {bits : Option Nat} : Top (DyadicInterval bits) := ⟨top⟩

def addEndpoint : Option Int → Option Int → Option Int
  | some x, some y => some (x + y)
  | _, _ => none

def floorHalf (x : Int) : Int := x / 2

def ceilHalf (x : Int) : Int := -((-x) / 2)

def roundLowerEndpoint : Option Int → Option Int
  | some x => some (floorHalf x)
  | none => none

def roundUpperEndpoint : Option Int → Option Int
  | some x => some (ceilHalf x)
  | none => none

def endpointTooLarge (bits : Nat) : Option Int → Bool
  | some x => decide ((2 ^ bits) ≤ x.natAbs)
  | none => false

def exceedsPrecision {bits? : Option Nat} (bits : Nat) (i : DyadicInterval bits?) : Bool :=
  endpointTooLarge bits i.lo || endpointTooLarge bits i.hi

/-- Conservatively drop one binary digit from finite endpoints and bump the exponent.

For lower endpoints this rounds down, for upper endpoints this rounds up. -/
def bumpExponent {bits : Option Nat} (i : DyadicInterval bits) : DyadicInterval bits :=
  { lo := roundLowerEndpoint i.lo
    hi := roundUpperEndpoint i.hi
    exp := i.exp + 1 }

def maxEndpointAbs {bits : Option Nat} (i : DyadicInterval bits) : Nat :=
  max (i.lo.map Int.natAbs |>.getD 0) (i.hi.map Int.natAbs |>.getD 0)

/-- Trim endpoints by repeatedly bumping the exponent until the finite endpoint
integers fit the requested precision, or until the fuel is exhausted.

The fuel is chosen from the current endpoint size by `normalize`. The `bits = 0`
case is intentionally left unchanged because “zero digits” is not a useful
computational representation. -/
def normalizeWithFuel {bits : Option Nat} : Nat → DyadicInterval bits → DyadicInterval bits
  | 0, i => i
  | fuel + 1, i =>
    match bits with
    | none => i
    | some 0 => i
    | some n =>
      if exceedsPrecision n i then
        normalizeWithFuel fuel (bumpExponent i)
      else
        i

def normalize {bits : Option Nat} (i : DyadicInterval bits) : DyadicInterval bits :=
  normalizeWithFuel (maxEndpointAbs i + 1) i

noncomputable section

def scale (exp : Int) : ℝ := (2 : ℝ) ^ exp

def endpoint (n : Int) (exp : Int) : ℝ := (n : ℝ) * scale exp

def lowerBound {bits : Option Nat} (i : DyadicInterval bits) (x : ℝ) : Prop :=
  ∀ lo, i.lo = some lo → endpoint lo i.exp ≤ x

def upperBound {bits : Option Nat} (i : DyadicInterval bits) (x : ℝ) : Prop :=
  ∀ hi, i.hi = some hi → x ≤ endpoint hi i.exp

def interval {bits : Option Nat} (i : DyadicInterval bits) : Set ℝ :=
  {x | lowerBound i x ∧ upperBound i x}

instance {bits : Option Nat} : Interval.IntervalType (DyadicInterval bits) ℝ where
  interval := interval

instance {bits : Option Nat} : Zero (DyadicInterval bits) where
  zero := ⟨some 0, some 0, 0⟩

instance {bits : Option Nat} : Add (DyadicInterval bits) where
  add i j :=
    if i.exp = j.exp then
      ⟨addEndpoint i.lo j.lo, addEndpoint i.hi j.hi, i.exp⟩
    else
      ⊤

instance {bits : Option Nat} : Neg (DyadicInterval bits) where
  neg i := ⟨i.hi.map Int.neg, i.lo.map Int.neg, i.exp⟩

instance {bits : Option Nat} : Sub (DyadicInterval bits) where
  sub i j := i + -j

instance {bits : Option Nat} : One (DyadicInterval bits) where
  one := ⟨some 1, some 1, 0⟩

instance {bits : Option Nat} : NatCast (DyadicInterval bits) where
  natCast n := ⟨some n, some n, 0⟩

instance {bits : Option Nat} : IntCast (DyadicInterval bits) where
  intCast n := ⟨some n, some n, 0⟩

instance {bits : Option Nat} : NNRatCast (DyadicInterval bits) where
  nnratCast _ := ⊤

instance {bits : Option Nat} : RatCast (DyadicInterval bits) where
  ratCast _ := ⊤

instance {bits : Option Nat} : Mul (DyadicInterval bits) where
  mul _ _ := ⊤

/-- Conservative total inversion. This is intentionally `⊤`; in particular it is
sound when the input interval contains zero. -/
instance {bits : Option Nat} : Inv (DyadicInterval bits) where
  inv _ := ⊤

instance {bits : Option Nat} : Div (DyadicInterval bits) where
  div _ _ := ⊤

instance {bits : Option Nat} : NatPow (DyadicInterval bits) where
  pow _ _ := ⊤

instance {bits : Option Nat} : Pow (DyadicInterval bits) Int where
  pow _ _ := ⊤

instance {bits : Option Nat} : AddGroupOps (DyadicInterval bits) where
  nsmul
    | 0, _ => 0
    | _, _ => ⊤
  zsmul
    | 0, _ => 0
    | _, _ => ⊤

instance {bits : Option Nat} : GroupOps (DyadicInterval bits) where
  npow n x := x ^ n
  zpow n x := x ^ n

instance {bits : Option Nat} : FieldOps (DyadicInterval bits) where
  nnqsmul _ _ := ⊤
  qsmul _ _ := ⊤

theorem mem_top {bits : Option Nat} (x : ℝ) : x ∈ (⊤ : DyadicInterval bits) := by
  constructor
  · intro lo hlo
    cases hlo
  · intro hi hhi
    cases hhi

theorem endpoint_zero : endpoint 0 0 = 0 := by
  simp [endpoint, scale]

theorem endpoint_add (x y : Int) (exp : Int) :
    endpoint (x + y) exp = endpoint x exp + endpoint y exp := by
  simp [endpoint, add_mul]

theorem mem_zero {bits : Option Nat} : (0 : ℝ) ∈ (0 : DyadicInterval bits) := by
  constructor
  · intro lo hlo
    change (some 0 : Option Int) = some lo at hlo
    cases hlo
    norm_num [endpoint, scale]
  · intro hi hhi
    change (some 0 : Option Int) = some hi at hhi
    cases hhi
    norm_num [endpoint, scale]

theorem mem_one {bits : Option Nat} : (1 : ℝ) ∈ (1 : DyadicInterval bits) := by
  constructor
  · intro lo hlo
    change (some 1 : Option Int) = some lo at hlo
    cases hlo
    change endpoint 1 0 ≤ (1 : ℝ)
    norm_num [endpoint, scale]
  · intro hi hhi
    change (some 1 : Option Int) = some hi at hhi
    cases hhi
    change (1 : ℝ) ≤ endpoint 1 0
    norm_num [endpoint, scale]

theorem neg_mem {bits : Option Nat} {x : ℝ} {i : DyadicInterval bits} :
    x ∈ i → -x ∈ (-i) := by
  intro hx
  constructor
  · intro lo hlo
    cases hhi : i.hi with
    | none => simp [Neg.neg, hhi] at hlo
    | some hi =>
      simp [Neg.neg, hhi] at hlo
      subst lo
      have hupper := hx.2 hi hhi
      have hendpoint : endpoint (-hi) i.exp = -endpoint hi i.exp := by
        simp [endpoint]
      change endpoint (-hi) i.exp ≤ -x
      rw [hendpoint]
      exact neg_le_neg hupper
  · intro hi hhi
    cases hlo : i.lo with
    | none => simp [Neg.neg, hlo] at hhi
    | some lo =>
      simp [Neg.neg, hlo] at hhi
      subst hi
      have hlower := hx.1 lo hlo
      have hendpoint : endpoint (-lo) i.exp = -endpoint lo i.exp := by
        simp [endpoint]
      change -x ≤ endpoint (-lo) i.exp
      rw [hendpoint]
      exact neg_le_neg hlower

theorem add_mem {bits : Option Nat} {x y : ℝ} {i j : DyadicInterval bits} :
    x ∈ i → y ∈ j → x + y ∈ (i + j) := by
  intro hx hy
  by_cases h : i.exp = j.exp
  · rw [show i + j = ⟨addEndpoint i.lo j.lo, addEndpoint i.hi j.hi, i.exp⟩ by
      simp [HAdd.hAdd, Add.add, h]]
    constructor
    · intro lo hlo
      cases hlo_i : i.lo with
      | none => simp [addEndpoint, hlo_i] at hlo
      | some ilo =>
        cases hlo_j : j.lo with
        | none => simp [addEndpoint, hlo_i, hlo_j] at hlo
        | some jlo =>
          simp [addEndpoint, hlo_i, hlo_j] at hlo
          subst lo
          have hxi := hx.1 ilo hlo_i
          have hyj := hy.1 jlo hlo_j
          have hyj' : endpoint jlo i.exp ≤ y := by simpa [h] using hyj
          calc
            endpoint (ilo + jlo) i.exp = endpoint ilo i.exp + endpoint jlo i.exp := endpoint_add ilo jlo i.exp
            _ ≤ x + y := add_le_add hxi hyj'
    · intro hi hhi
      cases hhi_i : i.hi with
      | none => simp [addEndpoint, hhi_i] at hhi
      | some ihi =>
        cases hhi_j : j.hi with
        | none => simp [addEndpoint, hhi_i, hhi_j] at hhi
        | some jhi =>
          simp [addEndpoint, hhi_i, hhi_j] at hhi
          subst hi
          have hxi := hx.2 ihi hhi_i
          have hyj := hy.2 jhi hhi_j
          have hyj' : y ≤ endpoint jhi i.exp := by simpa [h] using hyj
          calc
            x + y ≤ endpoint ihi i.exp + endpoint jhi i.exp := add_le_add hxi hyj'
            _ = endpoint (ihi + jhi) i.exp := (endpoint_add ihi jhi i.exp).symm
  · rw [show i + j = ⊤ by simp [HAdd.hAdd, Add.add, h]]
    exact mem_top (x + y)

instance {bits : Option Nat} : Interval.LawfulTop (DyadicInterval bits) ℝ where
  mem_top := mem_top

instance {bits : Option Nat} : Interval.LawfulZero (DyadicInterval bits) ℝ where
  zero_mem_interval := mem_zero

instance {bits : Option Nat} : Interval.LawfulOne (DyadicInterval bits) ℝ where
  one_mem_interval := mem_one

instance {bits : Option Nat} : Interval.LawfulNeg (DyadicInterval bits) ℝ where
  neg_mem_interval := neg_mem

instance {bits : Option Nat} : Interval.LawfulAdd (DyadicInterval bits) ℝ where
  add_mem_interval := add_mem

instance {bits : Option Nat} : Interval.LawfulSub (DyadicInterval bits) ℝ where
  sub_mem_interval := by
    intro x y i j hx hy
    rw [sub_eq_add_neg]
    change x + -y ∈ (i + -j)
    exact add_mem hx (neg_mem hy)

instance {bits : Option Nat} : Interval.LawfulMul (DyadicInterval bits) ℝ where
  mul_mem_interval := by
    intro x y i j hx hy
    exact mem_top (x * y)

instance {bits : Option Nat} : Interval.LawfulInv (DyadicInterval bits) ℝ where
  inv_mem_interval := by
    intro x i hx
    exact mem_top x⁻¹

instance {bits : Option Nat} : Interval.LawfulDiv (DyadicInterval bits) ℝ where
  div_mem_interval := by
    intro x y i j hx hy
    exact mem_top (x / y)

instance {bits : Option Nat} : Interval.LawfulAddGroupOps (DyadicInterval bits) ℝ where

instance {bits : Option Nat} : Interval.LawfulGroupOps (DyadicInterval bits) ℝ where

instance {bits : Option Nat} : Interval.LawfulFieldOps (DyadicInterval bits) ℝ where

end

end DyadicInterval

end NumLean
