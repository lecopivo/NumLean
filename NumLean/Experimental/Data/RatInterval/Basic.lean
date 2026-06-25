import Mathlib.Tactic
import NumLean.Algebra.Instances
import NumLean.Algebra.Ops
import NumLean.Experimental.Interfaces.Interval

namespace NumLean

/-- Rational intervals `[lo, hi]`.

`none` lower/upper endpoints represent `-∞`/`+∞`, respectively. This is mostly a
proof-of-concept interval type: easy to reason about, less attractive for computation. -/
structure RatInterval where
  lo : Option ℚ
  hi : Option ℚ
deriving Repr, DecidableEq

namespace RatInterval

def top : RatInterval := ⟨none, none⟩

instance : Top RatInterval := ⟨top⟩

def addEndpoint : Option ℚ → Option ℚ → Option ℚ
  | some x, some y => some (x + y)
  | _, _ => none

def lowerBound (i : RatInterval) (x : ℚ) : Prop :=
  ∀ lo, i.lo = some lo → lo ≤ x

def upperBound (i : RatInterval) (x : ℚ) : Prop :=
  ∀ hi, i.hi = some hi → x ≤ hi

def interval (i : RatInterval) : Set ℚ :=
  {x | lowerBound i x ∧ upperBound i x}

instance : Interval.IntervalType RatInterval ℚ where
  interval := interval
  split i := (i, i)
  mem_split hx := Or.inl hx

instance : Zero RatInterval where
  zero := ⟨some 0, some 0⟩

instance : One RatInterval where
  one := ⟨some 1, some 1⟩

instance : NatCast RatInterval where
  natCast n := ⟨some n, some n⟩

instance : IntCast RatInterval where
  intCast n := ⟨some n, some n⟩

instance : NNRatCast RatInterval where
  nnratCast q := ⟨some q, some q⟩

instance : RatCast RatInterval where
  ratCast q := ⟨some q, some q⟩

instance : Add RatInterval where
  add i j := ⟨addEndpoint i.lo j.lo, addEndpoint i.hi j.hi⟩

instance : Neg RatInterval where
  neg i := ⟨i.hi.map Neg.neg, i.lo.map Neg.neg⟩

instance : Sub RatInterval where
  sub i j := i + -j

instance : Mul RatInterval where
  mul _ _ := ⊤

/-- Conservative total inversion. A sharper version can inspect whether zero is contained. -/
instance : Inv RatInterval where
  inv _ := ⊤

instance : Div RatInterval where
  div _ _ := ⊤

instance : NatPow RatInterval where
  pow _ _ := ⊤

instance : Pow RatInterval Int where
  pow _ _ := ⊤

instance : AddGroupOps RatInterval where
  nsmul
    | 0, _ => 0
    | _, _ => ⊤
  zsmul
    | 0, _ => 0
    | _, _ => ⊤

instance : GroupOps RatInterval where
  npow n x := x ^ n
  zpow n x := x ^ n

instance : FieldOps RatInterval where
  nnqsmul _ _ := ⊤
  qsmul _ _ := ⊤

theorem mem_top (x : ℚ) : x ∈ (⊤ : RatInterval) := by
  constructor
  · intro lo hlo
    cases hlo
  · intro hi hhi
    cases hhi

theorem mem_zero : (0 : ℚ) ∈ (0 : RatInterval) := by
  constructor
  · intro lo hlo
    change (some 0 : Option ℚ) = some lo at hlo
    cases hlo
    norm_num
  · intro hi hhi
    change (some 0 : Option ℚ) = some hi at hhi
    cases hhi
    norm_num

theorem mem_one : (1 : ℚ) ∈ (1 : RatInterval) := by
  constructor
  · intro lo hlo
    change (some 1 : Option ℚ) = some lo at hlo
    cases hlo
    norm_num
  · intro hi hhi
    change (some 1 : Option ℚ) = some hi at hhi
    cases hhi
    norm_num

theorem neg_mem {x : ℚ} {i : RatInterval} :
    x ∈ i → -x ∈ (-i) := by
  intro hx
  constructor
  · intro lo hlo
    cases hhi : i.hi with
    | none => simp [Neg.neg, hhi] at hlo
    | some hi =>
      simp [Neg.neg, hhi] at hlo
      subst lo
      exact neg_le_neg (hx.2 hi hhi)
  · intro hi hhi
    cases hlo : i.lo with
    | none => simp [Neg.neg, hlo] at hhi
    | some lo =>
      simp [Neg.neg, hlo] at hhi
      subst hi
      exact neg_le_neg (hx.1 lo hlo)

theorem add_mem {x y : ℚ} {i j : RatInterval} :
    x ∈ i → y ∈ j → x + y ∈ (i + j) := by
  intro hx hy
  rw [show i + j = ⟨addEndpoint i.lo j.lo, addEndpoint i.hi j.hi⟩ by
    rfl]
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
        exact add_le_add (hx.1 ilo hlo_i) (hy.1 jlo hlo_j)
  · intro hi hhi
    cases hhi_i : i.hi with
    | none => simp [addEndpoint, hhi_i] at hhi
    | some ihi =>
      cases hhi_j : j.hi with
      | none => simp [addEndpoint, hhi_i, hhi_j] at hhi
      | some jhi =>
        simp [addEndpoint, hhi_i, hhi_j] at hhi
        subst hi
        exact add_le_add (hx.2 ihi hhi_i) (hy.2 jhi hhi_j)

instance : Interval.LawfulTop RatInterval ℚ where
  mem_top := mem_top

instance : Interval.LawfulZero RatInterval ℚ where
  zero_mem_interval := mem_zero

instance : Interval.LawfulOne RatInterval ℚ where
  one_mem_interval := mem_one

instance : Interval.LawfulNeg RatInterval ℚ where
  neg_mem_interval := neg_mem

instance : Interval.LawfulAdd RatInterval ℚ where
  add_mem_interval := add_mem

instance : Interval.LawfulSub RatInterval ℚ where
  sub_mem_interval := by
    intro x y i j hx hy
    rw [sub_eq_add_neg]
    change x + -y ∈ (i + -j)
    exact add_mem hx (neg_mem hy)

instance : Interval.LawfulMul RatInterval ℚ where
  mul_mem_interval := by
    intro x y i j hx hy
    exact mem_top (x * y)

instance : Interval.LawfulInv RatInterval ℚ where
  inv_mem_interval := by
    intro x i hx
    exact mem_top x⁻¹

instance : Interval.LawfulDiv RatInterval ℚ where
  div_mem_interval := by
    intro x y i j hx hy
    exact mem_top (x / y)

instance : Interval.LawfulAddGroupOps RatInterval ℚ where

instance : Interval.LawfulGroupOps RatInterval ℚ where

instance : Interval.LawfulFieldOps RatInterval ℚ where

end RatInterval

end NumLean
