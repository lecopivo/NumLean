import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace NumLean

def _root_.Dyadic.toFloat (x : Dyadic) : Float :=
  match x with
  | .zero => 0
  | .ofOdd n p _ => n.toInt64.toFloat * 2 ^ (-p.toInt64.toFloat)

@[coe]
def _root_.Dyadic.toReal (x : Dyadic) : ℝ := x.toRat

instance : Coe Dyadic ℝ := ⟨Dyadic.toReal⟩

@[simp]
theorem Dyadic.cast_toRat_eq_toReal (x : Dyadic) : (x.toRat : ℝ) = x.toReal := by rfl

@[simp]
theorem Dyadic.toReal_zero : (0 : Dyadic).toReal = 0 := by simp [Dyadic.toReal]

@[simp, grind =]
theorem Dyadic.toReal_add (x y : Dyadic) : ((x + y : Dyadic) : ℝ) = (x : ℝ) + (y : ℝ) := by
  change (((x + y).toRat : Rat) : ℝ) = ((x.toRat : Rat) : ℝ) + ((y.toRat : Rat) : ℝ)
  rw [Dyadic.toRat_add, Rat.cast_add]

@[simp, grind =]
theorem Dyadic.toReal_neg (x : Dyadic) : ((-x : Dyadic) : ℝ) = -(x : ℝ) := by
  change (((-x).toRat : Rat) : ℝ) = -((x.toRat : Rat) : ℝ)
  rw [Dyadic.toRat_neg, Rat.cast_neg]

@[simp, grind =]
theorem Dyadic.toReal_mul (x y : Dyadic) : ((x * y : Dyadic) : ℝ) = (x : ℝ) * (y : ℝ) := by
  change (((x * y).toRat : Rat) : ℝ) = ((x.toRat : Rat) : ℝ) * ((y.toRat : Rat) : ℝ)
  rw [Dyadic.toRat_mul, Rat.cast_mul]

@[simp]
theorem Dyadic.toReal_pow (x : Dyadic) (n : Nat) : ((x ^ n : Dyadic) : ℝ) = (x : ℝ) ^ n := by
  change (((x ^ n).toRat : Rat) : ℝ) = ((x.toRat : Rat) : ℝ) ^ n
  rw [Dyadic.toRat_pow, Rat.cast_pow]

@[simp]
theorem Dyadic.toReal_one : (1 : Dyadic).toReal = 1 := by
  change (((1 : Dyadic).toRat : Rat) : ℝ) = 1
  rw [show (1 : Dyadic).toRat = (1 : Rat) by exact Dyadic.toRat_natCast 1]
  rw [Rat.cast_one]

@[simp]
theorem Dyadic.toReal_natCast (n : Nat) : ((n : Dyadic) : ℝ) = n := by
  change (((n : Dyadic).toRat : Rat) : ℝ) = (n : ℝ)
  rw [Dyadic.toRat_natCast]
  norm_num

@[simp]
theorem Dyadic.toReal_intCast (n : Int) : ((n : Dyadic) : ℝ) = n := by
  change (((n : Dyadic).toRat : Rat) : ℝ) = (n : ℝ)
  rw [Dyadic.toRat_intCast]
  norm_num

theorem Dyadic.toReal_le_toReal {x y : Dyadic} (h : x ≤ y) : (x : ℝ) ≤ (y : ℝ) := by
  change ((x.toRat : Rat) : ℝ) ≤ ((y.toRat : Rat) : ℝ)
  rw [Rat.cast_le, Dyadic.toRat_le_toRat_iff]
  exact h

theorem Dyadic.toReal_lt_toReal {x y : Dyadic} (h : x < y) : (x : ℝ) < (y : ℝ) := by
  change ((x.toRat : Rat) : ℝ) < ((y.toRat : Rat) : ℝ)
  rw [Rat.cast_lt, Dyadic.toRat_lt_toRat_iff]
  exact h

def _root_.Dyadic.minD (x y : Dyadic) : Dyadic :=
  if x ≤ y then x else y

def _root_.Dyadic.maxD (x y : Dyadic) : Dyadic :=
  if x ≤ y then y else x

@[simp]
theorem Dyadic.toReal_minD (x y : Dyadic) : ((x.minD y : Dyadic) : ℝ) = min (x : ℝ) (y : ℝ) := by
  by_cases h : x ≤ y
  · have h' : (x : ℝ) ≤ (y : ℝ) := Dyadic.toReal_le_toReal h
    simp [Dyadic.minD, h, min_eq_left h']
  · have h' : (y : ℝ) ≤ (x : ℝ) := Dyadic.toReal_le_toReal ((Dyadic.le_total x y).resolve_left h)
    simp [Dyadic.minD, h, min_eq_right h']

@[simp]
theorem Dyadic.toReal_maxD (x y : Dyadic) : ((x.maxD y : Dyadic) : ℝ) = max (x : ℝ) (y : ℝ) := by
  by_cases h : x ≤ y
  · have h' : (x : ℝ) ≤ (y : ℝ) := Dyadic.toReal_le_toReal h
    simp [Dyadic.maxD, h, max_eq_right h']
  · have h' : (y : ℝ) ≤ (x : ℝ) := Dyadic.toReal_le_toReal ((Dyadic.le_total x y).resolve_left h)
    simp [Dyadic.maxD, h, max_eq_left h']

def _root_.Dyadic.roundDown? (x : Dyadic) (prec? : Option Int) : Dyadic :=
  match prec? with
  | some prec => x.roundDown prec
  | none => x

def _root_.Dyadic.roundUp? (x : Dyadic) (prec? : Option Int) : Dyadic :=
  match prec? with
  | some prec => x.roundUp prec
  | none => x

@[simp, grind .]
theorem _root_.Dyadic.roundDown?_le_toReal (x : Dyadic) (prec? : Option Int) :
    ((x.roundDown? prec? : Dyadic) : ℝ) ≤ (x : ℝ) := by
  cases prec? with
  | none => simp [Dyadic.roundDown?]
  | some prec =>
    change (((x.roundDown prec).toRat : Rat) : ℝ) ≤ ((x.toRat : Rat) : ℝ)
    rw [Rat.cast_le]
    simpa [Dyadic.toRat_le_toRat_iff] using (Dyadic.roundDown_le (x := x) (prec := prec))

@[simp, grind .]
theorem _root_.Dyadic.toReal_le_roundUp? (x : Dyadic) (prec? : Option Int) :
    (x : ℝ) ≤ ((x.roundUp? prec? : Dyadic) : ℝ) := by
  cases prec? with
  | none => simp [Dyadic.roundUp?]
  | some prec =>
    change (((x.toRat : Rat) : ℝ)) ≤ (((x.roundUp prec).toRat : Rat) : ℝ)
    rw [Rat.cast_le]
    simpa [Dyadic.toRat_le_toRat_iff] using (Dyadic.le_roundUp (x := x) (prec := prec))

@[simp, grind =>]
theorem _root_.Dyadic.roundDown?_pow_le_toReal_pow (x : Dyadic) (n : Nat) (prec? : Option Int) :
    (((x ^ n).roundDown? prec? : Dyadic) : ℝ) ≤ (x : ℝ) ^ n := by
  simpa using (Dyadic.roundDown?_le_toReal (x ^ n) prec?)

@[simp, grind =>]
theorem _root_.Dyadic.toReal_pow_le_roundUp?_pow (x : Dyadic) (n : Nat) (prec? : Option Int) :
    (x : ℝ) ^ n ≤ (((x ^ n).roundUp? prec? : Dyadic) : ℝ) := by
  simpa using (Dyadic.toReal_le_roundUp? (x ^ n) prec?)

@[grind =>]
theorem _root_.Dyadic.roundDown?_add_le {a b : Dyadic} {x y : ℝ} {prec? : Option Int}
    (ha : (a : ℝ) ≤ x) (hb : (b : ℝ) ≤ y) :
    (((a + b).roundDown? prec? : Dyadic) : ℝ) ≤ x + y := by
  have h := Dyadic.roundDown?_le_toReal (a + b) prec?
  rw [Dyadic.toReal_add] at h
  linarith

@[grind =>]
theorem _root_.Dyadic.add_le_roundUp? {a b : Dyadic} {x y : ℝ} {prec? : Option Int}
    (ha : x ≤ (a : ℝ)) (hb : y ≤ (b : ℝ)) :
    x + y ≤ (((a + b).roundUp? prec? : Dyadic) : ℝ) := by
  have h := Dyadic.toReal_le_roundUp? (a + b) prec?
  rw [Dyadic.toReal_add] at h
  linarith

def _root_.Dyadic.mulLower (a b c d : Dyadic) : Dyadic :=
  (a * c).minD (a * d) |>.minD ((b * c).minD (b * d))

def _root_.Dyadic.mulUpper (a b c d : Dyadic) : Dyadic :=
  (a * c).maxD (a * d) |>.maxD ((b * c).maxD (b * d))

theorem _root_.Dyadic.mulLower_le {a b c d : Dyadic} {x y : ℝ}
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hcy : (c : ℝ) ≤ y) (hyd : y ≤ (d : ℝ)) :
    (Dyadic.mulLower a b c d : ℝ) ≤ x * y := by
  simp only [Dyadic.mulLower, Dyadic.toReal_minD, Dyadic.toReal_mul]
  by_cases hy0 : 0 ≤ y
  · by_cases ha0 : 0 ≤ (a : ℝ)
    · have h1 : (a : ℝ) * c ≤ (a : ℝ) * y := mul_le_mul_of_nonneg_left hcy ha0
      have h2 : (a : ℝ) * y ≤ x * y := mul_le_mul_of_nonneg_right hax hy0
      exact (min_le_left _ _).trans ((min_le_left _ _).trans (h1.trans h2))
    · have h1 : (a : ℝ) * d ≤ (a : ℝ) * y := mul_le_mul_of_nonpos_left hyd (le_of_not_ge ha0)
      have h2 : (a : ℝ) * y ≤ x * y := mul_le_mul_of_nonneg_right hax hy0
      exact (min_le_left _ _).trans ((min_le_right _ _).trans (h1.trans h2))
  · have hy0' : y ≤ 0 := le_of_not_ge hy0
    by_cases hb0 : 0 ≤ (b : ℝ)
    · have h1 : (b : ℝ) * c ≤ (b : ℝ) * y := mul_le_mul_of_nonneg_left hcy hb0
      have h2 : (b : ℝ) * y ≤ x * y := mul_le_mul_of_nonpos_right hxb hy0'
      exact (min_le_right _ _).trans ((min_le_left _ _).trans (h1.trans h2))
    · have h1 : (b : ℝ) * d ≤ (b : ℝ) * y := mul_le_mul_of_nonpos_left hyd (le_of_not_ge hb0)
      have h2 : (b : ℝ) * y ≤ x * y := mul_le_mul_of_nonpos_right hxb hy0'
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (h1.trans h2))

theorem _root_.Dyadic.le_mulUpper {a b c d : Dyadic} {x y : ℝ}
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hcy : (c : ℝ) ≤ y) (hyd : y ≤ (d : ℝ)) :
    x * y ≤ (Dyadic.mulUpper a b c d : ℝ) := by
  simp only [Dyadic.mulUpper, Dyadic.toReal_maxD, Dyadic.toReal_mul]
  by_cases hy0 : 0 ≤ y
  · by_cases hb0 : 0 ≤ (b : ℝ)
    · have h1 : x * y ≤ (b : ℝ) * y := mul_le_mul_of_nonneg_right hxb hy0
      have h2 : (b : ℝ) * y ≤ (b : ℝ) * d := mul_le_mul_of_nonneg_left hyd hb0
      exact (h1.trans h2).trans ((le_max_right _ _).trans (le_max_right _ _))
    · have h1 : x * y ≤ (b : ℝ) * y := mul_le_mul_of_nonneg_right hxb hy0
      have h2 : (b : ℝ) * y ≤ (b : ℝ) * c := mul_le_mul_of_nonpos_left hcy (le_of_not_ge hb0)
      exact (h1.trans h2).trans ((le_max_left _ _).trans (le_max_right _ _))
  · have hy0' : y ≤ 0 := le_of_not_ge hy0
    by_cases ha0 : 0 ≤ (a : ℝ)
    · have h1 : x * y ≤ (a : ℝ) * y := mul_le_mul_of_nonpos_right hax hy0'
      have h2 : (a : ℝ) * y ≤ (a : ℝ) * d := mul_le_mul_of_nonneg_left hyd ha0
      exact (h1.trans h2).trans ((le_max_right _ _).trans (le_max_left _ _))
    · have h1 : x * y ≤ (a : ℝ) * y := mul_le_mul_of_nonpos_right hax hy0'
      have h2 : (a : ℝ) * y ≤ (a : ℝ) * c := mul_le_mul_of_nonpos_left hcy (le_of_not_ge ha0)
      exact (h1.trans h2).trans ((le_max_left _ _).trans (le_max_left _ _))

@[grind =>]
theorem _root_.Dyadic.roundDown?_mulLower_le {a b c d : Dyadic} {x y : ℝ} {prec? : Option Int}
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hcy : (c : ℝ) ≤ y) (hyd : y ≤ (d : ℝ)) :
    ((Dyadic.mulLower a b c d).roundDown? prec? : ℝ) ≤ x * y := by
  exact (Dyadic.roundDown?_le_toReal (Dyadic.mulLower a b c d) prec?).trans
    (Dyadic.mulLower_le hax hxb hcy hyd)

@[grind =>]
theorem _root_.Dyadic.le_roundUp?_mulUpper {a b c d : Dyadic} {x y : ℝ} {prec? : Option Int}
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hcy : (c : ℝ) ≤ y) (hyd : y ≤ (d : ℝ)) :
    x * y ≤ ((Dyadic.mulUpper a b c d).roundUp? prec? : ℝ) := by
  exact (Dyadic.le_mulUpper hax hxb hcy hyd).trans
    (Dyadic.toReal_le_roundUp? (Dyadic.mulUpper a b c d) prec?)

def _root_.Dyadic.toString (x : Dyadic) : String := s!"{x.toFloat}"

instance : ToString Dyadic := ⟨(·.toString)⟩

end NumLean
