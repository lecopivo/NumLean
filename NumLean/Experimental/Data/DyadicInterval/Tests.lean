module

public import NumLean.Experimental.Data.DyadicInterval.Basic

@[expose] public section

namespace NumLean

namespace DyadicIntervalTest

variable {prec : Option Int} {x : ℝ} {I : DyadicInterval prec}

def square {R} [Mul R] (x : R) := x * x

example (hx : x ∈ I) : square x ∈ square I := by
  unfold square
  grind

def cube (x : ℝ) : ℝ := x * x * x
def cubeInterval (I : DyadicInterval prec) : DyadicInterval prec := I ^ (3 : Nat)

example (hx : x ∈ I) : cube x ∈ cubeInterval I := by
  unfold cube cubeInterval
  ring_nf
  grind

def quinticMonomial (x : ℝ) : ℝ := x * x * x * x * x
def quinticMonomialInterval (I : DyadicInterval prec) : DyadicInterval prec := I ^ (5 : Nat)

example (hx : x ∈ I) : quinticMonomial x ∈ quinticMonomialInterval I := by
  unfold quinticMonomial quinticMonomialInterval
  ring_nf
  grind

def powFive (x : ℝ) : ℝ := x ^ (5 : Nat)
def powFiveInterval (I : DyadicInterval prec) : DyadicInterval prec := I ^ (5 : Nat)

example (hx : x ∈ I) : powFive x ∈ powFiveInterval I := by
  unfold powFive powFiveInterval
  grind

def monicQuadratic (x : ℝ) : ℝ := x * x + x + 1
def monicQuadraticInterval (I : DyadicInterval prec) : DyadicInterval prec := I ^ (2 : Nat) + I + 1

example (hx : x ∈ I) : monicQuadratic x ∈ monicQuadraticInterval I := by
  unfold monicQuadratic monicQuadraticInterval
  rw [show x * x + x + 1 = x ^ (2 : Nat) + x + 1 by ring]
  grind

def quadraticWithTwo (x : ℝ) : ℝ := x * x + (2 : ℝ) * x + 1
def quadraticWithTwoInterval (I : DyadicInterval prec) : DyadicInterval prec :=
  I ^ (2 : Nat) + (2 : DyadicInterval prec) * I + 1

example (hx : x ∈ I) : quadraticWithTwo x ∈ quadraticWithTwoInterval I := by
  unfold quadraticWithTwo quadraticWithTwoInterval
  rw [show x * x + (2 : ℝ) * x + 1 = x ^ (2 : Nat) + (2 : ℝ) * x + 1 by ring]
  grind

end DyadicIntervalTest

end NumLean
