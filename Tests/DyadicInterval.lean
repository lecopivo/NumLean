import NumLean.Experimental.Data.DyadicInterval.Basic
import NumLean.Experimental.Data.DyadicInterval.Isolate

namespace NumLean

namespace DyadicIntervalTest

variable {prec : Option Int} {x : ℝ} {I : DyadicInterval prec}

def square {R} [Mul R] (x : R) : R := x * x

example (hx : x ∈ I) : square x ∈ square I := by
  unfold square
  grind

def cube {R} [Mul R] (x : R) : R := x * x * x

example (hx : x ∈ I) : cube x ∈ cube I := by
  unfold cube
  grind

def quinticMonomial {R} [Mul R] (x : R) : R := x * x * x * x * x

example (hx : x ∈ I) : quinticMonomial x ∈ quinticMonomial I := by
  unfold quinticMonomial
  grind

def powFive {R} [NatPow R] (x : R) : R := x ^ (5 : Nat)

example (hx : x ∈ I) : powFive x ∈ powFive I := by
  unfold powFive
  grind

def monicQuadratic {R} [Mul R] [Add R] [One R] (x : R) : R := x * x + x + 1

example (hx : x ∈ I) : monicQuadratic x ∈ monicQuadratic I := by
  unfold monicQuadratic
  grind

end DyadicIntervalTest

section IsolateZeros

open DyadicInterval

macro "dyadic%" n:term "*2^-" p:term : term => `(Dyadic.ofOdd $n $p (by grind))

def sqrtFun {R} [NatPow R] [Sub R] [NatCast R] (x : R) := x^2 - 2

theorem sqrt2_bound1 :
    isolateCandidates (prec:=some 53) sqrtFun 4 ⟨some 1, some 2⟩
    =
    [{ lo := some (dyadic% 11*2^-3), hi := some (dyadic% 23*2^-4) }] := by
  cbv

theorem sqrt2_bound_50 :
    isolateCandidates (prec:=some 53) sqrtFun 50 ⟨some 1, some 2⟩
    =
    [{ lo := some (dyadic% 1592262918131443*2^-50),
        hi := some (dyadic% 398065729532861*2^-48) }] := by cbv

theorem sqrt2_bound_3 : (1414 / 1000 : Rat) ≤ √(2 : ℝ) ∧ √(2 : ℝ) ≤ (1415 / 1000 : Rat) := by
  let F : IntervalExtension (some 53) (fun x : ℝ => sqrtFun x) :=
    { eval := sqrtFun
      mem_eval := by
        intro x i hx
        unfold sqrtFun
        grind }
  have hstart : (√(2 : ℝ)) ∈ (⟨some 1, some 2⟩ : DyadicInterval (some 53)) := by
    simp
    rw [Real.sqrt_le_iff]
    constructor
    · simpa [Dyadic.toReal_zero] using
        Dyadic.toReal_le_toReal (show (0 : Dyadic) ≤ 2 by decide)
    · have h2 : ((2 : Dyadic) : ℝ) = (2 : ℝ) := Dyadic.toReal_natCast 2
      rw [h2]
      norm_num
  have hroot : sqrtFun (√(2 : ℝ)) = 0 := by
    unfold sqrtFun
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hcandidates :
      isolateCandidates (prec := some 53) sqrtFun 12 ⟨some 1, some 2⟩ =
        [{ lo := some (dyadic% 181*2^-7),
           hi := some (dyadic% 5793*2^-12) }] := by
    cbv
  rcases root_mem_isolateCandidates F hstart hroot with ⟨j, hj, hmem⟩
  rw [hcandidates] at hj
  simp at hj
  subst j
  simp at hmem
  have hlo : (181 / 128 : ℝ) ≤ √(2 : ℝ) := by
    convert hmem.1 using 1
    norm_num [Dyadic.toReal, Dyadic.toRat, Rat.cast_def]
  have hhi : √(2 : ℝ) ≤ (5793 / 4096 : ℝ) := by
    convert hmem.2 using 1
    norm_num [Dyadic.toReal, Dyadic.toRat, Rat.cast_def]
  have hlowRat : ((1414 / 1000 : Rat) : ℝ) ≤ (181 / 128 : ℝ) := by
    have h : ((1414 / 1000 : Rat) : ℝ) ≤ ((181 / 128 : Rat) : ℝ) := by
      exact (Rat.cast_le (K := ℝ)).mpr (by cbv : (1414 / 1000 : Rat) ≤ 181 / 128)
    simpa using h
  have hhiRat : (5793 / 4096 : ℝ) ≤ ((1415 / 1000 : Rat) : ℝ) := by
    have h : ((5793 / 4096 : Rat) : ℝ) ≤ ((1415 / 1000 : Rat) : ℝ) := by
      exact (Rat.cast_le (K := ℝ)).mpr (by cbv : (5793 / 4096 : Rat) ≤ 1415 / 1000)
    simpa using h
  constructor
  · exact le_trans hlowRat hlo
  · exact le_trans hhi hhiRat

/-- info: 'NumLean.sqrt2_bound_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrt2_bound_3

theorem sqrt2_bound_15 :
    (1414213562373094 / 1000000000000000 : Rat) ≤ √(2 : ℝ) ∧
      √(2 : ℝ) ≤ (1414213562373096 / 1000000000000000 : Rat) := by
  let F : IntervalExtension (some 53) (fun x : ℝ => sqrtFun x) :=
    { eval := sqrtFun
      mem_eval := by
        intro x i hx
        unfold sqrtFun
        grind }
  have hstart : (√(2 : ℝ)) ∈ (⟨some 1, some 2⟩ : DyadicInterval (some 53)) := by
    simp
    rw [Real.sqrt_le_iff]
    constructor
    · simpa [Dyadic.toReal_zero] using
        Dyadic.toReal_le_toReal (show (0 : Dyadic) ≤ 2 by decide)
    · have h2 : ((2 : Dyadic) : ℝ) = (2 : ℝ) := Dyadic.toReal_natCast 2
      rw [h2]
      norm_num
  have hroot : sqrtFun (√(2 : ℝ)) = 0 := by
    unfold sqrtFun
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rcases root_mem_isolateCandidates F hstart hroot with ⟨j, hj, hmem⟩
  rw [sqrt2_bound_50] at hj
  simp at hj
  subst j
  simp at hmem
  have hlo : (1592262918131443 / 1125899906842624 : ℝ) ≤ √(2 : ℝ) := by
    convert hmem.1 using 1
    norm_num [Dyadic.toReal, Dyadic.toRat, Rat.cast_def]
  have hhi : √(2 : ℝ) ≤ (398065729532861 / 281474976710656 : ℝ) := by
    convert hmem.2 using 1
    norm_num [Dyadic.toReal, Dyadic.toRat, Rat.cast_def]
  have hlowRat :
      ((1414213562373094 / 1000000000000000 : Rat) : ℝ) ≤
        (1592262918131443 / 1125899906842624 : ℝ) := by
    have h :
        ((1414213562373094 / 1000000000000000 : Rat) : ℝ) ≤
          ((1592262918131443 / 1125899906842624 : Rat) : ℝ) := by
      exact (Rat.cast_le (K := ℝ)).mpr
        (by cbv :
          (1414213562373094 / 1000000000000000 : Rat) ≤
            1592262918131443 / 1125899906842624)
    simpa using h
  have hhiRat :
      (398065729532861 / 281474976710656 : ℝ) ≤
        ((1414213562373096 / 1000000000000000 : Rat) : ℝ) := by
    have h :
        ((398065729532861 / 281474976710656 : Rat) : ℝ) ≤
          ((1414213562373096 / 1000000000000000 : Rat) : ℝ) := by
      exact (Rat.cast_le (K := ℝ)).mpr
        (by cbv :
          (398065729532861 / 281474976710656 : Rat) ≤
            1414213562373096 / 1000000000000000)
    simpa using h
  constructor
  · exact le_trans hlowRat hlo
  · exact le_trans hhi hhiRat

/-- info: 'NumLean.sqrt2_bound_15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrt2_bound_15


end IsolateZeros

end NumLean
