import NumLean.Experimental.Data.DyadicInterval.Basic

namespace NumLean

namespace DyadicInterval

structure IntervalExtension (prec : Option Int) (f : ℝ → ℝ) where
  eval : DyadicInterval prec → DyadicInterval prec
  mem_eval : ∀ {x : ℝ} {i : DyadicInterval prec}, x ∈ i → f x ∈ eval i

def couldContainZero {prec : Option Int} (i : DyadicInterval prec) : Bool :=
  !decide (i < (0 : DyadicInterval prec)) && !decide ((0 : DyadicInterval prec) < i)

theorem not_lt_zero_of_mem_zero {prec : Option Int} {i : DyadicInterval prec}
    (hzero : (0 : ℝ) ∈ i) : ¬ i < (0 : DyadicInterval prec) := by
  intro hlt
  have hzI : (0 : ℝ) ∈ (0 : DyadicInterval prec) :=
    Interval.LawfulZero.zero_mem_interval (I := DyadicInterval prec) (R := ℝ)
  exact (lt_irrefl (0 : ℝ)) (lt_pointwise hlt hzero hzI)

theorem not_zero_lt_of_mem_zero {prec : Option Int} {i : DyadicInterval prec}
    (hzero : (0 : ℝ) ∈ i) : ¬ (0 : DyadicInterval prec) < i := by
  intro hlt
  have hzI : (0 : ℝ) ∈ (0 : DyadicInterval prec) :=
    Interval.LawfulZero.zero_mem_interval (I := DyadicInterval prec) (R := ℝ)
  exact (lt_irrefl (0 : ℝ)) (lt_pointwise hlt hzI hzero)

theorem couldContainZero_of_mem_zero {prec : Option Int} {i : DyadicInterval prec}
    (hzero : (0 : ℝ) ∈ i) : couldContainZero i = true := by
  have hneg := not_lt_zero_of_mem_zero hzero
  have hpos := not_zero_lt_of_mem_zero hzero
  simp [couldContainZero, hneg, hpos]

theorem couldContainZero_of_root {prec : Option Int} {f : ℝ → ℝ}
    (F : IntervalExtension prec f) {x : ℝ} {i : DyadicInterval prec}
    (hx : x ∈ i) (hroot : f x = 0) : couldContainZero (F.eval i) = true := by
  apply couldContainZero_of_mem_zero
  simpa [hroot] using F.mem_eval hx

def isolateCandidates {prec : Option Int}
    (F : DyadicInterval prec → DyadicInterval prec) : Nat → DyadicInterval prec → List (DyadicInterval prec)
  | 0, i => if couldContainZero (F i) then [i] else []
  | fuel + 1, i =>
    if couldContainZero (F i) then
      let s := Interval.split i
      isolateCandidates F fuel s.1 ++ isolateCandidates F fuel s.2
    else
      []

theorem root_mem_isolateCandidates {prec : Option Int} {f : ℝ → ℝ}
    (F : IntervalExtension prec f) {fuel : Nat} {x : ℝ} {i : DyadicInterval prec}
    (hx : x ∈ i) (hroot : f x = 0) :
    ∃ j ∈ isolateCandidates F.eval fuel i, x ∈ j := by
  induction fuel generalizing i with
  | zero =>
    have hcz := couldContainZero_of_root F hx hroot
    refine ⟨i, ?_, hx⟩
    simp [isolateCandidates, hcz]
  | succ fuel ih =>
    have hcz := couldContainZero_of_root F hx hroot
    rcases Interval.mem_split (I := DyadicInterval prec) (R := ℝ) hx with hx₁ | hx₂
    · rcases ih hx₁ with ⟨j, hj, hxj⟩
      refine ⟨j, ?_, hxj⟩
      simp [isolateCandidates, hcz, hj]
    · rcases ih hx₂ with ⟨j, hj, hxj⟩
      refine ⟨j, ?_, hxj⟩
      simp [isolateCandidates, hcz, hj]


end DyadicInterval

end NumLean
