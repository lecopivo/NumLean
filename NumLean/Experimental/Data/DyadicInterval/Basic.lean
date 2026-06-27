import NumLean.Data.Scalars.Real.Algebra
import NumLean.Interfaces.Algebra.RNorm
import NumLean.Experimental.Data.DyadicInterval.ExtDyadic
import NumLean.Experimental.Interfaces.Interval

namespace NumLean

/-- Dyadic interval with given precision i.e. all operations are rounded up to this many bits of precision. -/
structure DyadicInterval (prec : Option Int := none) where
  lo : Option Dyadic
  hi : Option Dyadic
deriving DecidableEq

def DyadicInterval.split {prec : Option Int} (i : DyadicInterval prec) :
    DyadicInterval prec × DyadicInterval prec :=
  match i.lo, i.hi with
  | some lo, some hi =>
    let mid := ((lo + hi) >>> (1 : Int)).roundDown? prec
    ({ lo := some lo, hi := some mid }, { lo := some mid, hi := some hi })
  | some lo, _ =>
    let mid := lo + 1
    ({ lo := some lo, hi := some mid }, { lo := some mid, hi := i.hi })
  | none, some hi =>
    let mid := hi - 1
    ({ lo := none, hi := some mid }, { lo := some mid, hi := some hi })
  | none, none =>
    ({ lo := none, hi := some 0 }, { lo := some 0, hi := none })

open Set in
instance {prec : Option Int} : Interval.IntervalType (DyadicInterval prec) ℝ where
  interval i :=
    match i.lo, i.hi with
    | some lo, some hi => Icc lo hi
    | some lo, none => Ici lo
    | none, some hi => Iic hi
    | none, none => ⊤
  split := DyadicInterval.split
  mem_split := by
    intro x i hx
    cases i with
    | mk lo hi =>
      cases lo with
      | some lo =>
        cases hi with
        | some hi =>
          let mid := ((lo + hi) >>> (1 : Int)).roundDown? prec
          by_cases h : x ≤ (mid : ℝ)
          · simp [DyadicInterval.split] at hx ⊢
            exact Or.inl ⟨hx.1, h⟩
          · simp [DyadicInterval.split] at hx ⊢
            exact Or.inr ⟨le_of_not_ge h, hx.2⟩
        | none =>
          by_cases h : x ≤ ((lo + 1 : Dyadic) : ℝ)
          · simp [DyadicInterval.split] at hx ⊢
            exact Or.inl ⟨hx, by simpa using h⟩
          · simp [DyadicInterval.split] at hx ⊢
            exact Or.inr (by simpa using le_of_not_ge h)
      | none =>
        cases hi with
        | some hi =>
          by_cases h : x ≤ ((hi - 1 : Dyadic) : ℝ)
          · simp [DyadicInterval.split] at hx ⊢
            exact Or.inl h
          · simp [DyadicInterval.split] at hx ⊢
            exact Or.inr ⟨le_of_not_ge h, hx⟩
        | none =>
          by_cases h : x ≤ (0 : ℝ)
          · simp [DyadicInterval.split, h]
          · simp [DyadicInterval.split, le_of_not_ge h]

namespace DyadicInterval

def le {prec : Option Int} (i j : DyadicInterval prec) : Prop :=
  match i.hi, j.lo with
  | some hi, some lo => hi ≤ lo
  | _, _ => False

def lt {prec : Option Int} (i j : DyadicInterval prec) : Prop :=
  match i.hi, j.lo with
  | some hi, some lo => hi < lo
  | _, _ => False

instance {prec : Option Int} : LE (DyadicInterval prec) := ⟨le⟩

instance {prec : Option Int} : LT (DyadicInterval prec) := ⟨lt⟩

instance {prec : Option Int} (i j : DyadicInterval prec) : Decidable (i ≤ j) := by
  cases i; cases j
  rename_i ilo ihi jlo jhi
  cases ihi <;> cases jlo <;> simp [LE.le, le] <;> infer_instance

instance {prec : Option Int} (i j : DyadicInterval prec) : Decidable (i < j) := by
  cases i; cases j
  rename_i ilo ihi jlo jhi
  cases ihi <;> cases jlo <;> simp [LT.lt, lt] <;> infer_instance

theorem le_pointwise {prec : Option Int} {i j : DyadicInterval prec} (h : i ≤ j) :
    ∀ {x y : ℝ}, x ∈ i → y ∈ j → x ≤ y := by
  intro x y hx hy
  cases i with
  | mk ilo ihi =>
  cases j with
  | mk jlo jhi =>
  cases ihi <;> cases jlo <;> simp [LE.le, le] at h
  rename_i ihi jlo
  cases ilo <;> cases jhi <;> try simp at hx hy ⊢
  · exact hx.trans ((Dyadic.toReal_le_toReal h).trans hy)
  · exact hx.trans ((Dyadic.toReal_le_toReal h).trans hy.1)
  · exact hx.2.trans ((Dyadic.toReal_le_toReal h).trans hy)
  · exact hx.2.trans ((Dyadic.toReal_le_toReal h).trans hy.1)

theorem lt_pointwise {prec : Option Int} {i j : DyadicInterval prec} (h : i < j) :
    ∀ {x y : ℝ}, x ∈ i → y ∈ j → x < y := by
  intro x y hx hy
  cases i with
  | mk ilo ihi =>
  cases j with
  | mk jlo jhi =>
  cases ihi <;> cases jlo <;> simp [LT.lt, lt] at h
  rename_i ihi jlo
  cases ilo <;> cases jhi <;> try simp at hx hy ⊢
  · exact hx.trans_lt ((Dyadic.toReal_lt_toReal h).trans_le hy)
  · exact hx.trans_lt ((Dyadic.toReal_lt_toReal h).trans_le hy.1)
  · exact hx.2.trans_lt ((Dyadic.toReal_lt_toReal h).trans_le hy)
  · exact hx.2.trans_lt ((Dyadic.toReal_lt_toReal h).trans_le hy.1)

@[simp]
theorem mem_mk {prec : Option Int} {x : ℝ} {lo hi : Option Dyadic} :
    x ∈ ({ lo, hi } : DyadicInterval prec) ↔
      match lo, hi with
      | some lo, some hi => x ∈ Set.Icc (lo : ℝ) hi
      | some lo, none => x ∈ Set.Ici (lo : ℝ)
      | none, some hi => x ∈ Set.Iic (hi : ℝ)
      | none, none => x ∈ (⊤ : Set ℝ) := by
  cases lo <;> cases hi <;> rfl

instance {prec : Option Int} : Top (DyadicInterval prec) := ⟨⟨none, none⟩⟩

instance : Interval.LawfulTop (DyadicInterval bits) ℝ where
  mem_top := by intros; trivial

attribute [simp] Interval.LawfulTop.mem_top

instance {prec : Option Int} : Zero (DyadicInterval prec) where
  zero := ⟨some 0, some 0⟩

instance : Interval.LawfulZero (DyadicInterval bits) ℝ where
  zero_mem_interval := by
    suffices h : (0 : ℝ) ∈ Set.Icc ((0 : Dyadic) : ℝ) ((0 : Dyadic) : ℝ) from h
    simp

instance {prec : Option Int} : Add (DyadicInterval prec) where
  add i j :=
    ⟨i.lo.bind fun ilo => j.lo.map fun jlo => (ilo + jlo).roundDown? prec,
     i.hi.bind fun ihi => j.hi.map fun jhi => (ihi + jhi).roundUp? prec⟩

@[simp]
theorem add_mk {prec : Option Int} (ilo ihi jlo jhi : Option Dyadic) :
    ({ lo := ilo, hi := ihi } : DyadicInterval prec) + { lo := jlo, hi := jhi } =
      { lo := ilo.bind fun ilo => jlo.map fun jlo => (ilo + jlo).roundDown? prec,
        hi := ihi.bind fun ihi => jhi.map fun jhi => (ihi + jhi).roundUp? prec } := by
  cases ilo <;> cases ihi <;> cases jlo <;> cases jhi <;> rfl

instance : Interval.LawfulAdd (DyadicInterval prec) ℝ where
  add_mem_interval := by
    intro x y ⟨ilo, ihi⟩ ⟨jlo, jhi⟩ hx hy
    cases ilo <;> cases ihi <;> cases jlo <;> cases jhi <;> simp at hx hy ⊢ <;> grind

instance {prec : Option Int} : Neg (DyadicInterval prec) where
  neg i :=
    ⟨do let ihi ← i.hi
        return -ihi,
     do let ilo ← i.lo
        return -ilo⟩

instance {prec : Option Int} : Sub (DyadicInterval prec) where
  sub i j := i + -j

@[simp]
theorem neg_mk {prec : Option Int} (lo hi : Option Dyadic) :
    -({ lo, hi } : DyadicInterval prec) =
      { lo := hi.map Neg.neg, hi := lo.map Neg.neg } := by
  cases lo <;> cases hi <;> rfl

instance : Interval.LawfulNeg (DyadicInterval prec) ℝ where
  neg_mem_interval := by
    intro x ⟨lo, hi⟩ hx
    cases lo <;> cases hi <;> simp at hx ⊢ <;> grind

instance : Interval.LawfulSub (DyadicInterval prec) ℝ where
  sub_mem_interval := by
    intro x y i j hx hy
    rw [sub_eq_add_neg]
    change x + -y ∈ (i + -j)
    exact Interval.LawfulAdd.add_mem_interval hx (Interval.LawfulNeg.neg_mem_interval hy)

instance {prec : Option Int} : One (DyadicInterval prec) where
  one := ⟨some 1, some 1⟩

instance : Interval.LawfulOne (DyadicInterval prec) ℝ where
  one_mem_interval := by
    suffices h : (1 : ℝ) ∈ Set.Icc ((1 : Dyadic) : ℝ) ((1 : Dyadic) : ℝ) from h
    simp

instance {prec : Option Int} : NatCast (DyadicInterval prec) where
  natCast n := ⟨some ((n : Dyadic).roundDown? prec), some ((n : Dyadic).roundUp? prec)⟩

@[grind .]
theorem natCast_mem (n : Nat) : (n : ℝ) ∈ (n : DyadicInterval prec) := by
  constructor
  · simpa using (Dyadic.roundDown?_le_toReal (n : Dyadic) prec)
  · simpa using (Dyadic.toReal_le_roundUp? (n : Dyadic) prec)

@[grind .]
theorem two_mem : (2 : ℝ) ∈ (2 : DyadicInterval prec) := natCast_mem 2

instance {prec : Option Int} : IntCast (DyadicInterval prec) where
  intCast n := ⟨some ((n : Dyadic).roundDown? prec), some ((n : Dyadic).roundUp? prec)⟩

@[grind .]
theorem intCast_mem (n : Int) : (n : ℝ) ∈ (n : DyadicInterval prec) := by
  constructor
  · simpa using (Dyadic.roundDown?_le_toReal (n : Dyadic) prec)
  · simpa using (Dyadic.toReal_le_roundUp? (n : Dyadic) prec)

instance {prec : Option Int} : Mul (DyadicInterval prec) where
  mul i j :=
    match i.lo, i.hi, j.lo, j.hi with
    | some ilo, some ihi, some jlo, some jhi =>
      ⟨some ((Dyadic.mulLower ilo ihi jlo jhi).roundDown? prec),
       some ((Dyadic.mulUpper ilo ihi jlo jhi).roundUp? prec)⟩
    | _, _, _, _ => ⊤

@[simp]
theorem mul_mk {prec : Option Int} (ilo ihi jlo jhi : Option Dyadic) :
    ({ lo := ilo, hi := ihi } : DyadicInterval prec) * { lo := jlo, hi := jhi } =
      match ilo, ihi, jlo, jhi with
      | some ilo, some ihi, some jlo, some jhi =>
        { lo := some ((Dyadic.mulLower ilo ihi jlo jhi).roundDown? prec),
          hi := some ((Dyadic.mulUpper ilo ihi jlo jhi).roundUp? prec) }
      | _, _, _, _ => ⊤ := by
  cases ilo <;> cases ihi <;> cases jlo <;> cases jhi <;> rfl

instance : Interval.LawfulMul (DyadicInterval prec) ℝ where
  mul_mem_interval := by
    intro x y ⟨ilo, ihi⟩ ⟨jlo, jhi⟩ hx hy
    cases ilo <;> cases ihi <;> cases jlo <;> cases jhi <;> simp at hx hy ⊢ ; grind

theorem even_pow_le_even_pow_of_nonpos {a b : ℝ} {n : Nat} (hn : Even n)
    (hab : a ≤ b) (hb : b ≤ 0) : b ^ n ≤ a ^ n := by
  have hneg : -b ≤ -a := neg_le_neg hab
  have hbneg : 0 ≤ -b := by linarith
  have h := pow_le_pow_left₀ hbneg hneg n
  simpa [hn.neg_pow] using h

def natPowOdd {prec : Option Int} (i : DyadicInterval prec) (n : Nat) : DyadicInterval prec :=
  { lo := i.lo.map fun lo => (lo ^ n).roundDown? prec,
    hi := i.hi.map fun hi => (hi ^ n).roundUp? prec }

def natPowEven {prec : Option Int} (i : DyadicInterval prec) (n : Nat) : DyadicInterval prec :=
  match i.lo, i.hi with
  | some lo, some hi =>
    if hi ≤ 0 then
      { lo := some ((hi ^ n).roundDown? prec), hi := some ((lo ^ n).roundUp? prec) }
    else if (0 : Dyadic) ≤ lo then
      { lo := some ((lo ^ n).roundDown? prec), hi := some ((hi ^ n).roundUp? prec) }
    else
      { lo := some ((0 : Dyadic).roundDown? prec),
        hi := some (((lo ^ n).maxD (hi ^ n)).roundUp? prec) }
  | none, some hi =>
    if hi ≤ 0 then
      { lo := some ((hi ^ n).roundDown? prec), hi := none }
    else
      { lo := some ((0 : Dyadic).roundDown? prec), hi := none }
  | some lo, none =>
    if (0 : Dyadic) ≤ lo then
      { lo := some ((lo ^ n).roundDown? prec), hi := none }
    else
      { lo := some ((0 : Dyadic).roundDown? prec), hi := none }
  | none, none =>
    { lo := some ((0 : Dyadic).roundDown? prec), hi := none }

def natPow {prec : Option Int} (i : DyadicInterval prec) (n : Nat) : DyadicInterval prec :=
  if n = 0 then
    1
  else if Odd n then
    natPowOdd i n
  else
    natPowEven i n

instance {prec : Option Int} : NatPow (DyadicInterval prec) where
  pow i n := natPow i n

@[simp]
theorem pow_zero {prec : Option Int} (i : DyadicInterval prec) : i ^ (0 : Nat) = 1 := rfl

instance : Interval.LawfulNatPow (DyadicInterval prec) ℝ where
  natPow_mem_interval := by
    intro x i hx n
    cases i with
    | mk lo hi =>
      change x ^ n ∈ natPow ({ lo := lo, hi := hi } : DyadicInterval prec) n
      by_cases h0 : n = 0
      · subst n
        simpa using (Interval.LawfulOne.one_mem_interval (I := DyadicInterval prec) (R := ℝ))
      by_cases hodd : Odd n
      · cases lo with
      | none =>
        cases hi with
        | none => simp [natPow, natPowOdd, h0, hodd]
        | some hi =>
          simp [natPow, natPowOdd, h0, hodd] at hx ⊢
          exact ((Odd.pow_le_pow hodd).2 hx).trans (Dyadic.toReal_pow_le_roundUp?_pow _ n prec)
      | some lo =>
        cases hi with
        | none =>
          simp [natPow, natPowOdd, h0, hodd] at hx ⊢
          exact (Dyadic.roundDown?_pow_le_toReal_pow _ n prec).trans ((Odd.pow_le_pow hodd).2 hx)
        | some hi =>
          simp [natPow, natPowOdd, h0, hodd] at hx ⊢
          constructor
          · exact (Dyadic.roundDown?_pow_le_toReal_pow _ n prec).trans ((Odd.pow_le_pow hodd).2 hx.1)
          · exact ((Odd.pow_le_pow hodd).2 hx.2).trans (Dyadic.toReal_pow_le_roundUp?_pow _ n prec)
      · have heven : Even n := Nat.not_odd_iff_even.mp hodd
        cases lo with
      | none =>
        cases hi with
        | none =>
          simp [natPow, natPowEven, h0, hodd]
          exact (Dyadic.roundDown?_le_toReal (0 : Dyadic) prec).trans (by simpa using heven.pow_nonneg x)
        | some hi =>
          by_cases hhi : hi ≤ 0
          · simp [natPow, natPowEven, h0, hodd, hhi] at hx ⊢
            exact (Dyadic.roundDown?_pow_le_toReal_pow _ n prec).trans
              (even_pow_le_even_pow_of_nonpos heven hx (by simpa using Dyadic.toReal_le_toReal hhi))
          · simp [natPow, natPowEven, h0, hodd, hhi] at hx ⊢
            exact (Dyadic.roundDown?_le_toReal (0 : Dyadic) prec).trans (by simpa using heven.pow_nonneg x)
      | some lo =>
        cases hi with
        | none =>
          by_cases hlo : (0 : Dyadic) ≤ lo
          · simp [natPow, natPowEven, h0, hodd, hlo] at hx ⊢
            have hlo0 : 0 ≤ (lo : ℝ) := by simpa using (Dyadic.toReal_le_toReal hlo)
            exact (Dyadic.roundDown?_pow_le_toReal_pow _ n prec).trans
              (pow_le_pow_left₀ hlo0 hx n)
          · simp [natPow, natPowEven, h0, hodd, hlo] at hx ⊢
            exact (Dyadic.roundDown?_le_toReal (0 : Dyadic) prec).trans (by simpa using heven.pow_nonneg x)
        | some hi =>
          by_cases hhi : hi ≤ 0
          · simp [natPow, natPowEven, h0, hodd, hhi] at hx ⊢
            constructor
            · exact (Dyadic.roundDown?_pow_le_toReal_pow _ n prec).trans
                (even_pow_le_even_pow_of_nonpos heven hx.2 (by simpa using Dyadic.toReal_le_toReal hhi))
            · have hx0 : x ≤ 0 := hx.2.trans (by simpa using Dyadic.toReal_le_toReal hhi)
              exact (even_pow_le_even_pow_of_nonpos heven hx.1 hx0).trans
                (Dyadic.toReal_pow_le_roundUp?_pow _ n prec)
          · by_cases hlo : (0 : Dyadic) ≤ lo
            · simp [natPow, natPowEven, h0, hodd, hhi, hlo] at hx ⊢
              constructor
              · have hlo0 : 0 ≤ (lo : ℝ) := by simpa using (Dyadic.toReal_le_toReal hlo)
                exact (Dyadic.roundDown?_pow_le_toReal_pow _ n prec).trans
                  (pow_le_pow_left₀ hlo0 hx.1 n)
              · have hlo0 : 0 ≤ (lo : ℝ) := by simpa using (Dyadic.toReal_le_toReal hlo)
                have hx0 : 0 ≤ x := hlo0.trans hx.1
                exact (pow_le_pow_left₀ hx0 hx.2 n).trans
                  (Dyadic.toReal_pow_le_roundUp?_pow _ n prec)
            · simp [natPow, natPowEven, h0, hodd, hhi, hlo] at hx ⊢
              constructor
              · exact (Dyadic.roundDown?_le_toReal (0 : Dyadic) prec).trans (by simpa using heven.pow_nonneg x)
              · by_cases hx0 : x ≤ 0
                · have hle : x ^ n ≤ (lo : ℝ) ^ n := even_pow_le_even_pow_of_nonpos heven hx.1 hx0
                  have hmax : x ^ n ≤ (((lo ^ n).maxD (hi ^ n) : Dyadic) : ℝ) := by
                    simpa [Dyadic.toReal_maxD] using hle.trans (le_max_left ((lo : ℝ) ^ n) ((hi : ℝ) ^ n))
                  exact hmax.trans (Dyadic.toReal_le_roundUp? ((lo ^ n).maxD (hi ^ n)) prec)
                · have hx0' : 0 ≤ x := le_of_not_ge hx0
                  have hle : x ^ n ≤ (hi : ℝ) ^ n := pow_le_pow_left₀ hx0' hx.2 n
                  have hmax : x ^ n ≤ (((lo ^ n).maxD (hi ^ n) : Dyadic) : ℝ) := by
                    simpa [Dyadic.toReal_maxD] using hle.trans (le_max_right ((lo : ℝ) ^ n) ((hi : ℝ) ^ n))
                  exact hmax.trans (Dyadic.toReal_le_roundUp? ((lo ^ n).maxD (hi ^ n)) prec)

end DyadicInterval

end NumLean
