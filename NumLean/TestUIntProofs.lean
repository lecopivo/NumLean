

def sumSquares (n : Nat) : Nat :=
  go 0 0
where
  go (i : Nat) (s : Nat) : Nat :=
    if i < n then
      go (i+1) (i*i + s)
    else
      s

def sumSquaresUInt (n : UInt64) : UInt64 :=
  go 0 0
where
  go (i : UInt64) (s : UInt64) : UInt64 :=
    if _h : i < n then
      go (i+1) (i*i + s)
    else
      s
  termination_by n.toNat - i.toNat
  decreasing_by
    have hi : i.toNat < n.toNat := UInt64.lt_iff_toNat_lt.mp _h
    have hn : n.toNat < 2 ^ 64 := UInt64.toNat_lt n
    have hadd : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one]; omega
    omega

/-- The `UInt64` accumulator stays congruent (mod `2^64`) to the unbounded `Nat`
accumulator throughout the recursion, so the `UInt64` result is the true sum of
squares reduced mod `2^64`. -/
theorem sumSquaresUInt.go_mod (n : UInt64) :
    ∀ (i sU : UInt64) (sN : Nat),
      sN % 2 ^ 64 = sU.toNat →
      sumSquares.go n.toNat i.toNat sN % 2 ^ 64 = (sumSquaresUInt.go n i sU).toNat := by
  intro i sU
  induction i, sU using sumSquaresUInt.go.induct (n := n) with
  | case1 i sU hlt ih =>
      intro sN hs
      have hi : i.toNat < n.toNat := UInt64.lt_iff_toNat_lt.mp hlt
      have hadd : (i + 1).toNat = i.toNat + 1 := by
        have hn : n.toNat < 2 ^ 64 := UInt64.toNat_lt n
        rw [UInt64.toNat_add, UInt64.toNat_one]; omega
      rw [sumSquaresUInt.go.eq_def, sumSquares.go.eq_def]
      simp only [dif_pos hlt, if_pos hi]
      rw [← hadd]
      apply ih
      -- the new accumulators are still congruent mod `2^64`
      rw [UInt64.toNat_add, UInt64.toNat_mul]
      omega
  | case2 i sU hnlt =>
      intro sN hs
      have hi : ¬ i.toNat < n.toNat := fun h => hnlt (UInt64.lt_iff_toNat_lt.mpr h)
      rw [sumSquaresUInt.go.eq_def, sumSquares.go.eq_def]
      simp only [dif_neg hnlt, if_neg hi]
      exact hs

/-- As long as the true sum of squares fits in `UInt64` (no overflow), the
`UInt64` computation agrees with the `Nat` one. -/
theorem sumSquares_eq (n : UInt64) (h : sumSquares n.toNat < 2 ^ 64) :
    sumSquares n.toNat = (sumSquaresUInt n).toNat := by
  have key := sumSquaresUInt.go_mod n 0 0 0 (by simp)
  simp only [UInt64.toNat_ofNat] at key
  unfold sumSquares sumSquaresUInt
  rw [← key]
  exact (Nat.mod_eq_of_lt h).symm
