import NumLean.Data.Prod
import NumLean.Data.Sigma
import NumLean.Interfaces.FlatRepr.Lawful

namespace NumLean

instance {X Y : Type _} (m : Nat) [OfNat X m] [OfNat Y m] : OfNat (X × Y) m where
  ofNat := (OfNat.ofNat m, OfNat.ofNat m)

instance {X Y : Type _} [NatPow X] [NatPow Y] : NatPow (X × Y) where
  pow xy n := (xy.1 ^ n, xy.2 ^ n)

open FlatRepr in
instance {X Y K nX nY} [FlatRepr X K nX] [FlatRepr Y K nY] :
    FlatRepr (X × Y) K (nX + nY) where
  toVector := fun (x,y) => toVector (K:=K) x ++ toVector (K:=K) y
  fromVector := fun xy =>
    (FlatRepr.fromVector (X:=X) (K:=K) (Vector.ofFn fun i : Fin nX => xy[i.1]),
     FlatRepr.fromVector (X:=Y) (K:=K) (Vector.ofFn fun i : Fin nY => xy[nX + i.1]))
  left_inv := by
    intro (x,y)
    apply Prod.ext
    · change FlatRepr.fromVector (X:=X) (K:=K)
        (Vector.ofFn fun i : Fin nX => (toVector (K:=K) x ++ toVector (K:=K) y)[i.1]) = x
      rw [← FlatRepr.fromVector_toVector (K:=K) x]
      congr 1
      apply Vector.ext
      intro i hi
      rw [Vector.getElem_ofFn hi, Vector.getElem_append_left hi]
      rw [FlatRepr.toVector_fromVector]
    · change FlatRepr.fromVector (X:=Y) (K:=K)
        (Vector.ofFn fun i : Fin nY => (toVector (K:=K) x ++ toVector (K:=K) y)[nX + i.1]) = y
      rw [← FlatRepr.fromVector_toVector (K:=K) y]
      congr 1
      apply Vector.ext
      intro i hi
      rw [Vector.getElem_ofFn hi, Vector.getElem_append_right (Nat.add_lt_add_left hi nX) (by omega)]
      simp [Nat.add_sub_cancel_left]
  right_inv := by
    intro xy; ext i ih
    by_cases h : i < nX
    · rw [Vector.getElem_append_left h]
      rw [FlatRepr.toVector_fromVector]
      rw [Vector.getElem_ofFn h]
    · rw [Vector.getElem_append_right ih (by omega)]
      rw [FlatRepr.toVector_fromVector]
      rw [Vector.getElem_ofFn (by omega)]
      have hidx : nX + (i - nX) = i := Nat.add_sub_of_le (Nat.le_of_not_gt h)
      exact getElem_congr rfl hidx (by omega)
  getComp xy i h :=
    if hi : i < nX then
      FlatRepr.getComp (K:=K) xy.1 i hi
    else
      FlatRepr.getComp (K:=K) xy.2 (i - nX) (by omega)
  getComp_spec := by
    intro xy i h
    rcases xy with ⟨x,y⟩
    by_cases hi : i < nX
    · simp [hi, FlatRepr.getComp_spec, Vector.getElem_append_left hi]
    · simp [hi, FlatRepr.getComp_spec]
      rw [Vector.getElem_append_right h (by omega)]
  -- ugetComp xy i h :=
  --   if h : i < nX.toUSize then
  --     ugetComp xy.1 i sorry
  --   else
  --     ugetComp xy.2 (i - nX.toUSize) sorry
  -- ugetComp_spec := sorry
  setComp xy i k h :=
    let (x,y) := xy
    let xy' := (toVector (K:=K) x ++ toVector (K:=K) y).set i k h
    (FlatRepr.fromVector (X:=X) (K:=K) (Vector.ofFn fun j : Fin nX => xy'[j.1]'(by omega)),
     FlatRepr.fromVector (X:=Y) (K:=K) (Vector.ofFn fun j : Fin nY => xy'[nX + j.1]'(by omega)))
  setComp_spec := by intro xy i k h; rcases xy with ⟨x,y⟩; rfl
  -- usetComp := sorry
  -- usetComp_spec := sorry

namespace FlatRepr

section LawfulInstances

variable {X Y K R : Type _} {nX nY : Nat} [FlatRepr X K nX] [FlatRepr Y K nY]

private theorem prod_getComp_left (xy : X × Y) (i : Nat) (h : i < nX + nY) (hi : i < nX) :
    getComp (K:=K) xy i h = getComp (K:=K) xy.1 i hi := by
  simp [FlatRepr.getComp, hi]

private theorem prod_getComp_right (xy : X × Y) (i : Nat) (h : i < nX + nY) (hi : ¬ i < nX) :
    getComp (K:=K) xy i h = getComp (K:=K) xy.2 (i - nX) (by omega) := by
  simp [FlatRepr.getComp, hi]

instance [Zero X] [Zero Y] [Zero K] [LawfulZero X K] [LawfulZero Y K] :
    LawfulZero (X × Y) K where
  getComp_zero i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (0 : X × Y) i h hi]
      exact LawfulZero.getComp_zero i hi
    · rw [prod_getComp_right (K:=K) (0 : X × Y) i h hi]
      exact LawfulZero.getComp_zero (i - nX) (by omega)

instance [One X] [One Y] [One K] [LawfulOne X K] [LawfulOne Y K] :
    LawfulOne (X × Y) K where
  getComp_one i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (1 : X × Y) i h hi]
      exact LawfulOne.getComp_one i hi
    · rw [prod_getComp_right (K:=K) (1 : X × Y) i h hi]
      exact LawfulOne.getComp_one (i - nX) (by omega)

instance (m : Nat) [OfNat X m] [OfNat Y m] [OfNat K m]
    [LawfulOfNat X K m] [LawfulOfNat Y K m] :
    LawfulOfNat (X × Y) K m where
  getComp_ofNat i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (OfNat.ofNat m : X × Y) i h hi]
      exact LawfulOfNat.getComp_ofNat i hi
    · rw [prod_getComp_right (K:=K) (OfNat.ofNat m : X × Y) i h hi]
      exact LawfulOfNat.getComp_ofNat (i - nX) (by omega)

instance [Neg X] [Neg Y] [Neg K] [LawfulNeg X K] [LawfulNeg Y K] :
    LawfulNeg (X × Y) K where
  getComp_neg x i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (-x) i h hi, prod_getComp_left (K:=K) x i h hi]
      exact LawfulNeg.getComp_neg x.1 i hi
    · rw [prod_getComp_right (K:=K) (-x) i h hi, prod_getComp_right (K:=K) x i h hi]
      exact LawfulNeg.getComp_neg x.2 (i - nX) (by omega)

instance [Add X] [Add Y] [Add K] [LawfulAdd X K] [LawfulAdd Y K] :
    LawfulAdd (X × Y) K where
  getComp_add x y i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (x + y) i h hi, prod_getComp_left (K:=K) x i h hi,
        prod_getComp_left (K:=K) y i h hi]
      exact LawfulAdd.getComp_add x.1 y.1 i hi
    · rw [prod_getComp_right (K:=K) (x + y) i h hi, prod_getComp_right (K:=K) x i h hi,
        prod_getComp_right (K:=K) y i h hi]
      exact LawfulAdd.getComp_add x.2 y.2 (i - nX) (by omega)

instance [Sub X] [Sub Y] [Sub K] [LawfulSub X K] [LawfulSub Y K] :
    LawfulSub (X × Y) K where
  getComp_sub x y i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (x - y) i h hi, prod_getComp_left (K:=K) x i h hi,
        prod_getComp_left (K:=K) y i h hi]
      exact LawfulSub.getComp_sub x.1 y.1 i hi
    · rw [prod_getComp_right (K:=K) (x - y) i h hi, prod_getComp_right (K:=K) x i h hi,
        prod_getComp_right (K:=K) y i h hi]
      exact LawfulSub.getComp_sub x.2 y.2 (i - nX) (by omega)

instance [Mul X] [Mul Y] [Mul K] [LawfulMul X K] [LawfulMul Y K] :
    LawfulMul (X × Y) K where
  getComp_mul x y i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (x * y) i h hi, prod_getComp_left (K:=K) x i h hi,
        prod_getComp_left (K:=K) y i h hi]
      exact LawfulMul.getComp_mul x.1 y.1 i hi
    · rw [prod_getComp_right (K:=K) (x * y) i h hi, prod_getComp_right (K:=K) x i h hi,
        prod_getComp_right (K:=K) y i h hi]
      exact LawfulMul.getComp_mul x.2 y.2 (i - nX) (by omega)

instance [Inv X] [Inv Y] [Inv K] [LawfulInv X K] [LawfulInv Y K] :
    LawfulInv (X × Y) K where
  getComp_inv x i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) x⁻¹ i h hi, prod_getComp_left (K:=K) x i h hi]
      exact LawfulInv.getComp_inv x.1 i hi
    · rw [prod_getComp_right (K:=K) x⁻¹ i h hi, prod_getComp_right (K:=K) x i h hi]
      exact LawfulInv.getComp_inv x.2 (i - nX) (by omega)

instance [Div X] [Div Y] [Div K] [LawfulDiv X K] [LawfulDiv Y K] :
    LawfulDiv (X × Y) K where
  getComp_div x y i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (x / y) i h hi, prod_getComp_left (K:=K) x i h hi,
        prod_getComp_left (K:=K) y i h hi]
      exact LawfulDiv.getComp_div x.1 y.1 i hi
    · rw [prod_getComp_right (K:=K) (x / y) i h hi, prod_getComp_right (K:=K) x i h hi,
        prod_getComp_right (K:=K) y i h hi]
      exact LawfulDiv.getComp_div x.2 y.2 (i - nX) (by omega)

instance [SMul R X] [SMul R Y] [SMul R K] [LawfulSMul R X K] [LawfulSMul R Y K] :
    LawfulSMul R (X × Y) K where
  getComp_smul a x i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (a • x) i h hi, prod_getComp_left (K:=K) x i h hi]
      exact LawfulSMul.getComp_smul a x.1 i hi
    · rw [prod_getComp_right (K:=K) (a • x) i h hi, prod_getComp_right (K:=K) x i h hi]
      exact LawfulSMul.getComp_smul a x.2 (i - nX) (by omega)

instance [NatPow X] [NatPow Y] [NatPow K] [LawfulPowNat X K] [LawfulPowNat Y K] :
    LawfulPowNat (X × Y) K where
  getComp_pow_nat x m i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (x ^ m) i h hi, prod_getComp_left (K:=K) x i h hi]
      exact LawfulPowNat.getComp_pow_nat x.1 m i hi
    · rw [prod_getComp_right (K:=K) (x ^ m) i h hi, prod_getComp_right (K:=K) x i h hi]
      exact LawfulPowNat.getComp_pow_nat x.2 m (i - nX) (by omega)

instance [Pow X Int] [Pow Y Int] [Pow K Int] [LawfulPowInt X K] [LawfulPowInt Y K] :
    LawfulPowInt (X × Y) K where
  getComp_pow_int x m i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (x ^ m) i h hi, prod_getComp_left (K:=K) x i h hi]
      exact LawfulPowInt.getComp_pow_int x.1 m i hi
    · rw [prod_getComp_right (K:=K) (x ^ m) i h hi, prod_getComp_right (K:=K) x i h hi]
      exact LawfulPowInt.getComp_pow_int x.2 m (i - nX) (by omega)

instance [Star X] [Star Y] [Star K] [LawfulStar X K] [LawfulStar Y K] :
    LawfulStar (X × Y) K where
  getComp_star x i h := by
    by_cases hi : i < nX
    · rw [prod_getComp_left (K:=K) (star x) i h hi, prod_getComp_left (K:=K) x i h hi]
      exact LawfulStar.getComp_star x.1 i hi
    · rw [prod_getComp_right (K:=K) (star x) i h hi, prod_getComp_right (K:=K) x i h hi]
      exact LawfulStar.getComp_star x.2 (i - nX) (by omega)

end LawfulInstances

end FlatRepr

end NumLean
