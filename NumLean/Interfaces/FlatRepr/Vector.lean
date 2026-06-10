import NumLean.Interfaces.FlatRepr.Basic
import NumLean.Interfaces.FlatRepr.Lawful
import Mathlib.Tactic.Linarith

namespace Vector

instance instOne {X : Type _} {n : Nat} [One X] : One (_root_.Vector X n) where
  one := .ofFn fun _ => 1

instance instOfNat {X : Type _} {n : Nat} (m : Nat) [OfNat X m] : OfNat (_root_.Vector X n) m where
  ofNat := .ofFn fun _ => OfNat.ofNat m

instance instInv {X : Type _} {n : Nat} [Inv X] : Inv (_root_.Vector X n) where
  inv x := .ofFn fun i => x[i.1]⁻¹

instance instDiv {X : Type _} {n : Nat} [Div X] : Div (_root_.Vector X n) where
  div x y := .ofFn fun i => x[i.1] / y[i.1]

instance instMulPointwise {X : Type _} {n : Nat} [Mul X] : Mul (_root_.Vector X n) where
  mul x y := .ofFn fun i => x[i.1] * y[i.1]

instance instNatPow {X : Type _} {n : Nat} [NatPow X] : NatPow (_root_.Vector X n) where
  pow x m := .ofFn fun i => x[i.1] ^ m

instance instPowInt {X : Type _} {n : Nat} [Pow X Int] : Pow (_root_.Vector X n) Int where
  pow x m := .ofFn fun i => x[i.1] ^ m

instance instStar {X : Type _} {n : Nat} [Star X] : Star (_root_.Vector X n) where
  star x := .ofFn fun i => star x[i.1]

@[simp] theorem getElem_one {X : Type _} {n i : Nat} [One X] (h : i < n) :
    (One.one : _root_.Vector X n)[i] = 1 := rfl

@[simp] theorem getElem_ofNat {X : Type _} {n i m : Nat} [OfNat X m] (h : i < n) :
    (OfNat.ofNat m : _root_.Vector X n)[i] = (OfNat.ofNat m : X) := rfl

@[simp] theorem getElem_inv {X : Type _} {n i : Nat} [Inv X] (x : _root_.Vector X n) (h : i < n) :
    x⁻¹[i] = x[i]⁻¹ := rfl

@[simp] theorem getElem_div {X : Type _} {n i : Nat} [Div X] (x y : _root_.Vector X n) (h : i < n) :
    (x / y)[i] = x[i] / y[i] := rfl

@[simp] theorem getElem_pow_nat {X : Type _} {n i : Nat} [NatPow X] (x : _root_.Vector X n) (m : Nat) (h : i < n) :
    (x ^ m)[i] = x[i] ^ m := rfl

@[simp] theorem getElem_pow_int {X : Type _} {n i : Nat} [Pow X Int] (x : _root_.Vector X n) (m : Int) (h : i < n) :
    (x ^ m)[i] = x[i] ^ m := rfl

@[simp] theorem getElem_star {X : Type _} {n i : Nat} [Star X] (x : _root_.Vector X n) (h : i < n) :
    (star x)[i] = star x[i] := rfl

end Vector

namespace NumLean


open FlatRepr in
instance {X K n nX} [FlatRepr X K nX] : FlatRepr (Vector X n) K (n * nX) where
  toVector x := x.map (toVector (K:=K)) |>.flatten
  fromVector x :=
    Vector.ofFn fun i : Fin n =>
      FlatRepr.fromVector X (Vector.ofFn fun j : Fin nX =>
        x[i.1 * nX + j.1]'(by have := i.2; have := j.2; nlinarith))
  left_inv := by
    intro x
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_ofFn hi]
    rw [← FlatRepr.fromVector_toVector (K:=K) x[i]]
    congr 1
    apply Vector.ext
    intro j hj
    rw [Vector.getElem_ofFn hj]
    rw [Vector.getElem_flatten]
    rw [Vector.getElem_map]
    · congr
      · exact Nat.div_eq_of_lt_le (Nat.le_add_right _ _) (by
          have hlt : i * nX + j < i * nX + nX := Nat.add_lt_add_left hj _
          simpa [Nat.succ_mul] using hlt)
      · rw [Nat.mul_comm i nX, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  right_inv := by
    intro x
    apply Vector.ext
    intro i hi
    by_cases hzero : nX = 0
    · subst nX
      omega
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by
      rw [Nat.div_lt_iff_lt_mul hnX]
      simpa [Nat.mul_comm] using hi
    have hmod : i % nX < nX := Nat.mod_lt i hnX
    rw [Vector.getElem_flatten]
    rw [Vector.getElem_map]
    rw [Vector.getElem_ofFn hdiv]
    rw [FlatRepr.toVector_fromVector]
    rw [Vector.getElem_ofFn hmod]
    have hidx : (i / nX) * nX + i % nX = i := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod i nX)
    exact getElem_congr (c:=x) (d:=x) rfl hidx (by rw [hidx]; exact hi)
  getComp x i h := ((x.map (FlatRepr.toVector (K:=K))).flatten)[i]
  getComp_spec := by intros; rfl
  setComp x i k h :=
    let x' := ((x.map (FlatRepr.toVector (K:=K))).flatten).set i k h
    Vector.ofFn fun i : Fin n =>
      FlatRepr.fromVector (X:=X) (K:=K) (Vector.ofFn fun j : Fin nX => x'[i.1 * nX + j.1]'(by
        have hj : i.1 * nX + j.1 < i.1 * nX + nX := Nat.add_lt_add_left j.2 _
        have hi : (i.1 + 1) * nX ≤ n * nX := Nat.mul_le_mul_right nX (Nat.succ_le_of_lt i.2)
        exact Nat.lt_of_lt_of_le (by rw [Nat.succ_mul]; exact hj) hi))
  setComp_spec := by intros; rfl

namespace FlatRepr

section VectorLawfulInstances

variable {X K R : Type _} {n nX : Nat} [FlatRepr X K nX]

private theorem vector_getComp_as_base (x : _root_.Vector X n) (i : Nat) (h : i < n * nX)
    (hnX : 0 < nX) (hdiv : i / nX < n) :
    getComp (K:=K) x i h = getComp (K:=K) x[i / nX] (i % nX) (Nat.mod_lt i hnX) := by
  rw [FlatRepr.getComp_spec]
  change ((x.map (FlatRepr.toVector (K:=K))).flatten)[i] = getComp (K:=K) x[i / nX] (i % nX) (Nat.mod_lt i hnX)
  rw [Vector.getElem_flatten]
  rw [Vector.getElem_map]
  rw [← FlatRepr.getComp_spec]

private theorem vector_no_index_of_zero_width {i n : Nat} (h : i < n * 0) : False := by
  omega

instance [Zero X] [Zero K] [LawfulZero X K] :
    LawfulZero (_root_.Vector X n) K where
  getComp_zero i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    have hbase := vector_getComp_as_base (K:=K) (0 : _root_.Vector X n) i h hnX hdiv
    exact hbase.trans (by
      rw [Vector.getElem_zero]
      exact LawfulZero.getComp_zero (X:=X) (K:=K) (i % nX) (Nat.mod_lt i hnX))

instance [One X] [One K] [LawfulOne X K] :
    LawfulOne (_root_.Vector X n) K where
  getComp_one i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    exact (vector_getComp_as_base (K:=K) (1 : _root_.Vector X n) i h hnX hdiv).trans (by
      rw [Vector.getElem_one]
      exact LawfulOne.getComp_one (X:=X) (K:=K) (i % nX) (Nat.mod_lt i hnX))

instance (m : Nat) [OfNat X m] [OfNat K m] [LawfulOfNat X K m] :
    LawfulOfNat (_root_.Vector X n) K m where
  getComp_ofNat i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    exact (vector_getComp_as_base (K:=K) (OfNat.ofNat m : _root_.Vector X n) i h hnX hdiv).trans (by
      rw [Vector.getElem_ofNat]
      exact LawfulOfNat.getComp_ofNat (X:=X) (K:=K) (m:=m) (i % nX) (Nat.mod_lt i hnX))

instance [Neg X] [Neg K] [LawfulNeg X K] :
    LawfulNeg (_root_.Vector X n) K where
  getComp_neg x i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    rw [vector_getComp_as_base (K:=K) (-x) i h hnX hdiv, vector_getComp_as_base (K:=K) x i h hnX hdiv]
    rw [Vector.getElem_neg]
    exact LawfulNeg.getComp_neg x[i / nX] (i % nX) (Nat.mod_lt i hnX)

instance [Add X] [Add K] [LawfulAdd X K] :
    LawfulAdd (_root_.Vector X n) K where
  getComp_add x y i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    rw [vector_getComp_as_base (K:=K) (x + y) i h hnX hdiv, vector_getComp_as_base (K:=K) x i h hnX hdiv,
      vector_getComp_as_base (K:=K) y i h hnX hdiv]
    rw [Vector.getElem_add]
    exact LawfulAdd.getComp_add x[i / nX] y[i / nX] (i % nX) (Nat.mod_lt i hnX)

instance [Sub X] [Sub K] [LawfulSub X K] :
    LawfulSub (_root_.Vector X n) K where
  getComp_sub x y i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    rw [vector_getComp_as_base (K:=K) (x - y) i h hnX hdiv, vector_getComp_as_base (K:=K) x i h hnX hdiv,
      vector_getComp_as_base (K:=K) y i h hnX hdiv]
    rw [Vector.getElem_sub]
    exact LawfulSub.getComp_sub x[i / nX] y[i / nX] (i % nX) (Nat.mod_lt i hnX)

instance [Mul X] [Mul K] [LawfulMul X K] :
    LawfulMul (_root_.Vector X n) K where
  getComp_mul x y i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    rw [vector_getComp_as_base (K:=K) (x * y) i h hnX hdiv, vector_getComp_as_base (K:=K) x i h hnX hdiv,
      vector_getComp_as_base (K:=K) y i h hnX hdiv]
    simpa using (LawfulMul.getComp_mul (X:=X) (K:=K) x[i / nX] y[i / nX] (i % nX) (Nat.mod_lt i hnX))

instance [Inv X] [Inv K] [LawfulInv X K] :
    LawfulInv (_root_.Vector X n) K where
  getComp_inv x i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    rw [vector_getComp_as_base (K:=K) x⁻¹ i h hnX hdiv, vector_getComp_as_base (K:=K) x i h hnX hdiv]
    simpa [Vector.instInv] using (LawfulInv.getComp_inv x[i / nX] (i % nX) (Nat.mod_lt i hnX))

instance [Div X] [Div K] [LawfulDiv X K] :
    LawfulDiv (_root_.Vector X n) K where
  getComp_div x y i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    rw [vector_getComp_as_base (K:=K) (x / y) i h hnX hdiv, vector_getComp_as_base (K:=K) x i h hnX hdiv,
      vector_getComp_as_base (K:=K) y i h hnX hdiv]
    simpa [Vector.instDiv] using (LawfulDiv.getComp_div (X:=X) (K:=K) x[i / nX] y[i / nX] (i % nX) (Nat.mod_lt i hnX))

instance [SMul R X] [SMul R K] [LawfulSMul R X K] :
    LawfulSMul R (_root_.Vector X n) K where
  getComp_smul a x i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    rw [vector_getComp_as_base (K:=K) (a • x) i h hnX hdiv, vector_getComp_as_base (K:=K) x i h hnX hdiv]
    rw [Vector.getElem_smul]
    exact LawfulSMul.getComp_smul a x[i / nX] (i % nX) (Nat.mod_lt i hnX)

instance [NatPow X] [NatPow K] [LawfulPowNat X K] :
    LawfulPowNat (_root_.Vector X n) K where
  getComp_pow_nat x m i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    rw [vector_getComp_as_base (K:=K) (x ^ m) i h hnX hdiv, vector_getComp_as_base (K:=K) x i h hnX hdiv]
    simpa [Vector.instNatPow] using (LawfulPowNat.getComp_pow_nat (X:=X) (K:=K) x[i / nX] m (i % nX) (Nat.mod_lt i hnX))

instance [Pow X Int] [Pow K Int] [LawfulPowInt X K] :
    LawfulPowInt (_root_.Vector X n) K where
  getComp_pow_int x m i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    rw [vector_getComp_as_base (K:=K) (x ^ m) i h hnX hdiv, vector_getComp_as_base (K:=K) x i h hnX hdiv]
    simpa [Vector.instPowInt] using (LawfulPowInt.getComp_pow_int (X:=X) (K:=K) x[i / nX] m (i % nX) (Nat.mod_lt i hnX))

instance [Star X] [Star K] [LawfulStar X K] :
    LawfulStar (_root_.Vector X n) K where
  getComp_star x i h := by
    by_cases hzero : nX = 0
    · subst nX; exact False.elim (vector_no_index_of_zero_width h)
    have hnX : 0 < nX := Nat.pos_of_ne_zero hzero
    have hdiv : i / nX < n := by rw [Nat.div_lt_iff_lt_mul hnX]; simpa [Nat.mul_comm] using h
    rw [vector_getComp_as_base (K:=K) (star x) i h hnX hdiv, vector_getComp_as_base (K:=K) x i h hnX hdiv]
    simpa [Vector.instStar] using (LawfulStar.getComp_star x[i / nX] (i % nX) (Nat.mod_lt i hnX))

end VectorLawfulInstances

end FlatRepr


end NumLean
