module

public import NumLean.Interfaces.HasFlatRepr.Basic
public import NumLean.Interfaces.Algebra
public import NumLean.Interfaces.Module

@[expose] public section

namespace NumLean

namespace HasFlatRepr

class LawfulZero (X : Type u) (Ks : Nat → Type v) {K : Type w} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [Zero X] [Zero K] : Prop where
  getComp_zero (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (0 : X) i h = 0

class LawfulOne (X : Type u) (Ks : Nat → Type v) {K : Type w} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [One X] [One K] : Prop where
  getComp_one (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (1 : X) i h = 1

class LawfulOfNat (X : Type u) (Ks : Nat → Type v) {K : Type w} (m : Nat) {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [OfNat X m] [OfNat K m] : Prop where
  getComp_ofNat (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (OfNat.ofNat m : X) i h = (OfNat.ofNat m : K)

class LawfulNeg (X : Type u) (Ks : Nat → Type v) {K : Type w} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [Neg X] [Neg K] : Prop where
  getComp_neg (x : X) (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (-x) i h = -getComp (Ks := Ks) (K := K) x i h

class LawfulAdd (X : Type u) (Ks : Nat → Type v) {K : Type w} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [Add X] [Add K] : Prop where
  getComp_add (x y : X) (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (x + y) i h =
      getComp (Ks := Ks) (K := K) x i h + getComp (Ks := Ks) (K := K) y i h

class LawfulSub (X : Type u) (Ks : Nat → Type v) {K : Type w} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [Sub X] [Sub K] : Prop where
  getComp_sub (x y : X) (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (x - y) i h =
      getComp (Ks := Ks) (K := K) x i h - getComp (Ks := Ks) (K := K) y i h

class LawfulMul (X : Type u) (Ks : Nat → Type v) {K : Type w} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [Mul X] [Mul K] : Prop where
  getComp_mul (x y : X) (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (x * y) i h =
      getComp (Ks := Ks) (K := K) x i h * getComp (Ks := Ks) (K := K) y i h

class LawfulInv (X : Type u) (Ks : Nat → Type v) {K : Type w} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [Inv X] [Inv K] : Prop where
  getComp_inv (x : X) (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) x⁻¹ i h = (getComp (Ks := Ks) (K := K) x i h)⁻¹

class LawfulDiv (X : Type u) (Ks : Nat → Type v) {K : Type w} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [Div X] [Div K] : Prop where
  getComp_div (x y : X) (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (x / y) i h =
      getComp (Ks := Ks) (K := K) x i h / getComp (Ks := Ks) (K := K) y i h

class LawfulSMul (R : Type u) (X : Type v) (Ks : Nat → Type w) {K : Type z} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [SMul R X] [SMul R K] : Prop where
  getComp_smul (a : R) (x : X) (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (a • x) i h = a • getComp (Ks := Ks) (K := K) x i h

class LawfulAddMonoidOps (X : Type v) (Ks : Nat → Type w) {K : Type z}
    {nX : Nat} [VectorType Ks K] [HasFlatRepr X Ks nX]
    [RingOps K] [AddMonoidOps X] [SMul K X] [LawfulModuleOps K X] : Prop extends
    LawfulZero X Ks, LawfulAdd X Ks, LawfulSMul K X Ks

class LawfulAddGroupOps (X : Type v) (Ks : Nat → Type w) {K : Type z}
    {nX : Nat} [VectorType Ks K] [HasFlatRepr X Ks nX]
    [RingOps K] [AddGroupOps X] [SMul K X] [LawfulModuleOps K X] : Prop
    extends LawfulAddMonoidOps X Ks, LawfulSub X Ks, LawfulNeg X Ks

class LawfulPowNat (X : Type u) (Ks : Nat → Type v) {K : Type w} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [NatPow X] [NatPow K] : Prop where
  getComp_pow_nat (x : X) (m : Nat) (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (x ^ m) i h = getComp (Ks := Ks) (K := K) x i h ^ m

class LawfulPowInt (X : Type u) (Ks : Nat → Type v) {K : Type w} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [Pow X Int] [Pow K Int] : Prop where
  getComp_pow_int (x : X) (m : Int) (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (x ^ m) i h = getComp (Ks := Ks) (K := K) x i h ^ m

class LawfulStar (X : Type u) (Ks : Nat → Type v) {K : Type w} {nX : Nat}
    [VectorType Ks K] [HasFlatRepr X Ks nX] [Star X] [Star K] : Prop where
  getComp_star (x : X) (i : Nat) (h : i < nX) :
    getComp (Ks := Ks) (K := K) (star x) i h = star (getComp (Ks := Ks) (K := K) x i h)

section ScalarInstances

variable {R : Type u} {Rs : Nat → Type v} [VectorType Rs R]

instance [Zero R] : LawfulZero R Rs where
  getComp_zero := by intros; rfl

instance [One R] : LawfulOne R Rs where
  getComp_one := by intros; rfl

instance (m : Nat) [OfNat R m] : LawfulOfNat R Rs m where
  getComp_ofNat := by intros; rfl

instance [Neg R] : LawfulNeg R Rs where
  getComp_neg := by intros; rfl

instance [Add R] : LawfulAdd R Rs where
  getComp_add := by intros; rfl

instance [Sub R] : LawfulSub R Rs where
  getComp_sub := by intros; rfl

instance [Mul R] : LawfulMul R Rs where
  getComp_mul := by intros; rfl

instance [Inv R] : LawfulInv R Rs where
  getComp_inv := by intros; rfl

instance [Div R] : LawfulDiv R Rs where
  getComp_div := by intros; rfl

instance {S : Type w} [SMul S R] : LawfulSMul S R Rs where
  getComp_smul := by intros; rfl

instance [RingOps R] [LawfulModuleOps R R] : LawfulAddMonoidOps R Rs where

instance [RingOps R] [LawfulModuleOps R R] : LawfulAddGroupOps R Rs where

instance [NatPow R] : LawfulPowNat R Rs where
  getComp_pow_nat := by intros; rfl

instance [Pow R Int] : LawfulPowInt R Rs where
  getComp_pow_int := by intros; rfl

instance [Star R] : LawfulStar R Rs where
  getComp_star := by intros; rfl

end ScalarInstances

end HasFlatRepr

end NumLean
