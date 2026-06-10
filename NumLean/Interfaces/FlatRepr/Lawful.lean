import NumLean.Algebra.Ops
import NumLean.Interfaces.FlatRepr.Basic

namespace NumLean

namespace FlatRepr

class LawfulZero (X K : Type _) {nX : Nat} [FlatRepr X K nX] [Zero X] [Zero K] : Prop where
  getComp_zero (i : Nat) (h : i < nX) :
    getComp (K:=K) (0 : X) i h = 0

class LawfulOne (X K : Type _) {nX : Nat} [FlatRepr X K nX] [One X] [One K] : Prop where
  getComp_one (i : Nat) (h : i < nX) :
    getComp (K:=K) (1 : X) i h = 1

class LawfulOfNat (X K : Type _) (m : Nat) {nX : Nat} [FlatRepr X K nX] [OfNat X m] [OfNat K m] : Prop where
  getComp_ofNat (i : Nat) (h : i < nX) :
    getComp (K:=K) (OfNat.ofNat m : X) i h = (OfNat.ofNat m : K)

class LawfulNeg (X K : Type _) {nX : Nat} [FlatRepr X K nX] [Neg X] [Neg K] : Prop where
  getComp_neg (x : X) (i : Nat) (h : i < nX) :
    getComp (K:=K) (-x) i h = -getComp (K:=K) x i h

class LawfulAdd (X K : Type _) {nX : Nat} [FlatRepr X K nX] [Add X] [Add K] : Prop where
  getComp_add (x y : X) (i : Nat) (h : i < nX) :
    getComp (K:=K) (x + y) i h = getComp (K:=K) x i h + getComp (K:=K) y i h

class LawfulSub (X K : Type _) {nX : Nat} [FlatRepr X K nX] [Sub X] [Sub K] : Prop where
  getComp_sub (x y : X) (i : Nat) (h : i < nX) :
    getComp (K:=K) (x - y) i h = getComp (K:=K) x i h - getComp (K:=K) y i h

class LawfulMul (X K : Type _) {nX : Nat} [FlatRepr X K nX] [Mul X] [Mul K] : Prop where
  getComp_mul (x y : X) (i : Nat) (h : i < nX) :
    getComp (K:=K) (x * y) i h = getComp (K:=K) x i h * getComp (K:=K) y i h

class LawfulInv (X K : Type _) {nX : Nat} [FlatRepr X K nX] [Inv X] [Inv K] : Prop where
  getComp_inv (x : X) (i : Nat) (h : i < nX) :
    getComp (K:=K) x⁻¹ i h = (getComp (K:=K) x i h)⁻¹

class LawfulDiv (X K : Type _) {nX : Nat} [FlatRepr X K nX] [Div X] [Div K] : Prop where
  getComp_div (x y : X) (i : Nat) (h : i < nX) :
    getComp (K:=K) (x / y) i h = getComp (K:=K) x i h / getComp (K:=K) y i h

class LawfulSMul (R X K : Type _) {nX : Nat} [FlatRepr X K nX] [SMul R X] [SMul R K] : Prop where
  getComp_smul (a : R) (x : X) (i : Nat) (h : i < nX) :
    getComp (K:=K) (a • x) i h = a • getComp (K:=K) x i h

class LawfulPowNat (X K : Type _) {nX : Nat} [FlatRepr X K nX] [NatPow X] [NatPow K] : Prop where
  getComp_pow_nat (x : X) (m : Nat) (i : Nat) (h : i < nX) :
    getComp (K:=K) (x ^ m) i h = getComp (K:=K) x i h ^ m

class LawfulPowInt (X K : Type _) {nX : Nat} [FlatRepr X K nX] [Pow X Int] [Pow K Int] : Prop where
  getComp_pow_int (x : X) (m : Int) (i : Nat) (h : i < nX) :
    getComp (K:=K) (x ^ m) i h = getComp (K:=K) x i h ^ m

class LawfulStar (X K : Type _) {nX : Nat} [FlatRepr X K nX] [Star X] [Star K] : Prop where
  getComp_star (x : X) (i : Nat) (h : i < nX) :
    getComp (K:=K) (star x) i h = star (getComp (K:=K) x i h)

end FlatRepr

section BasicInstances

namespace FlatRepr

instance {X : Type _} [Zero X] : LawfulZero X X where
  getComp_zero := by intros; rfl

instance {X : Type _} [One X] : LawfulOne X X where
  getComp_one := by intros; rfl

instance {X : Type _} (m : Nat) [OfNat X m] : LawfulOfNat X X m where
  getComp_ofNat := by intros; rfl

instance {X : Type _} [Neg X] : LawfulNeg X X where
  getComp_neg := by intros; rfl

instance {X : Type _} [Add X] : LawfulAdd X X where
  getComp_add := by intros; rfl

instance {X : Type _} [Sub X] : LawfulSub X X where
  getComp_sub := by intros; rfl

instance {X : Type _} [Mul X] : LawfulMul X X where
  getComp_mul := by intros; rfl

instance {X : Type _} [Inv X] : LawfulInv X X where
  getComp_inv := by intros; rfl

instance {X : Type _} [Div X] : LawfulDiv X X where
  getComp_div := by intros; rfl

instance {X R : Type _} [SMul R X] : LawfulSMul R X X where
  getComp_smul := by intros; rfl

instance {X : Type _} [NatPow X] : LawfulPowNat X X where
  getComp_pow_nat := by intros; rfl

instance {X : Type _} [Pow X Int] : LawfulPowInt X X where
  getComp_pow_int := by intros; rfl

instance {X : Type _} [Star X] : LawfulStar X X where
  getComp_star := by intros; rfl

end FlatRepr

end BasicInstances

end NumLean
