import NumLean.Algebra.Ops
import NumLean.Data.Sigma

namespace NumLean

namespace Unit

instance instZero : Zero Unit where
  zero := ()

instance instOne : One Unit where
  one := ()

instance instAdd : Add Unit where
  add _ _ := ()

instance instSub : Sub Unit where
  sub _ _ := ()

instance instNeg : Neg Unit where
  neg _ := ()

instance instMul : Mul Unit where
  mul _ _ := ()

instance instDiv : Div Unit where
  div _ _ := ()

instance instInv : Inv Unit where
  inv _ := ()

instance instNatPow : NatPow Unit where
  pow _ _ := ()

instance instPowInt : Pow Unit Int where
  pow _ _ := ()

instance instSMulNat : SMul Nat Unit where
  smul _ _ := ()

instance instSMulInt : SMul Int Unit where
  smul _ _ := ()

end Unit

namespace Sigma

@[simp]
theorem mk_zero_mk {X Y : Type _} [Zero X] [Zero Y] :
    (0 : ((_ : X) × Y)) = ⟨0, 0⟩ := rfl

@[simp]
theorem mk_one_mk {X Y : Type _} [One X] [One Y] :
    (1 : ((_ : X) × Y)) = ⟨1, 1⟩ := rfl

@[simp]
theorem mk_add_mk {X Y : Type _} [Add X] [Add Y] (x x' : X) (y y' : Y) :
    (⟨x, y⟩ : ((_ : X) × Y)) + ⟨x', y'⟩ = ⟨x + x', y + y'⟩ := rfl

@[simp]
theorem mk_sub_mk {X Y : Type _} [Sub X] [Sub Y] (x x' : X) (y y' : Y) :
    (⟨x, y⟩ : ((_ : X) × Y)) - ⟨x', y'⟩ = ⟨x - x', y - y'⟩ := rfl

@[simp]
theorem neg_mk {X Y : Type _} [Neg X] [Neg Y] (x : X) (y : Y) :
    -(⟨x, y⟩ : ((_ : X) × Y)) = ⟨-x, -y⟩ := rfl

@[simp]
theorem mk_mul_mk {X Y : Type _} [Mul X] [Mul Y] (x x' : X) (y y' : Y) :
    (⟨x, y⟩ : ((_ : X) × Y)) * ⟨x', y'⟩ = ⟨x * x', y * y'⟩ := rfl

@[simp]
theorem mk_div_mk {X Y : Type _} [Div X] [Div Y] (x x' : X) (y y' : Y) :
    (⟨x, y⟩ : ((_ : X) × Y)) / ⟨x', y'⟩ = ⟨x / x', y / y'⟩ := rfl

@[simp]
theorem inv_mk {X Y : Type _} [Inv X] [Inv Y] (x : X) (y : Y) :
    (⟨x, y⟩ : ((_ : X) × Y))⁻¹ = ⟨x⁻¹, y⁻¹⟩ := rfl

@[simp]
theorem nat_smul_mk {X Y : Type _} [SMul Nat X] [SMul Nat Y]
    (n : Nat) (x : X) (y : Y) :
    n • (⟨x, y⟩ : ((_ : X) × Y)) = ⟨n • x, n • y⟩ := rfl

@[simp]
theorem int_smul_mk {X Y : Type _} [SMul Int X] [SMul Int Y]
    (n : Int) (x : X) (y : Y) :
    n • (⟨x, y⟩ : ((_ : X) × Y)) = ⟨n • x, n • y⟩ := rfl

@[simp]
theorem mk_npow {X Y : Type _} [NatPow X] [NatPow Y] (x : X) (y : Y) (n : Nat) :
    (⟨x, y⟩ : ((_ : X) × Y)) ^ n = ⟨x ^ n, y ^ n⟩ := rfl

@[simp]
theorem mk_zpow {X Y : Type _} [Pow X Int] [Pow Y Int] (x : X) (y : Y) (n : Int) :
    (⟨x, y⟩ : ((_ : X) × Y)) ^ n = ⟨x ^ n, y ^ n⟩ := rfl

end Sigma

instance : AddGroupOps Unit where
  nsmul _ _ := ()
  zsmul _ _ := ()

instance : GroupOps Unit where
  npow _ _ := ()
  zpow _ _ := ()

instance {X Y : Type _} [AddGroupOps X] [AddGroupOps Y] :
    AddGroupOps ((_ : X) × Y) where
  nsmul n xy := n • xy
  zsmul n xy := n • xy

instance {X Y : Type _} [GroupOps X] [GroupOps Y] :
    GroupOps ((_ : X) × Y) where
  npow n xy := xy ^ n
  zpow n xy := xy ^ n

end NumLean
