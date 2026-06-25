import NumLean.Algebra.Ops
import NumLean.Experimental.Interfaces.Interval.Basic

namespace NumLean

namespace Interval

variable (I : Type u) (R : outParam (Type v)) [IntervalType I R]

class LawfulTop [Top I] : Prop where
  mem_top : ∀ x : R, x ∈ (⊤ : I)

class LawfulZero [Zero I] [Zero R] : Prop where
  zero_mem_interval : (0 : R) ∈ (0 : I)

class LawfulOne [One I] [One R] : Prop where
  one_mem_interval : (1 : R) ∈ (1 : I)

class LawfulNeg [Neg I] [Neg R] : Prop where
  neg_mem_interval : ∀ {x : R} {i : I}, x ∈ i → -x ∈ (-i)

class LawfulAdd [Add I] [Add R] : Prop where
  add_mem_interval : ∀ {x y : R} {i j : I},
    x ∈ i → y ∈ j → x + y ∈ (i + j)

class LawfulSub [Sub I] [Sub R] : Prop where
  sub_mem_interval : ∀ {x y : R} {i j : I},
    x ∈ i → y ∈ j → x - y ∈ (i - j)

class LawfulMul [Mul I] [Mul R] : Prop where
  mul_mem_interval : ∀ {x y : R} {i j : I},
    x ∈ i → y ∈ j → x * y ∈ (i * j)

class LawfulNatPow [NatPow I] [NatPow R] : Prop where
  natPow_mem_interval : ∀ {x : R} {i : I}, x ∈ i → ∀ n : Nat, x ^ n ∈ (i ^ n)

/-- Inversion is total at the interface level. Concrete interval types may return `⊤`
when the input interval contains zero. -/
class LawfulInv [Inv I] [Inv R] : Prop where
  inv_mem_interval : ∀ {x : R} {i : I}, x ∈ i → x⁻¹ ∈ i⁻¹

class LawfulDiv [Div I] [Div R] : Prop where
  div_mem_interval : ∀ {x y : R} {i j : I},
    x ∈ i → y ∈ j → x / y ∈ (i / j)

class LawfulAddGroupOps [AddGroupOps I] [AddGroupOps R] : Prop extends
  LawfulZero I R, LawfulNeg I R, LawfulAdd I R, LawfulSub I R

class LawfulGroupOps [GroupOps I] [GroupOps R] : Prop extends
  LawfulOne I R, LawfulMul I R, LawfulInv I R, LawfulDiv I R

class LawfulFieldOps [FieldOps I] [FieldOps R] : Prop extends
  LawfulAddGroupOps I R, LawfulGroupOps I R

attribute [grind .] LawfulTop.mem_top LawfulZero.zero_mem_interval LawfulOne.one_mem_interval
attribute [grind ←] LawfulNeg.neg_mem_interval LawfulAdd.add_mem_interval LawfulSub.sub_mem_interval
attribute [grind ←] LawfulMul.mul_mem_interval LawfulNatPow.natPow_mem_interval
attribute [grind ←] LawfulInv.inv_mem_interval LawfulDiv.div_mem_interval

end Interval

end NumLean
