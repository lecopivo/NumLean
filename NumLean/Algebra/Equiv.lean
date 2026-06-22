import Mathlib.Logic.Equiv.Basic
import NumLean.Algebra.Ops

namespace Zero

@[reducible, inline]
def ofEquiv (e : X ≃ Y) [Zero X] : Zero Y where
  zero := e 0

end Zero

namespace One

@[reducible, inline]
def ofEquiv (e : X ≃ Y) [One X] : One Y where
  one := e 1

end One

namespace Add

@[reducible, inline]
def ofEquiv (e : X ≃ Y) [Add X] : Add Y where
  add y y' := e (e.symm y + e.symm y')

end Add

namespace Sub

@[reducible, inline]
def ofEquiv (e : X ≃ Y) [Sub X] : Sub Y where
  sub y y' := e (e.symm y - e.symm y')

end Sub

namespace Neg

@[reducible, inline]
def ofEquiv (e : X ≃ Y) [Neg X] : Neg Y where
  neg y := e (-e.symm y)

end Neg

namespace Mul

@[reducible, inline]
def ofEquiv (e : X ≃ Y) [Mul X] : Mul Y where
  mul y y' := e (e.symm y * e.symm y')

end Mul

namespace Div

@[reducible, inline]
def ofEquiv (e : X ≃ Y) [Div X] : Div Y where
  div y y' := e (e.symm y / e.symm y')

end Div

namespace Inv

@[reducible, inline]
def ofEquiv (e : X ≃ Y) [Inv X] : Inv Y where
  inv y := e (e.symm y)⁻¹

end Inv

namespace Star

@[reducible, inline]
def ofEquiv (e : X ≃ Y) [Star X] : Star Y where
  star y := e (star (e.symm y))

end Star

namespace NumLean

namespace AddGroupOps

@[reducible, inline]
def ofEquiv (e : X ≃ Y) [AddGroupOps X] [Add Y] [Sub Y] [Neg Y] [Zero Y] :
    AddGroupOps Y where
  nsmul n y := e (n • e.symm y)
  zsmul n y := e (n • e.symm y)

end AddGroupOps

namespace GroupOps

@[reducible, inline]
def ofEquiv (e : X ≃ Y) [GroupOps X] [Mul Y] [Div Y] [Inv Y] [One Y] : GroupOps Y where
  npow n y := e (e.symm y ^ n)
  zpow n y := e (e.symm y ^ n)

end GroupOps

end NumLean
