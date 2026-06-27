import NumLean.Interfaces.Algebra.Field

namespace NumLean

export Interfaces.Algebra (AddMonoidOps LawfulAddMonoidOps MonoidOps LawfulMonoidOps
  AddGroupOps LawfulAddGroupOps GroupOps LawfulGroupOps SemiringOps LawfulSemiringOps RingOps
  LawfulRingOps FieldOps LawfulFieldOps)

class RNorm (K : Type u) (R : outParam (Type v)) where
  rnorm : K → R

end NumLean
