module

public import NumLean.Data.Scalars.UInt8.Basic

@[expose] public section

namespace NumLean

example : Interfaces.Algebra.SemiringOps UInt8 := inferInstance

end NumLean
