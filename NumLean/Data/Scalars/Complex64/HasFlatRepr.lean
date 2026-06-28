module

public import NumLean.Data.Scalars.Complex64.VectorType
public import NumLean.Data.Scalars.Float64.VectorType
public import NumLean.Data.Scalars.UInt8.VectorType
public import NumLean.Interfaces.HasFlatRepr.Basic

@[expose] public section

namespace NumLean

instance : HasDefaultFlatRepr Complex64 Complex64Vector 1 where

-- instance instHasFlatReprFloatComplex64Vector : HasFlatRepr Float Complex64Vector 2
-- instance instHasFlatReprComplex64FloatVector : HasFlatRepr Complex64 FloatVector 2
-- instance instHasFlatReprComplex64ByteVector : HasFlatRepr Complex64 ByteVector 16

end NumLean
