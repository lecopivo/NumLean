module

public import NumLean.Data.Scalars.Float32.VectorType
public import NumLean.Interfaces.HasFlatRepr.Basic

@[expose] public section

namespace NumLean

instance : HasDefaultFlatRepr Float32 Float32Vector 1 where

end NumLean
