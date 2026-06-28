module

public import NumLean.Data.Scalars.Float64.TensorAlgebra
public import NumLean.Interfaces.RealModel

@[expose] public section

namespace NumLean

instance : RealModelOps Float64 Float64Vector where
