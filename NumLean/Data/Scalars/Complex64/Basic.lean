module

public import NumLean.Data.Scalars.Float64.Basic

@[expose] public section

namespace NumLean

@[unbox]
structure Complex64 where
  (re im : Float64)

end NumLean
