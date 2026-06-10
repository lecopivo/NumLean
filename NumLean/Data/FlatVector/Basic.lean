import NumLean.Data.FlatArray.Basic
import NumLean.Interfaces.IndexType

namespace NumLean

structure FlatVector (X : Type u) (I : Type v)
    {Ks K nX nI} [ArrayType Ks K] [HasDefaultFlatArray X Ks nX] [IndexType I nI] where
  toFlatArray : FlatArray X
  size_toFlatArray : toFlatArray.size = nI

end NumLean
