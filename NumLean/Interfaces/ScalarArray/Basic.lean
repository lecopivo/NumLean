import NumLean.Interfaces.IndexType
import NumLean.Interfaces.ArrayType.Basic
import NumLean.Interfaces.ArrayType.Array
import NumLean.Interfaces.ArrayType.FloatArray
import NumLean.Interfaces.BlasOps.Basic
import NumLean.Interfaces.BlasOps.Array
import NumLean.Interfaces.BlasOps.FloatArray

namespace NumLean


/-- A scalar storage type with a BLAS level-one style API. The `set`/`get` laws are structural
coherency laws of the storage representation; mathematical operation laws live in
`LawfulScalarArray`. -/
class ScalarArray (Ks : Type u) (K : outParam (Type v))
  extends
    ArrayType Ks K,
    BLASOps Ks K

class LawfulScalarArray (Ks : Type u) {K : outParam (Type v)}
  [RCLike K] [ScalarArray Ks K]
  extends
    LawfulBLASOps Ks


instance [Add K] [Mul K] : ScalarArray (Array K) K where
instance [RCLike K] : LawfulScalarArray (Array K) where
instance : ScalarArray FloatArray Float where

end NumLean
