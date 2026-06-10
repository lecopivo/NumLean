import NumLean.Interfaces.ArrayType.Array
import NumLean.Interfaces.BlasOps.Basic
import NumLean.Interfaces.BlasOps.ArrayOps
import NumLean.Interfaces.BlasOps.ArrayLemmas

namespace NumLean

instance {K} [Add K] [Mul K] : BLASOps (Array K) K where
  axpby := Array.axpby
  scal := Array.scal

instance {K} [RCLike K] : LawfulBLASOps (Array K) where
  axpby_spec := by intros; rfl
  scal_spec := by intros; rfl

end NumLean
