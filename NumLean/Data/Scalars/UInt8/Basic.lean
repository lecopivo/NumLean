module

public import NumLean.Interfaces.Algebra.Ring.Basic

@[expose] public section

namespace NumLean

instance : NatCast UInt8 where
  natCast n := UInt8.ofNat n

instance : OfNat UInt8 n where
  ofNat := UInt8.ofNat n

instance : Interfaces.Algebra.SemiringOps UInt8 where
  nsmul n x := UInt8.ofNat (n * x.toNat)
  npow n x := UInt8.ofNat (x.toNat ^ n)

end NumLean
