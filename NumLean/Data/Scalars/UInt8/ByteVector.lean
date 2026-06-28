module

public import NumLean.Data.Scalars.UInt8.Basic

@[expose] public section

namespace NumLean

structure ByteVector (n : Nat) where
  data : ByteArray
  size_data : data.size = n

namespace ByteVector

instance {n : Nat} : GetElem (ByteVector n) Nat UInt8 fun _ i => i < n where
  getElem xs i h := xs.data[i]'(by rw[xs.2]; exact h)


end ByteVector

end NumLean
