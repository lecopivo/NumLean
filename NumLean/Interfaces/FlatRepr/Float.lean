import NumLean.Interfaces.FlatRepr

namespace NumLean

instance : DefaultFlatRepr Float Float 1 where

-- todo:
-- this will be usefull for compactifying Float to `ByteArray`
-- instance : FlatRepr Float UInt8 8 where

-- This might be just interesting not useful
-- instance : FlatRepr Float Bool 64 where


end NumLean
