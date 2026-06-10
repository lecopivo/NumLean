import NumLean.Data.FloatP
import NumLean.Data.Float32Array

namespace NumLean

@[unbox]
structure Complex32 where
  (re im : Float32)

@[unbox]
structure Complex64 where
  (re im : Float)

def ComplexP (p : Float.Precision) : Type :=
  match p with
  | .single => Complex32
  | .double => Complex64

-- todo: create basic API
structure Complex32Array where
  data : Float32Array
  h_size : data.size % 2 == 0

-- todo: create basic API
structure Complex64Array where
  data : Float32Array
  h_size : data.size % 2 == 0
