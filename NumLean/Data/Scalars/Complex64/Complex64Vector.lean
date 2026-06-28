module

public import NumLean.Data.Scalars.Complex64.Basic

@[expose] public section

namespace NumLean

structure Complex64Vector (n : Nat) where
  data : Vector Complex64 n

namespace Complex64Vector

instance {n : Nat} : GetElem (Complex64Vector n) Nat Complex64 fun _ i => i < n where
  getElem xs i h := xs.data[i]'h

def emptyWithCapacity (c : Nat) : Complex64Vector 0 :=
  ⟨Vector.emptyWithCapacity c⟩

def replicate (n : Nat) (x : Complex64) : Complex64Vector n :=
  ⟨Vector.replicate n x⟩

end Complex64Vector

end NumLean
