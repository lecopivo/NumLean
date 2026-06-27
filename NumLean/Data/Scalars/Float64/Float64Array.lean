import Batteries.Data.FloatArray

namespace FloatArray

@[extern "numlean_float_array_replicate"]
def replicate (n : @& Nat) (x : Float) : FloatArray where
  data := Array.replicate n x

@[simp]
theorem size_replicate (n : Nat) (x : Float) :
    (replicate n x).size = n := by
  simp [replicate, size]

@[extern "numlean_float_array_pop"]
def pop (xs : FloatArray) : FloatArray where
  data := xs.data.pop

@[simp]
theorem size_pop (xs : FloatArray) :
    xs.pop.size = xs.size - 1 := by
  cases xs
  simp [pop, size]

@[extern "numlean_float_array_append"]
def append (xs ys : FloatArray) : FloatArray where
  data := xs.data ++ ys.data

@[simp]
theorem size_append (xs ys : FloatArray) :
    (xs.append ys).size = xs.size + ys.size := by
  cases xs
  cases ys
  simp [append, size]

end FloatArray
