import NumLean.Data.Scalars.Float64.Float64Vector
import NumLean.Interfaces.VectorType.Basic

namespace NumLean

namespace Float64Vector

instance : VectorType Float64Vector Float64 where
  toVector xs := ⟨xs.data.1, xs.2⟩
  fromVector xs := ⟨⟨xs.1⟩, xs.2⟩
  left_inv := by
    intro n xs
    cases xs with
    | mk data h =>
    cases data
    rfl
  right_inv := by
    intro n xs
    cases xs with
    | mk data h =>
    cases data
    rfl
  emptyWithCapacity := emptyWithCapacity
  get xs i h := xs[i]
  get_spec := by intros; rfl
  set xs i x h := setElem xs i x h
  set_spec := by
    intro n xs i x h
    cases xs with
    | mk data hdata =>
    cases data
    rfl
  pop := pop
  pop_spec := by
    intro n xs
    cases xs with
    | mk data hdata =>
    cases data
    rfl
  replicate := replicate
  replicate_spec := by intros; rfl
  swap xs i j hi hj := swap xs i j hi hj
  swap_spec := by
    intro n xs i j hi hj
    cases xs with
    | mk data hdata =>
    cases data
    rfl
  push := push
  push_spec := by
    intro n xs x
    cases xs with
    | mk data hdata =>
    cases data
    rfl
  append := append
  append_spec := by
    intro m n xs ys
    cases xs with
    | mk xdata xsize =>
    cases ys with
    | mk ydata ysize =>
    cases xdata
    cases ydata
    rfl

open VectorType

@[simp]
theorem toVector_cast (xs : Float64Vector n) (h : n = m) :
    VectorType.toVector (xs.cast h) = (VectorType.toVector xs).cast h := by
  cases h
  rfl

@[simp]
theorem toVector_append (xs : Float64Vector m) (ys : Float64Vector n) :
    VectorType.toVector (xs.append ys) = (VectorType.toVector xs).append (VectorType.toVector ys) :=
  VectorType.append_spec xs ys

@[simp]
theorem toVector_replicate (n : Nat) (x : Float64) :
    VectorType.toVector (replicate n x) = .replicate n x := by
  rfl

end Float64Vector

end NumLean
