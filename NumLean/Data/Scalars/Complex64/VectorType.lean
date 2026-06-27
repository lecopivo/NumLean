import NumLean.Data.Scalars.Complex64.Complex64Vector
import NumLean.Interfaces.VectorType.Basic

namespace NumLean

instance : VectorType Complex64Vector Complex64 where
  toVector xs := xs.data
  fromVector xs := ⟨xs⟩
  left_inv _ := rfl
  right_inv _ := rfl
  emptyWithCapacity c := Complex64Vector.emptyWithCapacity c
  -- uget xs i h := xs.data[i.toNat]'h
  -- uget_spec _ _ _ := rfl
  get xs i h := xs.data[i]'h
  get_spec _ _ _ := rfl
  -- uset xs i x h := ⟨xs.data.set i.toNat x h⟩
  -- uset_spec _ _ _ _ := rfl
  set xs i x h := ⟨xs.data.set i x h⟩
  set_spec _ _ _ _ := rfl
  pop xs := ⟨xs.data.pop⟩
  pop_spec _ := rfl
  replicate n x := Complex64Vector.replicate n x
  replicate_spec _ _ := rfl
  swap xs i j hi hj := ⟨((xs.data.set i (xs.data[j]'hj) hi).set j (xs.data[i]'hi) hj)⟩
  swap_spec _ _ _ _ _ := rfl
  push xs x := ⟨xs.data.push x⟩
  push_spec _ _ := rfl
  append xs ys := ⟨xs.data.append ys.data⟩
  append_spec _ _ := rfl

end NumLean
