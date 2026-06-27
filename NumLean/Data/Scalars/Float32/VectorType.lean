import NumLean.Data.Scalars.Float32.Float32Vector
import NumLean.Interfaces.VectorType.Basic

namespace NumLean

instance : VectorType Float32Vector Float32 where
  toVector := Float32Vector.toVector
  fromVector := Float32Vector.ofVector
  left_inv := Float32Vector.ofVector_toVector
  right_inv := Float32Vector.toVector_ofVector
  emptyWithCapacity := Float32Vector.emptyWithCapacity
  -- uget := Float32Vector.uget
  -- uget_spec := Float32Vector.uget_spec
  get := Float32Vector.get
  get_spec := by
    intro n xs i h
    rw [Float32Vector.get, Float32Vector.getElem_toVector]
  -- uset := Float32Vector.uset
  -- uset_spec := Float32Vector.uset_spec
  set := Float32Vector.set
  set_spec := Float32Vector.set_spec
  pop := Float32Vector.pop
  pop_spec := Float32Vector.pop_spec
  replicate := Float32Vector.replicate
  replicate_spec := Float32Vector.replicate_spec
  swap := Float32Vector.swap
  swap_spec := Float32Vector.swap_spec
  push := Float32Vector.push
  push_spec := Float32Vector.push_spec
  append := Float32Vector.append
  append_spec := Float32Vector.append_spec

end NumLean
