import NumLean.Data.Scalars.Complex32.Complex32Vector
import NumLean.Interfaces.VectorType.Basic

namespace NumLean

-- instance : VectorType Complex32Vector Complex32 where
--   toVector := Complex32Vector.toVector
--   fromVector := Complex32Vector.ofVector
--   left_inv := Complex32Vector.ofVector_toVector
--   right_inv := Complex32Vector.toVector_ofVector
--   emptyWithCapacity := Complex32Vector.emptyWithCapacity
--   uget := Complex32Vector.uget
--   uget_spec := Complex32Vector.uget_spec
--   get := Complex32Vector.get
--   get_spec := by
--     intro n xs i h
--     simp [Complex32Vector.get, Complex32Vector.toVector]
--   uset := Complex32Vector.uset
--   uset_spec := Complex32Vector.uset_spec
--   set := Complex32Vector.set
--   set_spec := Complex32Vector.set_spec
--   pop := Complex32Vector.pop
--   pop_spec := Complex32Vector.pop_spec
--   replicate := Complex32Vector.replicate
--   replicate_spec := Complex32Vector.replicate_spec
--   swap := Complex32Vector.swap
--   swap_spec := Complex32Vector.swap_spec
--   push := Complex32Vector.push
--   push_spec := Complex32Vector.push_spec
--   append := Complex32Vector.append
--   append_spec := Complex32Vector.append_spec

end NumLean
