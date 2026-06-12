import Batteries.Data.FloatArray
import NumLean.Interfaces.ArrayOps.Basic

namespace NumLean

namespace ArrayOps

-- todo: some implementations are still bad

instance : ArrayOps FloatArray Float where
  toArray := FloatArray.data
  fromArray := FloatArray.mk
  left_inv := by intro _; rfl
  right_inv := by intro _; rfl
  size as := as.size
  size_spec as := by intros; rfl
  emptyWithCapacity c := FloatArray.emptyWithCapacity c
  emptyWithCapacity_spec := by intros; rfl
  uget as i h := as.uget i h
  uget_spec := by intros; rfl
  get as i h := as.get i h
  get_spec := by intros; rfl
  uset as i a h := as.uset i a h
  uset_spec := by intros; rfl
  set as i a h := as.set i a h
  set_spec := by intros; rfl
  pop as := FloatArray.mk as.data.pop
  pop_spec := by intros; rfl
  replicate n a := FloatArray.mk (Array.replicate n a)
  replicate_spec := by intros; rfl
  swap as i j hi hj := FloatArray.mk (as.data.swap i j (by simpa using hi) (by simpa using hj))
  swap_spec := by intros; rfl
  push as a := as.push a
  push_spec := by intros; rfl
  append as bs := FloatArray.mk (as.data.append bs.data)
  append_spec := by intros; rfl
  copySlice n src srcOff srcInc dst dstOff dstInc :=
    FloatArray.mk (src.data.copySlice n srcOff srcInc dst.data dstOff dstInc)
  copySlice_spec := by intros; rfl
  extractSlice n src srcOff srcInc := FloatArray.mk (src.data.extractSlice n srcOff srcInc)
  extractSlice_spec := by intros; rfl

end ArrayOps
end NumLean
