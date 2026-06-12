import Batteries.Data.ByteArray
import NumLean.Interfaces.ArrayOps.Basic

namespace NumLean

namespace ArrayOps

instance : ArrayOps ByteArray UInt8 where
  toArray := ByteArray.data
  fromArray := ByteArray.mk
  left_inv := by intro; rfl
  right_inv := by intro; rfl
  size as := as.size
  size_spec as := by simp
  emptyWithCapacity c := ByteArray.emptyWithCapacity c
  emptyWithCapacity_spec := by simp
  uget as i h := as.uget i h
  uget_spec := by intros; rfl
  get as i h := as.get i h
  get_spec := by intros; rfl
  uset as i a h := as.uset i a h
  uset_spec := by intros; simp[ByteArray.uset]
  set as i a h := as.set i a h
  set_spec := by intros; simp[ByteArray.set]
  pop as := ByteArray.mk as.data.pop
  pop_spec := by intros; rfl
  replicate n a := ByteArray.ofFn fun _ : Fin n => a
  replicate_spec := sorry
  swap as i j hi hj := ByteArray.mk ((as.data).swap i j (by simpa using hi) (by simpa using hj))
  swap_spec := by sorry
  push as a := as.push a
  push_spec := by intros; simp
  append as bs := as.append bs
  append_spec := by intros; simp
  copySlice n src srcOff srcInc dst dstOff dstInc :=
    ByteArray.mk (src.data.copySlice n srcOff srcInc dst.data dstOff dstInc)
  copySlice_spec := by intros; simp
  extractSlice n src srcOff srcInc := ByteArray.mk (src.data.extractSlice n srcOff srcInc)
  extractSlice_spec := by intros; simp

end ArrayOps
end NumLean
