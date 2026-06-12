import NumLean.Interfaces.ArrayOps.Basic

namespace NumLean

namespace ArrayOps

instance {A : Type u} : ArrayOps (Array A) A where
  toArray as := as
  fromArray as := as
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  size as := as.size
  size_spec _ := rfl
  emptyWithCapacity c := Array.mkEmpty c
  emptyWithCapacity_spec _ := rfl
  uget as i h := as.uget i h
  uget_spec _ _ _ := rfl
  get as i h := as[i]'h
  get_spec _ _ _ := rfl
  uset as i a h := as.uset i a h
  uset_spec _ _ _ _ := rfl
  set as i a h := as.set i a h
  set_spec _ _ _ _ := rfl
  pop as := as.pop
  pop_spec _ := rfl
  replicate n a := Array.replicate n a
  replicate_spec _ _ := rfl
  swap as i j hi hj := as.swap i j hi hj
  swap_spec _ _ _ _ _ := rfl
  push as a := as.push a
  push_spec _ _ := rfl
  append as bs := as.append bs
  append_spec _ _ := rfl
  copySlice n src srcOff srcInc dst dstOff dstInc :=
    src.copySlice n srcOff srcInc dst dstOff dstInc
  copySlice_spec _ _ _ _ _ _ _ := rfl
  extractSlice n src srcOff srcInc := src.extractSlice n srcOff srcInc
  extractSlice_spec _ _ _ _ := rfl


end ArrayOps
end NumLean
