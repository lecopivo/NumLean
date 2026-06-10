import Batteries.Data.Array.Lemmas
import NumLean.Data.Array

namespace NumLean

open Function

class ArrayType (As : Type u) (A : outParam (Type w)) where

  toArray (as : As) : Array A
  fromArray (as : Array A) : As

  left_inv  : LeftInverse fromArray toArray
  right_inv : RightInverse fromArray toArray

  size (as : As) : Nat
  size_spec (as : As) : size as = (toArray as).size

  emptyWithCapacity (c : Nat) : As
  emptyWithCapacity_spec (c : Nat) :
    toArray (emptyWithCapacity c) = Array.mkEmpty c

  uget (as : As) (i : USize) (h : i.toNat < size as) : A
  uget_spec (as : As) (i : USize) (h : i.toNat < size as) :
    uget as i h = (toArray as).uget i (size_spec as ▸ h)

  get (as : As) (i : Nat) (h : i < size as) : A
  get_spec (as : As) (i : Nat) (h : i < size as) :
    get as i h = (toArray as)[i]'(size_spec as ▸ h)

  uset (as : As) (i : USize) (a : A) (h : i.toNat < size as) : As
  uset_spec (as : As) (i : USize) (a : A) (h : i.toNat < size as) :
    toArray (uset as i a h) = (toArray as).uset i a (size_spec as ▸ h)

  set (as : As) (i : Nat) (a : A) (h : i < size as) : As
  set_spec (as : As) (i : Nat) (a : A) (h : i < size as) :
    toArray (set as i a h) = (toArray as).set i a (size_spec as ▸ h)

  pop (as : As) : As
  pop_spec (as : As) : toArray (pop as) = (toArray as).pop

  replicate (n : Nat) (a : A) : As
  replicate_spec (n : Nat) (a : A) :
    toArray (replicate n a) = Array.replicate n a

  swap (as : As) (i j : Nat) (hi : i < size as) (hj : j < size as) : As
  swap_spec (as : As) (i j : Nat) (hi : i < size as) (hj : j < size as) :
    toArray (swap as i j hi hj) =
      (toArray as).swap i j (size_spec as ▸ hi) (size_spec as ▸ hj)

  push (as : As) (a : A) : As
  push_spec (as : As) (a : A) :
    toArray (push as a) = (toArray as).push a

  append (as bs : As) : As
  append_spec (as bs : As) :
    toArray (append as bs) = (toArray as).append (toArray bs)

  copySlice (n : Nat) (src : As) (srcOff srcInc : Nat) (dst : As) (dstOff dstInc : Nat) : As
  copySlice_spec (n : Nat) (src : As) (srcOff srcInc : Nat) (dst : As) (dstOff dstInc : Nat) :
    toArray (copySlice n src srcOff srcInc dst dstOff dstInc) =
      (toArray src).copySlice n srcOff srcInc (toArray dst) dstOff dstInc

  extractSlice (n : Nat) (src : As) (srcOff srcInc : Nat) : As
  extractSlice_spec (n : Nat) (src : As) (srcOff srcInc : Nat) :
    toArray (extractSlice n src srcOff srcInc) =
      (toArray src).extractSlice n srcOff srcInc

namespace ArrayType

variable {As : Type u} {A : Type w} [ArrayType As A]

@[simp]
theorem toArray_fromArray (as : Array A) : toArray (fromArray (As:=As) as) = as :=
  ArrayType.right_inv as

@[simp]
theorem fromArray_toArray (as : As) : fromArray (toArray as) = as :=
  ArrayType.left_inv as

end ArrayType

end NumLean
