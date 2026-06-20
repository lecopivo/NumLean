import Batteries.Data.Array.Lemmas
import NumLean.Data.Array

namespace NumLean

open Function

class VectorType (As : Nat → Type u) (A : outParam (Type w)) where

  toVector {n} (as : As n) : Vector A n
  fromVector {n} (as : Vector A n) : As n

  left_inv {n} (as : As n) : fromVector (toVector as) = as
  right_inv {n} (as : Vector A n) : toVector (fromVector as) = as

  emptyWithCapacity (c : Nat) : As 0

  uget {n} (as : As n) (i : USize) (h : i.toNat < n) : A
  uget_spec {n} (as : As n) (i : USize) (h : i.toNat < n) :
    uget as i h = (toVector as)[i.toNat]'h

  get {n} (as : As n) (i : Nat) (h : i < n) : A
  get_spec {n} (as : As n) (i : Nat) (h : i < n) :
    get as i h = (toVector as)[i]'h

  uset {n} (as : As n) (i : USize) (a : A) (h : i.toNat < n) : As n
  uset_spec {n} (as : As n) (i : USize) (a : A) (h : i.toNat < n) :
    toVector (uset as i a h) = (toVector as).set i.toNat a h

  set {n} (as : As n) (i : Nat) (a : A) (h : i < n) : As n
  set_spec {n} (as : As n) (i : Nat) (a : A) (h : i < n) :
    toVector (set as i a h) = (toVector as).set i a h

  pop {n} (as : As (n + 1)) : As n
  pop_spec {n} (as : As (n + 1)) :
    toVector (pop as) = (toVector as).pop

  replicate (n : Nat) (a : A) : As n
  replicate_spec (n : Nat) (a : A) :
    toVector (replicate n a) = Vector.replicate n a

  swap {n} (as : As n) (i j : Nat) (hi : i < n) (hj : j < n) : As n
  swap_spec {n} (as : As n) (i j : Nat) (hi : i < n) (hj : j < n) :
    toVector (swap as i j hi hj) =
      ((toVector as).set i ((toVector as)[j]'hj) hi).set j ((toVector as)[i]'hi) hj

  push {n} (as : As n) (a : A) : As (n + 1)
  push_spec {n} (as : As n) (a : A) :
    toVector (push as a) = (toVector as).push a

  append {m n} (as : As m) (bs : As n) : As (m + n)
  append_spec {m n} (as : As m) (bs : As n) :
    toVector (append as bs) = (toVector as).append (toVector bs)

namespace VectorType

variable {As : Nat → Type u} {A : Type w} [_root_.NumLean.VectorType As A]

@[simp]
theorem toVector_fromVector {n} (as : Vector A n) :
    toVector (fromVector (As:=As) as) = as :=
  _root_.NumLean.VectorType.right_inv as

@[simp]
theorem fromVector_toVector {n} (as : As n) : fromVector (toVector as) = as :=
  _root_.NumLean.VectorType.left_inv as

end VectorType

instance {A : Type u} : VectorType (Vector A) A where
  toVector as := as
  fromVector as := as
  left_inv _ := rfl
  right_inv _ := rfl
  emptyWithCapacity c := .emptyWithCapacity c
  uget as i h := as[i.toNat]'h
  uget_spec _ _ _ := rfl
  get as i h := as[i]'h
  get_spec _ _ _ := rfl
  uset as i a h := as.set i.toNat a h
  uset_spec _ _ _ _ := rfl
  set as i a h := as.set i a h
  set_spec _ _ _ _ := rfl
  pop as := as.pop
  pop_spec _ := rfl
  replicate n a := Vector.replicate n a
  replicate_spec _ _ := rfl
  swap as i j hi hj := ((as.set i (as[j]'hj) hi).set j (as[i]'hi) hj)
  swap_spec _ _ _ _ _ := rfl
  push as a := as.push a
  push_spec _ _ := rfl
  append as bs := as.append bs
  append_spec _ _ := rfl

end NumLean
