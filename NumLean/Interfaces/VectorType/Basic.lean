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

variable {As : Nat → Type u} {A : Type w} [VectorType As A]

@[simp]
theorem toVector_fromVector {n} (as : Vector A n) :
    toVector (fromVector (As:=As) as) = as :=
  right_inv as

@[simp]
theorem fromVector_toVector {n} (as : As n) : fromVector (toVector as) = as :=
  left_inv as

attribute [simp]
  uset_spec
  set_spec
  pop_spec
  replicate_spec
  swap_spec
  push_spec
  append_spec

theorem toVector_injective : (toVector : As n → Vector A n).Injective := by
  intro xs ys h
  rw [← fromVector_toVector xs, h, fromVector_toVector ys]

theorem fromVector_injective : (fromVector (As := As) : Vector A n → As n).Injective := by
  intro xs ys h
  have h' := congrArg (toVector (As := As)) h
  simpa using h'

theorem toVector_surjective : (toVector : As n → Vector A n).Surjective := by
  intro xs
  exact ⟨fromVector (As := As) xs, toVector_fromVector xs⟩

theorem fromVector_surjective : (fromVector (As := As) : Vector A n → As n).Surjective := by
  intro xs
  exact ⟨toVector xs, fromVector_toVector xs⟩

theorem eq_fromVector_toVector {n} (xs : As n) : xs = fromVector (toVector xs) := by
  rw [fromVector_toVector]

theorem toVector_eq_iff {n} {xs ys : As n} : toVector xs = toVector ys ↔ xs = ys :=
  toVector_injective.eq_iff

theorem fromVector_eq_iff {n} {xs ys : Vector A n} :
    fromVector (As := As) xs = fromVector (As := As) ys ↔ xs = ys :=
  fromVector_injective.eq_iff

def induction_on {n} {motive : As n → Sort v} (xs : As n)
    (h : ∀ xs' : Vector A n, motive (fromVector (As := As) xs')) : motive xs := by
  rw [eq_fromVector_toVector xs]
  exact h (toVector xs)

theorem ext {n} (xs ys : As n) : (∀ i, (h : i < n) → get xs i h = get ys i h) → xs = ys := by
  intro h
  apply toVector_injective
  ext i hi
  rw [← get_spec xs i hi, ← get_spec ys i hi]
  exact h i hi

theorem uget_eq_getElem {n} (as : As n) (i : USize) (h : i.toNat < n) :
    uget as i h = (toVector as)[i.toNat]'h :=
  uget_spec as i h

theorem get_eq_getElem {n} (as : As n) (i : Nat) (h : i < n) :
    get as i h = (toVector as)[i]'h :=
  get_spec as i h

@[simp]
theorem get_replicate (a : A) (i : Nat) (hi : i < n) :
    get (replicate (As := As) n a) i hi = a := by
  rw [get_eq_getElem, replicate_spec]
  exact Vector.getElem_replicate hi

@[simp]
theorem get_set_eq {n} (as : As n) (i : Nat) (a : A) (hi : i < n) :
    get (set as i a hi) i hi = a := by
  rw [get_eq_getElem, set_spec]
  exact Vector.getElem_set_self hi

@[simp]
theorem get_set_ne {n} (as : As n) {i j : Nat} (a : A) (hi : i < n) (hj : j < n)
    (hij : i ≠ j) : get (set as i a hi) j hj = get as j hj := by
  rw [get_eq_getElem, set_spec, get_eq_getElem]
  rw [Vector.getElem_set]
  simp [hij]

@[simp]
theorem uget_uset_eq {n} (as : As n) (i : USize) (a : A) (hi : i.toNat < n) :
    uget (uset as i a hi) i hi = a := by
  rw [uget_eq_getElem, uset_spec]
  exact Vector.getElem_set_self hi

@[simp]
theorem uget_uset_ne {n} (as : As n) {i j : USize} (a : A)
    (hi : i.toNat < n) (hj : j.toNat < n) (hij : i.toNat ≠ j.toNat) :
    uget (uset as i a hi) j hj = uget as j hj := by
  rw [uget_eq_getElem, uset_spec, uget_eq_getElem]
  rw [Vector.getElem_set]
  simp [hij]

@[simp]
theorem get_pop {n} (as : As (n + 1)) (i : Nat) (hi : i < n) :
    get (pop as) i hi = get as i (Nat.lt_succ_of_lt hi) := by
  rw [get_eq_getElem, pop_spec, get_eq_getElem]
  exact Vector.getElem_pop (by simpa using hi)

@[simp]
theorem get_push_lt {n} (as : As n) (a : A) (i : Nat) (hi : i < n) :
    get (push as a) i (Nat.lt_succ_of_lt hi) = get as i hi := by
  rw [get_eq_getElem, push_spec, get_eq_getElem]
  exact Vector.getElem_push_lt hi

@[simp]
theorem get_push_eq {n} (as : As n) (a : A) :
    get (push as a) n (Nat.lt_add_one n) = a := by
  rw [get_eq_getElem, push_spec]
  exact Vector.getElem_push_eq

@[simp]
theorem get_append_left {m n} (as : As m) (bs : As n) (i : Nat) (hi : i < m) :
    get (append as bs) i (Nat.lt_of_lt_of_le hi (Nat.le_add_right m n)) = get as i hi := by
  rw [get_eq_getElem, append_spec, get_eq_getElem]
  exact Vector.getElem_append_left hi

@[simp]
theorem get_append_right {m n} (as : As m) (bs : As n) (i : Nat) (hi : i < m + n) (hm : m ≤ i) :
    get (append as bs) i hi = get bs (i - m) (Nat.sub_lt_left_of_lt_add hm hi) := by
  rw [get_eq_getElem, append_spec, get_eq_getElem]
  exact Vector.getElem_append_right hi hm

@[simp]
theorem get_swap_left {n} (as : As n) {i j : Nat} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) : get (swap as i j hi hj) i hi = get as j hj := by
  rw [get_eq_getElem, swap_spec, get_eq_getElem]
  rw [Vector.getElem_set, Vector.getElem_set_self]
  simp [hij.symm]

@[simp]
theorem get_swap_right {n} (as : As n) {i j : Nat} (hi : i < n) (hj : j < n)
    : get (swap as i j hi hj) j hj = get as i hi := by
  rw [get_eq_getElem, swap_spec, get_eq_getElem]
  rw [Vector.getElem_set_self]

@[simp]
theorem get_swap_of_ne {n} (as : As n) {i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n)
    (hki : k ≠ i) (hkj : k ≠ j) : get (swap as i j hi hj) k hk = get as k hk := by
  rw [get_eq_getElem, swap_spec, get_eq_getElem]
  rw [Vector.getElem_set, Vector.getElem_set]
  simp [hki.symm, hkj.symm]

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
