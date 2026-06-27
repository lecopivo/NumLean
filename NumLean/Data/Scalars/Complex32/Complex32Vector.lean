import NumLean.Data.Scalars.Complex32.Basic
import NumLean.Data.Scalars.Float32.Float32Array
import Mathlib.Tactic

namespace NumLean

structure Complex32Vector (n : Nat) where
  data : Float32Array
  size_eq : data.size = 2 * n

namespace Complex32Vector

instance {n : Nat} : GetElem (Complex32Vector n) Nat Complex32 fun _ i => i < n where
  getElem xs i h :=
    { re := xs.data[2 * i]'(by rw [xs.size_eq]; omega)
      im := xs.data[2 * i + 1]'(by rw [xs.size_eq]; omega) }

def emptyWithCapacity (c : Nat) : Complex32Vector 0 where
  data := Float32Array.emptyWithCapacity (2 * c)
  size_eq := by simp [Float32Array.emptyWithCapacity, Float32Array.size]

def ofVector {n : Nat} (xs : Vector Complex32 n) : Complex32Vector n where
  data := Float32Array.mk <| Array.ofFn fun i : Fin (2 * n) =>
    if i.val % 2 = 0 then
      (xs[i.val / 2]'(by omega)).re
    else
      (xs[i.val / 2]'(by omega)).im
  size_eq := by
    simp [Float32Array.size]

def toVector {n : Nat} (xs : Complex32Vector n) : Vector Complex32 n :=
  Vector.ofFn fun i => xs[i]

@[simp]
theorem ofVector_get_re {n : Nat} (xs : Vector Complex32 n) (i : Nat)
    (h : 2 * i < (ofVector xs).data.size) :
    (ofVector xs).data[2 * i]'h =
      (xs[i]'(by rw [show (ofVector xs).data.size = 2 * n from (ofVector xs).size_eq] at h; omega)).re := by
  change (Array.ofFn (fun j : Fin (2 * n) =>
      if j.val % 2 = 0 then (xs[j.val / 2]'(by omega)).re else (xs[j.val / 2]'(by omega)).im))[2 * i] = _
  rw [Array.getElem_ofFn]
  simp

@[simp]
theorem ofVector_get_im {n : Nat} (xs : Vector Complex32 n) (i : Nat)
    (h : 2 * i + 1 < (ofVector xs).data.size) :
    (ofVector xs).data[2 * i + 1]'h =
      (xs[i]'(by rw [show (ofVector xs).data.size = 2 * n from (ofVector xs).size_eq] at h; omega)).im := by
  have hodd : (2 * i + 1) % 2 ≠ 0 := by omega
  change (Array.ofFn (fun j : Fin (2 * n) =>
      if j.val % 2 = 0 then (xs[j.val / 2]'(by omega)).re else (xs[j.val / 2]'(by omega)).im))[2 * i + 1] = _
  rw [Array.getElem_ofFn]
  have hdiv : (2 * i + 1) / 2 = i := by omega
  simp [hdiv]

def get {n : Nat} (xs : Complex32Vector n) (i : Nat) (h : i < n) : Complex32 :=
  xs[i]

def uget {n : Nat} (xs : Complex32Vector n) (i : USize) (h : i.toNat < n) : Complex32 :=
  { re := xs.data[2 * i.toNat]'(by rw [xs.size_eq]; omega)
    im := xs.data[2 * i.toNat + 1]'(by rw [xs.size_eq]; omega) }

def set {n : Nat} (xs : Complex32Vector n) (i : Nat) (x : Complex32) (h : i < n) :
    Complex32Vector n :=
  let data := xs.data.set (2 * i) x.re (by rw [xs.size_eq]; omega)
  { data := data.set (2 * i + 1) x.im (by simp [data, xs.size_eq]; omega)
    size_eq := by simp [data, xs.size_eq] }

def uset {n : Nat} (xs : Complex32Vector n) (i : USize) (x : Complex32)
    (h : i.toNat < n) : Complex32Vector n :=
  set xs i.toNat x h

def pop {n : Nat} (xs : Complex32Vector (n + 1)) : Complex32Vector n :=
  { data := xs.data.pop.pop
    size_eq := by simp [xs.size_eq]; omega }


def replicate (n : Nat) (x : Complex32) : Complex32Vector n :=
  { data := Float32Array.replicate2 n x.re x.im
    size_eq := by simp }

def swap {n : Nat} (xs : Complex32Vector n) (i j : Nat) (hi : i < n) (hj : j < n) :
    Complex32Vector n :=
  let xi := xs[i]
  let xj := xs[j]
  (xs.set i xj hi).set j xi hj

def push {n : Nat} (xs : Complex32Vector n) (x : Complex32) : Complex32Vector (n + 1) :=
  { data := (xs.data.push x.re).push x.im
    size_eq := by simp [xs.size_eq]; omega }

def append {m n : Nat} (xs : Complex32Vector m) (ys : Complex32Vector n) :
    Complex32Vector (m + n) :=
  { data := xs.data.append ys.data
    size_eq := by simp [xs.size_eq, ys.size_eq]; omega }

@[ext]
axiom ext {n : Nat} {xs ys : Complex32Vector n} (h : ∀ i : Nat, (h : i < n) → xs[i] = ys[i]) :
    xs = ys

-- use extensionality
@[simp]
theorem toVector_ofVector {n : Nat} (xs : Vector Complex32 n) :
    toVector (ofVector xs) = xs := by
  ext i
  · simp only [toVector, Vector.getElem_ofFn]
    change (ofVector xs).data[2 * i]'_ = (xs[i]).re
    exact ofVector_get_re xs i _
  · simp only [toVector, Vector.getElem_ofFn]
    change (ofVector xs).data[2 * i + 1]'_ = (xs[i]).im
    exact ofVector_get_im xs i _

@[simp]
axiom ofVector_toVector {n : Nat} (xs : Complex32Vector n) :
    ofVector (toVector xs) = xs

theorem uget_spec {n : Nat} (xs : Complex32Vector n) (i : USize) (h : i.toNat < n) :
    uget xs i h = (toVector xs)[i.toNat]'h := by
  ext <;> simp [uget, toVector] <;> rfl

end Complex32Vector

end NumLean
