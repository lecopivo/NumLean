module

public import NumLean.Data.Scalars.Float32.Basic
public import NumLean.Data.Scalars.Float32.Float32Array
public import Mathlib.Tactic

@[expose] public section

namespace NumLean

structure Float32Vector (n : Nat) where
  data : Float32Array
  size_eq : data.size = n

namespace Float32Vector

instance {n : Nat} : GetElem (Float32Vector n) Nat Float32 fun _ i => i < n where
  getElem xs i h := xs.data[i]'(by rw [xs.size_eq]; exact h)

theorem getElem_eq_data {n : Nat} (xs : Float32Vector n) (i : Nat) (h : i < n) :
    xs[i]'h = xs.data.get i (by rw [xs.size_eq]; exact h) := by
  rfl

def emptyWithCapacity (c : Nat) : Float32Vector 0 where
  data := Float32Array.emptyWithCapacity c
  size_eq := by simp [Float32Array.emptyWithCapacity, Float32Array.size]

def ofVector {n : Nat} (xs : Vector Float32 n) : Float32Vector n where
  data := Float32Array.mk xs.toArray
  size_eq := by simp [Float32Array.size, Vector.size_toArray]

def toVector {n : Nat} (xs : Float32Vector n) : Vector Float32 n :=
  Vector.mk xs.data.data (by simpa [Float32Array.size] using xs.size_eq)

@[simp]
theorem getElem_toVector {n : Nat} (xs : Float32Vector n) (i : Nat) (h : i < n) :
    (toVector xs)[i]'h = xs[i]'h := by
  rfl

def get {n : Nat} (xs : Float32Vector n) (i : Nat) (h : i < n) : Float32 :=
  xs[i]

def uget {n : Nat} (xs : Float32Vector n) (i : USize) (h : i.toNat < n) : Float32 :=
  xs.data[i]'(by rw [xs.size_eq]; exact h)

def set {n : Nat} (xs : Float32Vector n) (i : Nat) (x : Float32) (h : i < n) :
    Float32Vector n where
  data := xs.data.set i x (by rw [xs.size_eq]; exact h)
  size_eq := by simp [xs.size_eq]

def uset {n : Nat} (xs : Float32Vector n) (i : USize) (x : Float32)
    (h : i.toNat < n) : Float32Vector n :=
  set xs i.toNat x h

def pop {n : Nat} (xs : Float32Vector (n + 1)) : Float32Vector n where
  data := xs.data.pop
  size_eq := by simp [xs.size_eq]

def replicate (n : Nat) (x : Float32) : Float32Vector n where
  data := Float32Array.replicate n x
  size_eq := by simp

def swap {n : Nat} (xs : Float32Vector n) (i j : Nat) (hi : i < n) (hj : j < n) :
    Float32Vector n :=
  let xi := xs[i]
  let xj := xs[j]
  (xs.set i xj hi).set j xi hj

def push {n : Nat} (xs : Float32Vector n) (x : Float32) : Float32Vector (n + 1) where
  data := xs.data.push x
  size_eq := by simp [xs.size_eq]

def append {m n : Nat} (xs : Float32Vector m) (ys : Float32Vector n) :
    Float32Vector (m + n) where
  data := xs.data.append ys.data
  size_eq := by simp [xs.size_eq, ys.size_eq]

@[simp]
theorem getElem_set_eq {n : Nat} (xs : Float32Vector n) (i : Nat) (x : Float32)
    (h : i < n) :
    (set xs i x h)[i]'h = x := by
  change (xs.data.set i x _).get i _ = x
  simp

@[simp]
theorem getElem_set_ne {n : Nat} (xs : Float32Vector n) {i j : Nat} (x : Float32)
    (hi : i < n) (hj : j < n) (hij : j ≠ i) :
    (set xs i x hi)[j]'hj = xs[j]'hj := by
  change (xs.data.set i x _).get j _ = xs.data.get j _
  exact Float32Array.get_set_ne xs.data x _ _ hij

@[simp]
theorem getElem_replicate (n i : Nat) (x : Float32) (h : i < n) :
    (replicate n x)[i]'h = x := by
  change (Float32Array.replicate n x).get i _ = x
  cases i <;> simp [Float32Array.replicate, Float32Array.get]

@[simp]
theorem getElem_push_lt {n : Nat} (xs : Float32Vector n) (x : Float32) (i : Nat)
    (h : i < n) :
    (push xs x)[i]'(Nat.lt_succ_of_lt h) = xs[i]'h := by
  change (xs.data.push x).get i _ = xs.data.get i _
  exact Float32Array.get_push_lt xs.data x i _

@[simp]
theorem getElem_push_eq {n : Nat} (xs : Float32Vector n) (x : Float32) :
    (push xs x)[n]'(Nat.lt_add_one n) = x := by
  change (xs.data.push x).get n _ = x
  simpa [xs.size_eq] using Float32Array.get_push_eq xs.data x

@[simp]
theorem getElem_append_left {m n : Nat} (xs : Float32Vector m) (ys : Float32Vector n)
    (i : Nat) (h : i < m) :
    (append xs ys)[i]'(Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)) = xs[i]'h := by
  change (xs.data.append ys.data).get i _ = xs.data.get i _
  exact Float32Array.get_append_left xs.data ys.data i _

@[ext]
theorem ext {n : Nat} {xs ys : Float32Vector n} (h : ∀ i : Nat, (hi : i < n) → xs[i] = ys[i]) :
    xs = ys := by
  cases xs with
  | mk xdata xsize =>
  cases ys with
  | mk ydata ysize =>
  cases xdata with
  | mk xarray =>
  cases ydata with
  | mk yarray =>
  simp [Float32Array.size] at xsize ysize
  congr
  apply Array.ext
  · rw [xsize, ysize]
  · intro i hi₁ hi₂
    have hin : i < n := by simpa [xsize] using hi₁
    specialize h i hin
    simpa [Float32Array.get] using h

@[simp]
theorem toVector_ofVector {n : Nat} (xs : Vector Float32 n) :
    toVector (ofVector xs) = xs := by
  cases xs
  rfl

@[simp]
theorem ofVector_toVector {n : Nat} (xs : Float32Vector n) :
    ofVector (toVector xs) = xs := by
  cases xs with
  | mk data h =>
  cases data
  simp [ofVector, toVector, Vector.toArray_mk]

theorem uget_spec {n : Nat} (xs : Float32Vector n) (i : USize) (h : i.toNat < n) :
    uget xs i h = (toVector xs)[i.toNat]'h := by
  rfl

theorem set_spec {n : Nat} (xs : Float32Vector n) (i : Nat) (x : Float32) (h : i < n) :
    toVector (set xs i x h) = (toVector xs).set i x h := by
  rfl

theorem uset_spec {n : Nat} (xs : Float32Vector n) (i : USize) (x : Float32)
    (h : i.toNat < n) :
    toVector (uset xs i x h) = (toVector xs).set i.toNat x h := by
  exact set_spec xs i.toNat x h

theorem pop_spec {n : Nat} (xs : Float32Vector (n + 1)) :
    toVector (pop xs) = (toVector xs).pop := by
  rfl

theorem replicate_spec (n : Nat) (x : Float32) :
    toVector (replicate n x) = Vector.replicate n x := by
  rfl

theorem swap_spec {n : Nat} (xs : Float32Vector n) (i j : Nat) (hi : i < n) (hj : j < n) :
    toVector (swap xs i j hi hj) =
      ((toVector xs).set i ((toVector xs)[j]'hj) hi).set j ((toVector xs)[i]'hi) hj := by
  simp [swap, set_spec]

theorem push_spec {n : Nat} (xs : Float32Vector n) (x : Float32) :
    toVector (push xs x) = (toVector xs).push x := by
  rfl

theorem append_spec {m n : Nat} (xs : Float32Vector m) (ys : Float32Vector n) :
    toVector (append xs ys) = (toVector xs).append (toVector ys) := by
  rfl

end Float32Vector

end NumLean
