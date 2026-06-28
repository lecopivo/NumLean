module

public import Init.Data.Float
public import Init.Ext
public import Init.Data.Array.DecidableEq

@[expose] public section

namespace NumLean

universe v w

structure Float32Array where
  data : Array Float32

attribute [extern "lean_float32_array_mk"] Float32Array.mk
attribute [extern "lean_float32_array_data"] Float32Array.data

namespace Float32Array

attribute [ext] Float32Array

@[extern "lean_mk_empty_float32_array"]
def emptyWithCapacity (c : @& Nat) : Float32Array :=
  { data := Array.mkEmpty c }

def empty : Float32Array :=
  emptyWithCapacity 0

instance : Inhabited Float32Array where
  default := empty

instance : EmptyCollection Float32Array where
  emptyCollection := Float32Array.empty

@[extern "lean_float32_array_push"]
def push : Float32Array → Float32 → Float32Array
  | ⟨ds⟩, x => ⟨ds.push x⟩

@[extern "lean_float32_array_size", tagged_return]
def size : (@& Float32Array) → Nat
  | ⟨ds⟩ => ds.size

@[simp]
theorem size_push (xs : Float32Array) (x : Float32) :
    (xs.push x).size = xs.size + 1 := by
  cases xs
  simp [push, size]

@[simp]
def usize (a : @& Float32Array) : USize :=
  a.size.toUSize

@[extern "lean_float32_array_uget"]
def uget : (a : @& Float32Array) → (i : USize) → i.toNat < a.size → Float32
  | ⟨ds⟩, i, h => ds[i.toNat]

@[extern "lean_float32_array_fget"]
def get : (ds : @& Float32Array) → (i : @& Nat) → (h : i < ds.size := by get_elem_tactic) → Float32
  | ⟨ds⟩, i, h => ds[i]

@[extern "lean_float32_array_get"]
def get! : (@& Float32Array) → (@& Nat) → Float32
  | ⟨ds⟩, i => if h : i < ds.size then ds[i] else 0

def get? (ds : Float32Array) (i : Nat) : Option Float32 :=
  if h : i < ds.size then
    some (ds.get i h)
  else
    none

instance : GetElem Float32Array Nat Float32 fun xs i => i < xs.size where
  getElem xs i h := xs.get i h

instance : GetElem Float32Array USize Float32 fun xs i => i.toNat < xs.size where
  getElem xs i h := xs.uget i h

@[extern "lean_float32_array_uset"]
def uset : (a : Float32Array) → (i : USize) → Float32 → (h : i.toNat < a.size := by get_elem_tactic) → Float32Array
  | ⟨ds⟩, i, x, h => ⟨ds.set i.toNat x h⟩

@[extern "lean_float32_array_fset"]
def set : (ds : Float32Array) → (i : @& Nat) → Float32 → (h : i < ds.size := by get_elem_tactic) → Float32Array
  | ⟨ds⟩, i, x, h => ⟨ds.set i x h⟩

@[simp]
theorem size_set (xs : Float32Array) (i : Nat) (x : Float32) (h : i < xs.size) :
    (xs.set i x h).size = xs.size := by
  cases xs
  simp [set, size]

@[simp]
theorem get_set_eq (xs : Float32Array) (i : Nat) (x : Float32) (h : i < xs.size) :
    (xs.set i x h).get i (by simp [h]) = x := by
  cases xs
  simp [set, get]

theorem get_set_ne (xs : Float32Array) {i j : Nat} (x : Float32) (hi : i < xs.size)
    (hj : j < (xs.set i x hi).size) (hij : j ≠ i) :
    (xs.set i x hi).get j hj = xs.get j (by simpa using hj) := by
  cases xs
  simp [set, get]
  rw [Array.getElem_set]
  have hji : i ≠ j := fun h => hij h.symm
  simp [hji]
  rfl

@[simp]
theorem get_push_lt (xs : Float32Array) (x : Float32) (i : Nat) (h : i < xs.size) :
    (xs.push x).get i (by rw [size_push]; exact Nat.lt_succ_of_lt h) = xs.get i h := by
  cases xs with
  | mk data =>
  have h' : i < data.size := by simpa [size] using h
  simp only [push, get]
  rw [Array.getElem_push]
  simp [h']
  rfl

@[simp]
theorem get_push_eq (xs : Float32Array) (x : Float32) :
    (xs.push x).get xs.size (by simp) = x := by
  cases xs
  simp [push, get, size]

@[extern "lean_float32_array_replicate"]
def replicate (n : @& Nat) (x : Float32) : Float32Array where
  data := Array.replicate n x

@[simp]
theorem size_replicate (n : Nat) (x : Float32) :
    (replicate n x).size = n := by
  simp [replicate, size]

@[extern "lean_float32_array_replicate2"]
def replicate2 (n : @& Nat) (x y : Float32) : Float32Array where
  data := Array.ofFn fun i : Fin (2 * n) => if i.val % 2 = 0 then x else y

@[simp]
theorem size_replicate2 (n : Nat) (x y : Float32) :
    (replicate2 n x y).size = 2 * n := by
  simp [replicate2, size]

theorem get_replicate2_even (n i : Nat) (x y : Float32) (h : 2 * i < (replicate2 n x y).size) :
    (replicate2 n x y).get (2 * i) h = x := by
  change (Array.ofFn (fun j : Fin (2 * n) => if j.val % 2 = 0 then x else y))[2 * i] = x
  rw [Array.getElem_ofFn]
  simp

theorem get_replicate2_odd (n i : Nat) (x y : Float32)
    (h : 2 * i + 1 < (replicate2 n x y).size) :
    (replicate2 n x y).get (2 * i + 1) h = y := by
  change (Array.ofFn (fun j : Fin (2 * n) => if j.val % 2 = 0 then x else y))[2 * i + 1] = y
  rw [Array.getElem_ofFn]
  simp

@[extern "lean_float32_array_pop"]
def pop (xs : Float32Array) : Float32Array :=
  { data := xs.data.pop }

@[simp]
theorem size_pop (xs : Float32Array) :
    xs.pop.size = xs.size - 1 := by
  cases xs
  simp [pop, size]

theorem get_pop (xs : Float32Array) (i : Nat) (h : i < xs.pop.size) (h' : i < xs.size) :
    xs.pop.get i h = xs.get i h' := by
  cases xs with
  | mk data =>
  simp only [pop, get]
  rw [Array.getElem_pop]
  rfl

@[extern "lean_float32_array_append"]
def append (xs ys : Float32Array) : Float32Array where
  data := xs.data ++ ys.data

@[simp]
theorem size_append (xs ys : Float32Array) :
    (xs.append ys).size = xs.size + ys.size := by
  cases xs
  cases ys
  simp [append, size]

@[simp]
theorem get_append_left (xs ys : Float32Array) (i : Nat) (h : i < xs.size) :
    (xs.append ys).get i (by rw [size_append]; exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)) = xs.get i h := by
  cases xs with
  | mk data =>
  cases ys with
  | mk data' =>
  have h' : i < data.size := by simpa [size] using h
  simp only [append, get]
  rw [Array.getElem_append]
  simp [h']
  rfl

@[simp]
theorem get_append_right (xs ys : Float32Array) (i : Nat)
    (h : i < ys.size) :
    (xs.append ys).get (xs.size + i) (by rw [size_append]; exact Nat.add_lt_add_left h _) = ys.get i h := by
  cases xs with
  | mk data =>
  cases ys with
  | mk data' =>
  have h' : i < data'.size := by simpa [size] using h
  simp only [append, get, size]
  rw [Array.getElem_append]
  have hn : ¬ data.size + i < data.size := by omega
  simp [hn]
  rfl

@[extern "lean_float32_array_set"]
def set! : Float32Array → (@& Nat) → Float32 → Float32Array
  | ⟨ds⟩, i, x => if h : i < ds.size then ⟨ds.set i x h⟩ else ⟨ds⟩

def isEmpty (s : Float32Array) : Bool :=
  s.size == 0

partial def toList (ds : Float32Array) : List Float32 :=
  let rec loop (i r) :=
    if h : i < ds.size then
      loop (i+1) (ds[i] :: r)
    else
      r.reverse
  loop 0 []

end Float32Array

/--
Converts a list of floats into a `Float32Array`.
-/
def List.toFloat32Array (ds : List Float32) : Float32Array :=
  let rec loop
    | [],    r => r
    | b::ds, r => loop ds (r.push b)
  loop ds Float32Array.empty

instance : ToString Float32Array := ⟨fun ds => ds.toList.toString⟩

end NumLean
