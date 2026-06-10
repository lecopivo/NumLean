namespace NumLean

-- todo: provide C implementations of lean_float32_array_ ...

structure Float32Array where
  data : Array Float32

attribute [extern "lean_float32_array_mk"] Float32Array.mk
attribute [extern "lean_float32_array_data"] Float32Array.data

namespace Float32Array

deriving instance BEq for Float32Array

attribute [ext] Float32Array

@[extern "lean_mk_empty_float32_array"]
def emptyWithCapacity (c : @& Nat) : Float32Array :=
  { data := #[] }

def empty : Float32Array :=
  emptyWithCapacity 0

instance : Inhabited Float32Array where
  default := empty

instance : EmptyCollection Float32Array where
  emptyCollection := Float32Array.empty

@[extern "lean_float32_array_push"]
def push : Float32Array → Float32 → Float32Array
  | ⟨ds⟩, b => ⟨ds.push b⟩

@[extern "lean_float32_array_size", tagged_return]
def size : (@& Float32Array) → Nat
  | ⟨ds⟩ => ds.size

@[extern "lean_sarray_size", simp]
def usize (a : @& Float32Array) : USize :=
  a.size.toUSize

@[extern "lean_float32_array_uget"]
def uget : (a : @& Float32Array) → (i : USize) → i.toNat < a.size → Float32
  | ⟨ds⟩, i, h => ds[i]

@[extern "lean_float32_array_fget"]
def get : (ds : @& Float32Array) → (i : @& Nat) → (h : i < ds.size := by get_elem_tactic) → Float32
  | ⟨ds⟩, i, h => ds[i]

@[extern "lean_float32_array_get"]
def get! : (@& Float32Array) → (@& Nat) → Float32
  | ⟨ds⟩, i => ds[i]!

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
  | ⟨ds⟩, i, v, h => ⟨ds.uset i v h⟩

@[extern "lean_float32_array_fset"]
def set : (ds : Float32Array) → (i : @& Nat) → Float32 → (h : i < ds.size := by get_elem_tactic) → Float32Array
  | ⟨ds⟩, i, d, h => ⟨ds.set i d h⟩

@[extern "lean_float32_array_set"]
def set! : Float32Array → (@& Nat) → Float32 → Float32Array
  | ⟨ds⟩, i, d => ⟨ds.set! i d⟩

def isEmpty (s : Float32Array) : Bool :=
  s.size == 0
