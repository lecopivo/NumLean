module

public import Init.Data.Array.DecidableEq

@[expose] public section

namespace NumLean

structure Int32Array where
  data : Array Int32

attribute [extern "lean_int32_array_mk"] Int32Array.mk
attribute [extern "lean_int32_array_data"] Int32Array.data

namespace Int32Array

attribute [ext] Int32Array

deriving instance BEq for Int32Array

@[extern "lean_mk_empty_int32_array"]
def emptyWithCapacity (c : @& Nat) : Int32Array :=
  { data := Array.mkEmpty c }

def empty : Int32Array := emptyWithCapacity 0

instance : Inhabited Int32Array where default := empty
instance : EmptyCollection Int32Array where emptyCollection := empty

@[extern "lean_int32_array_push"]
def push : Int32Array → Int32 → Int32Array
  | ⟨data⟩, x => ⟨data.push x⟩

@[extern "lean_int32_array_size", tagged_return]
def size : (@& Int32Array) → Nat
  | ⟨data⟩ => data.size

@[simp]
def usize (xs : @& Int32Array) : USize :=
  xs.size.toUSize

@[extern "lean_int32_array_uget"]
def uget : (xs : @& Int32Array) → (i : USize) → i.toNat < xs.size → Int32
  | ⟨data⟩, i, h => data[i.toNat]

@[extern "lean_int32_array_fget"]
def get : (xs : @& Int32Array) → (i : @& Nat) → (h : i < xs.size := by get_elem_tactic) → Int32
  | ⟨data⟩, i, h => data[i]

@[extern "lean_int32_array_get"]
def get! : (@& Int32Array) → (@& Nat) → Int32
  | ⟨data⟩, i => if h : i < data.size then data[i] else 0

instance : GetElem Int32Array Nat Int32 fun xs i => i < xs.size where
  getElem xs i h := xs.get i h

instance : GetElem Int32Array USize Int32 fun xs i => i.toNat < xs.size where
  getElem xs i h := xs.uget i h

@[extern "lean_int32_array_uset"]
def uset : (xs : Int32Array) → (i : USize) → Int32 → (h : i.toNat < xs.size := by get_elem_tactic) → Int32Array
  | ⟨data⟩, i, x, h => ⟨data.set i.toNat x h⟩

@[extern "lean_int32_array_fset"]
def set : (xs : Int32Array) → (i : @& Nat) → Int32 → (h : i < xs.size := by get_elem_tactic) → Int32Array
  | ⟨data⟩, i, x, h => ⟨data.set i x h⟩

@[extern "lean_int32_array_set"]
def set! : Int32Array → (@& Nat) → Int32 → Int32Array
  | ⟨data⟩, i, x => if h : i < data.size then ⟨data.set i x h⟩ else ⟨data⟩

end Int32Array

structure Int64Array where
  data : Array Int64

attribute [extern "lean_int64_array_mk"] Int64Array.mk
attribute [extern "lean_int64_array_data"] Int64Array.data

namespace Int64Array

attribute [ext] Int64Array
deriving instance BEq for Int64Array

@[extern "lean_mk_empty_int64_array"]
def emptyWithCapacity (c : @& Nat) : Int64Array :=
  { data := Array.mkEmpty c }

def empty : Int64Array := emptyWithCapacity 0

instance : Inhabited Int64Array where default := empty
instance : EmptyCollection Int64Array where emptyCollection := empty

@[extern "lean_int64_array_push"]
def push : Int64Array → Int64 → Int64Array
  | ⟨data⟩, x => ⟨data.push x⟩

@[extern "lean_int64_array_size", tagged_return]
def size : (@& Int64Array) → Nat
  | ⟨data⟩ => data.size

@[simp]
def usize (xs : @& Int64Array) : USize :=
  xs.size.toUSize

@[extern "lean_int64_array_uget"]
def uget : (xs : @& Int64Array) → (i : USize) → i.toNat < xs.size → Int64
  | ⟨data⟩, i, h => data[i.toNat]

@[extern "lean_int64_array_fget"]
def get : (xs : @& Int64Array) → (i : @& Nat) → (h : i < xs.size := by get_elem_tactic) → Int64
  | ⟨data⟩, i, h => data[i]

@[extern "lean_int64_array_get"]
def get! : (@& Int64Array) → (@& Nat) → Int64
  | ⟨data⟩, i => if h : i < data.size then data[i] else 0

instance : GetElem Int64Array Nat Int64 fun xs i => i < xs.size where
  getElem xs i h := xs.get i h

instance : GetElem Int64Array USize Int64 fun xs i => i.toNat < xs.size where
  getElem xs i h := xs.uget i h

@[extern "lean_int64_array_uset"]
def uset : (xs : Int64Array) → (i : USize) → Int64 → (h : i.toNat < xs.size := by get_elem_tactic) → Int64Array
  | ⟨data⟩, i, x, h => ⟨data.set i.toNat x h⟩

@[extern "lean_int64_array_fset"]
def set : (xs : Int64Array) → (i : @& Nat) → Int64 → (h : i < xs.size := by get_elem_tactic) → Int64Array
  | ⟨data⟩, i, x, h => ⟨data.set i x h⟩

@[extern "lean_int64_array_set"]
def set! : Int64Array → (@& Nat) → Int64 → Int64Array
  | ⟨data⟩, i, x => if h : i < data.size then ⟨data.set i x h⟩ else ⟨data⟩

end Int64Array

structure USizeArray where
  data : Array USize

attribute [extern "lean_usize_array_mk"] USizeArray.mk
attribute [extern "lean_usize_array_data"] USizeArray.data

namespace USizeArray

attribute [ext] USizeArray
deriving instance BEq for USizeArray

@[extern "lean_mk_empty_usize_array"]
def emptyWithCapacity (c : @& Nat) : USizeArray :=
  { data := Array.mkEmpty c }

def empty : USizeArray := emptyWithCapacity 0
instance : Inhabited USizeArray where default := empty
instance : EmptyCollection USizeArray where emptyCollection := empty

@[extern "lean_usize_array_push"]
def push : USizeArray → USize → USizeArray
  | ⟨data⟩, x => ⟨data.push x⟩

@[extern "lean_usize_array_size", tagged_return]
def size : (@& USizeArray) → Nat
  | ⟨data⟩ => data.size

@[simp]
def usize (xs : @& USizeArray) : USize :=
  xs.size.toUSize

@[extern "lean_usize_array_uget"]
def uget : (xs : @& USizeArray) → (i : USize) → i.toNat < xs.size → USize
  | ⟨data⟩, i, h => data[i.toNat]

@[extern "lean_usize_array_fget"]
def get : (xs : @& USizeArray) → (i : @& Nat) → (h : i < xs.size := by get_elem_tactic) → USize
  | ⟨data⟩, i, h => data[i]

@[extern "lean_usize_array_get"]
def get! : (@& USizeArray) → (@& Nat) → USize
  | ⟨data⟩, i => if h : i < data.size then data[i] else 0

instance : GetElem USizeArray Nat USize fun xs i => i < xs.size where
  getElem xs i h := xs.get i h

instance : GetElem USizeArray USize USize fun xs i => i.toNat < xs.size where
  getElem xs i h := xs.uget i h

@[extern "lean_usize_array_uset"]
def uset : (xs : USizeArray) → (i : USize) → USize → (h : i.toNat < xs.size := by get_elem_tactic) → USizeArray
  | ⟨data⟩, i, x, h => ⟨data.set i.toNat x h⟩

@[extern "lean_usize_array_fset"]
def set : (xs : USizeArray) → (i : @& Nat) → USize → (h : i < xs.size := by get_elem_tactic) → USizeArray
  | ⟨data⟩, i, x, h => ⟨data.set i x h⟩

@[extern "lean_usize_array_set"]
def set! : USizeArray → (@& Nat) → USize → USizeArray
  | ⟨data⟩, i, x => if h : i < data.size then ⟨data.set i x h⟩ else ⟨data⟩

end USizeArray

end NumLean
