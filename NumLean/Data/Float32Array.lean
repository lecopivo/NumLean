import Init.Data.Float
import Init.Ext
import Init.Data.Array.DecidableEq

namespace NumLean

universe v w

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

partial def toList (ds : Float32Array) : List Float32 :=
  let rec loop (i r) :=
    if h : i < ds.size then
      loop (i+1) (ds[i] :: r)
    else
      r.reverse
  loop 0 []

/--
  We claim this unsafe implementation is correct because an array cannot have more than `usizeSz` elements in our runtime.
  This is similar to the `Array` version.
-/
-- TODO: avoid code duplication in the future after we improve the compiler.
@[inline] unsafe def forInUnsafe {β : Type v} {m : Type v → Type w} [Monad m] (as : Float32Array) (b : β) (f : Float32 → β → m (ForInStep β)) : m β :=
  let sz := as.usize
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := as.uget i lcProof
      match (← f a b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop 0 b

/-- Reference implementation for `forIn` -/
@[implemented_by Float32Array.forInUnsafe]
protected def forIn {β : Type v} {m : Type v → Type w} [Monad m] (as : Float32Array) (b : β) (f : Float32 → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : as.size - 1 < as.size     := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
      match (← f as[as.size - 1 - i] b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop as.size (Nat.le_refl _) b

instance [Monad m] : ForIn m Float32Array Float32 where
  forIn := Float32Array.forIn

/-- See comment at `forInUnsafe` -/
-- TODO: avoid code duplication.
@[inline]
unsafe def foldlMUnsafe {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float32 → m β) (init : β) (as : Float32Array) (start := 0) (stop := as.size) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i+1) stop (← f b (as.uget i lcProof))
  if start < stop then
    if stop ≤ as.size then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure init
  else
    pure init

/-- Reference implementation for `foldlM` -/
@[implemented_by foldlMUnsafe]
def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float32 → m β) (init : β) (as : Float32Array) (start := 0) (stop := as.size) : m β :=
  let fold (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m β := do
      if hlt : j < stop then
        match i with
        | 0    => pure b
        | i'+1 =>
          loop i' (j+1) (← f b (as[j]'(Nat.lt_of_lt_of_le hlt h)))
      else
        pure b
    loop (stop - start) start init
  if h : stop ≤ as.size then
    fold stop h
  else
    fold as.size (Nat.le_refl _)

@[inline]
def foldl {β : Type v} (f : β → Float32 → β) (init : β) (as : Float32Array) (start := 0) (stop := as.size) : β :=
  Id.run <| as.foldlM (pure <| f · ·) init start stop

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
