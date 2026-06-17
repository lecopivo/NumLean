import NumLean.Data.Vector.Basic
import NumLean.Data.RangeEnum
import Std.Data.Iterators.Producers.Range
import Mathlib.Tactic

namespace Vector

namespace Range

open Std Std.PRange Std.Iterators

@[always_inline, inline] private def cons {α : Type u} {n : Nat} (x : α)
    (xs : Vector α n) : Vector α (n + 1) :=
  ⟨#[x] ++ xs.toArray, by simp [xs.size_toArray, Nat.add_comm]⟩

@[simp] private theorem head_cons {α : Type u} {n : Nat} (x : α) (xs : Vector α n) :
    (cons x xs).head = x := by
  simp [head, cons]

@[simp] private theorem tail_cons {α : Type u} {n : Nat} (x : α) (xs : Vector α n) :
    (cons x xs).tail = xs := by
  apply Vector.ext
  intro i hi
  simp [tail, cons]
  rfl

/-- Pointwise membership for half-open vector ranges. -/
@[inline] def Valid {α : Type u} [LE α] [LT α] : {n : Nat} →
    Vector α n → Vector α n → Vector α n → Prop
  | 0, _, _, _ => True
  | _ + 1, lo, hi, idx => idx.head ∈ (lo.head...hi.head) ∧ Valid lo.tail hi.tail idx.tail

instance instMembershipRcoVector {α : Type u} [LE α] [LT α] {n : Nat} :
    Membership (Vector α n) (Std.Rco (Vector α n)) where
  mem r idx := Valid r.lower r.upper idx

/-- Leaf loop for generic half-open scalar ranges. -/
@[always_inline, inline, specialize] def forInLeafStep {α : Type u} [LE α] [LT α]
    [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
    {m : Type v → Type w} [Monad m] [IteratorLoop (Rxo.Iterator α) Id m] {β : Type v}
    (lo hi : α) (init : β)
    (f : (idx : α) → idx ∈ (lo...hi) → β → m (ForInStep β)) : m (ForInStep β) :=
  haveI := Std.Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
  ForIn'.forIn' (m := m) (ρ := Iter (α := Rxo.Iterator α) α) (α := α)
    (Std.Rco.Internal.iter (lo...hi)) (ForInStep.yield init)
    fun idx hidx stepAcc =>
      match stepAcc with
      | .done acc => pure (ForInStep.done (ForInStep.done acc))
      | .yield acc => do
          have hmem : idx ∈ (lo...hi) := by
            simpa using (Std.Rco.Internal.isPlausibleIndirectOutput_iter_iff (r := (lo...hi)) (a := idx)).mp hidx
          let step ← f idx hmem acc
          match step with
          | .done acc => pure (ForInStep.done (ForInStep.done acc))
          | .yield acc => pure (ForInStep.yield (ForInStep.yield acc))

/-- Typeclass-specialized structural loop for a fixed vector rank. -/
class ForInRank (n : Nat) where
  forInRangeStep {α : Type u} [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
    {m : Type v → Type w} [Monad m] [IteratorLoop (Rxo.Iterator α) Id m] {β : Type v}
    (r : Std.Rco (Vector α n)) (init : β)
    (f : (idx : Vector α n) → idx ∈ r → β → m (ForInStep β)) : m (ForInStep β)

attribute [always_inline, inline, specialize] ForInRank.forInRangeStep

@[always_inline, inline] instance : ForInRank 0 where
  forInRangeStep r init f :=
    f (Vector.ofFn (fun i : Fin 0 => nomatch i)) (by simp [Membership.mem, Valid]) init

@[always_inline, inline] instance {n : Nat} [ForInRank n] : ForInRank (n + 1) where
  forInRangeStep r init f :=
    forInLeafStep r.lower.head r.upper.head init fun head hHead acc => do
      let rTail : Std.Rco (Vector _ n) := r.lower.tail...r.upper.tail
      let step ← ForInRank.forInRangeStep rTail acc fun tail hTail acc =>
        f (cons head tail) (by
          have hTail' : Valid r.lower.tail r.upper.tail (cons head tail).tail := by
            rw [tail_cons]
            exact hTail
          simpa [Membership.mem, Valid, head_cons] using And.intro hHead hTail') acc
      match step with
      | .done acc => pure (.done acc)
      | .yield acc => pure (.yield acc)

@[always_inline, inline] instance instForIn'RcoVector {α : Type u} [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
    {n : Nat} [ForInRank n]
    {m : Type v → Type w} [Monad m] [IteratorLoop (Rxo.Iterator α) Id m] :
    ForIn' m (Std.Rco (Vector α n)) (Vector α n) inferInstance where
  forIn' r init f := do
    let step ← ForInRank.forInRangeStep r init f
    match step with
    | .done acc => pure acc
    | .yield acc => pure acc

/-- Explicit loop over a vector range. -/
@[always_inline, inline, specialize] def forInRange {α : Type u} [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
    {n : Nat} [ForInRank n]
    {m : Type v → Type w} [Monad m] [IteratorLoop (Rxo.Iterator α) Id m] {β : Type v}
    (r : Std.Rco (Vector α n)) (init : β)
    (f : (idx : Vector α n) → idx ∈ r → β → m (ForInStep β)) : m β :=
  instForIn'RcoVector.forIn' r init f

/-- Cardinality of a half-open natural vector range. -/
@[always_inline, inline] def card : {n : Nat} → Vector Nat n → Vector Nat n → Nat
  | 0, _, _ => 1
  | _ + 1, lo, hi => (hi.head - lo.head) * card lo.tail hi.tail

/-- Row-major linear index, with the last coordinate fastest. -/
@[always_inline, inline] def linearIndex : {n : Nat} → Vector Nat n → Vector Nat n → Vector Nat n → Nat
  | 0, _, _, _ => 0
  | _ + 1, lo, hi, idx => linearIndex lo.tail hi.tail idx.tail + card lo.tail hi.tail * (idx.head - lo.head)

/-- Explicit indexed view of a natural vector range. -/
structure Enum (n : Nat) where
  range : Std.Rco (Vector Nat n)

/-- Membership for `Enum`: the natural number is the row-major linear index of the vector. -/
@[inline] def Enum.Valid {n : Nat} (r : Std.Rco (Vector Nat n)) (out : Nat × Vector Nat n) : Prop :=
  out.2 ∈ r ∧ out.1 = linearIndex r.lower r.upper out.2

instance instMembershipEnum {n : Nat} : Membership (Nat × Vector Nat n) (Enum n) where
  mem e out := Enum.Valid e.range out

instance instForIn'Enum {n : Nat} [ForInRank n]
    {m : Type u → Type v} [Monad m] [IteratorLoop (Rxo.Iterator Nat) Id m] :
    ForIn' m (Enum n) (Nat × Vector Nat n) inferInstance where
  forIn' e init f :=
    forInRange e.range init fun idx hidx acc =>
      let out : Nat × Vector Nat n := (linearIndex e.range.lower e.range.upper idx, idx)
      f out ⟨hidx, rfl⟩ acc

/-- Explicit loop over a natural vector range with row-major linear indices. -/
@[inline] def forInEnum {n : Nat} [ForInRank n]
    {m : Type u → Type v} [Monad m] [IteratorLoop (Rxo.Iterator Nat) Id m] {β : Type u}
    (e : Enum n) (init : β)
    (f : (out : Nat × Vector Nat n) → out ∈ e → β → m (ForInStep β)) : m β :=
  instForIn'Enum.forIn' e init f

end Range

end Vector

namespace Std.Rco

/-- Enumerate a natural vector range with row-major linear indices. -/
instance instHasEnumRcoVector {n : Nat} :
    HasEnum (Std.Rco (Vector Nat n)) (Vector.Range.Enum n) where
  enum r := ⟨r⟩

end Std.Rco
