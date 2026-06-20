import NumLean.Data.HTuple.Range
import NumLean.Data.RangeEnum
import Std.Data.Iterators.Producers.Range

namespace NumLean

namespace HTuple

namespace Range

open Std Std.PRange Std.Iterators

/-- Leaf loop for generic half-open scalar ranges.

This deliberately reuses Lean core's `IteratorLoop` for `Rxo.Iterator α`.  In particular, Nat and
Int get the optimized scalar range loops from core instead of reimplementing them here. -/
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

/-- Implementation helper for structural tuple range loops.

The worker returns `ForInStep`, so `break` propagates through products without storing loop-control
state in the accumulator.  Type-class recursion specializes the loop nest for a fixed profile. -/
class ForInProfile (p : Profile) where
  forInRangeStep {α : Type u} [LE α] [LT α] [DecidableLT α]
      [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
      [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
      {m : Type v → Type w} [Monad m] [IteratorLoop (Rxo.Iterator α) Id m] {β : Type v}
      (r : Std.Rco (HTuple α p)) (init : β)
      (f : (idx : HTuple α p) → idx ∈ r → β → m (ForInStep β)) : m (ForInStep β)

attribute [always_inline, inline, specialize] ForInProfile.forInRangeStep

@[always_inline, inline] instance : ForInProfile .leaf where
  forInRangeStep r init f :=
    match r with
    | ⟨.leaf lo, .leaf hi⟩ =>
        forInLeafStep lo hi init fun idx hidx acc => f (.leaf idx) (mem_iff_Valid.2 hidx) acc

@[always_inline, inline] instance {p q : Profile} [ForInProfile p] [ForInProfile q] :
    ForInProfile (.prod p q) where
  forInRangeStep r init f :=
    match r with
    | ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩ =>
        let r₀ : Std.Rco (HTuple _ p) := lo₀...hi₀
        let r₁ : Std.Rco (HTuple _ q) := lo₁...hi₁
        ForInProfile.forInRangeStep r₀ init fun idx₀ hidx₀ acc =>
          ForInProfile.forInRangeStep r₁ acc fun idx₁ hidx₁ acc =>
            f (.prod idx₀ idx₁)
              (mem_iff_Valid.2 ⟨mem_iff_Valid.1 hidx₀, mem_iff_Valid.1 hidx₁⟩) acc

@[always_inline, inline, specialize] def forInRange {α : Type u} [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
    {p : Profile} [ForInProfile p]
    {m : Type v → Type w} [Monad m] [IteratorLoop (Rxo.Iterator α) Id m] {β : Type v}
    (r : Std.Rco (HTuple α p)) (init : β)
    (f : (idx : HTuple α p) → idx ∈ r → β → m (ForInStep β)) : m β := do
  let step ← ForInProfile.forInRangeStep r init f
  match step with
  | .done acc => pure acc
  | .yield acc => pure acc

/-- Typeclass-specialized fold over a tuple range for loops that do not use `break`.

Unlike `ForInProfile`, this carries the accumulator directly instead of through `ForInStep`, which
lets scalar accumulators such as `Float` remain unboxed in compiled tight loops. -/
class FoldProfile (p : Profile) where
  foldRange {α : Type u} [LE α] [LT α] [DecidableLT α]
      [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
      [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
      {β : Type v} (r : Std.Rco (HTuple α p)) (init : β)
      (f : (idx : HTuple α p) → idx ∈ r → β → β) : β

attribute [always_inline, inline, specialize] FoldProfile.foldRange

@[always_inline, inline] instance : FoldProfile .leaf where
  foldRange r init f :=
    match r with
    | ⟨.leaf lo, .leaf hi⟩ => Id.run do
        let mut acc := init
        for hidx : idx in lo...hi do
          acc := f (.leaf idx) (mem_iff_Valid.2 hidx) acc
        return acc

@[always_inline, inline] instance {p q : Profile} [FoldProfile p] [FoldProfile q] :
    FoldProfile (.prod p q) where
  foldRange r init f :=
    match r with
    | ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩ =>
        let r₀ : Std.Rco (HTuple _ p) := lo₀...hi₀
        let r₁ : Std.Rco (HTuple _ q) := lo₁...hi₁
        FoldProfile.foldRange r₀ init fun idx₀ hidx₀ acc =>
          FoldProfile.foldRange r₁ acc fun idx₁ hidx₁ acc =>
            f (.prod idx₀ idx₁)
              (mem_iff_Valid.2 ⟨mem_iff_Valid.1 hidx₀, mem_iff_Valid.1 hidx₁⟩) acc

@[always_inline, inline, specialize] def foldRange {α : Type u} [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
    {p : Profile} [FoldProfile p] {β : Type v}
    (r : Std.Rco (HTuple α p)) (init : β)
    (f : (idx : HTuple α p) → idx ∈ r → β → β) : β :=
  FoldProfile.foldRange r init f

@[always_inline, inline]
instance instForIn'RcoHTuple {α : Type u} [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
    {p : Profile} [ForInProfile p]
    {m : Type v → Type w} [Monad m] [IteratorLoop (Rxo.Iterator α) Id m] :
    ForIn' m (Std.Rco (HTuple α p)) (HTuple α p) inferInstance where
  forIn' r init f :=
    forInRange r init f

/-- Explicit indexed view of a natural tuple range. -/
structure Enum (p : Profile) where
  range : Std.Rco (HTuple Nat p)

/-- Membership for `Enum`: the natural number is the row-major linear index of the tuple. -/
@[inline] def Enum.Valid {p : Profile} (r : Std.Rco (HTuple Nat p)) (out : Nat × HTuple Nat p) : Prop :=
  out.2 ∈ r ∧ out.1 = linearIndex r.lower r.upper out.2

instance instMembershipEnum {p : Profile} : Membership (Nat × HTuple Nat p) (Enum p) where
  mem e out := Enum.Valid e.range out

class EnumForInProfile (p : Profile) where
  forInEnum {m : Type u → Type v} [Monad m] {β : Type u}
      (r : Std.Rco (HTuple Nat p)) (init : β)
      (f : (out : Nat × HTuple Nat p) → out ∈ (Enum.mk r : Enum p) → β → m (ForInStep β)) : m β

attribute [inline, specialize] EnumForInProfile.forInEnum

@[inline] instance : EnumForInProfile .leaf where
  forInEnum r init f :=
    match r with
    | ⟨.leaf lo, .leaf hi⟩ =>
        ForIn'.forIn' (m := _) (ρ := Std.Rco Nat) (α := Nat) (lo...hi) init
          fun idx hidx acc =>
            let out : Nat × HTuple Nat .leaf := (idx - lo, .leaf idx)
            f out ⟨mem_iff_Valid.2 hidx, rfl⟩ acc

@[inline] instance {p q : Profile} [EnumForInProfile p] [EnumForInProfile q] :
    EnumForInProfile (.prod p q) where
  forInEnum r init f :=
    match r with
    | ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩ => do
        let r₀ : Std.Rco (HTuple Nat p) := lo₀...hi₀
        let r₁ : Std.Rco (HTuple Nat q) := lo₁...hi₁
        let step ← EnumForInProfile.forInEnum r₀ (ForInStep.yield init) fun out₀ hout₀ stepAcc =>
          match stepAcc with
          | .done acc => pure (ForInStep.done (ForInStep.done acc))
          | .yield acc => do
              let inner ← EnumForInProfile.forInEnum r₁ (ForInStep.yield acc) fun out₁ hout₁ stepAcc =>
                match stepAcc with
                | .done acc => pure (ForInStep.done (ForInStep.done acc))
                | .yield acc => do
                    let idx₀ := out₀.2
                    let idx₁ := out₁.2
                    let idx := HTuple.prod idx₀ idx₁
                    let out : Nat × HTuple Nat (.prod p q) :=
                      (linearIndex (.prod lo₀ lo₁) (.prod hi₀ hi₁) idx, idx)
                    let hidx : idx ∈ ((HTuple.prod lo₀ lo₁)...(HTuple.prod hi₀ hi₁)) :=
                      mem_iff_Valid.2 ⟨mem_iff_Valid.1 hout₀.1, mem_iff_Valid.1 hout₁.1⟩
                    let step ← f out ⟨hidx, rfl⟩ acc
                    match step with
                    | .done acc => pure (ForInStep.done (ForInStep.done acc))
                    | .yield acc => pure (ForInStep.yield (ForInStep.yield acc))
              match inner with
              | .done acc => pure (ForInStep.done (ForInStep.done acc))
              | .yield acc => pure (ForInStep.yield (ForInStep.yield acc))
        match step with
        | .done acc => pure acc
        | .yield acc => pure acc

instance instForIn'Enum {p : Profile} [EnumForInProfile p]
    {m : Type u → Type v} [Monad m] :
    ForIn' m (Enum p) (Nat × HTuple Nat p) inferInstance where
  forIn' e init f :=
    EnumForInProfile.forInEnum e.range init f

end Range

end HTuple

end NumLean

namespace Std.Rco

/-- Enumerate a natural hierarchical tuple range with row-major linear indices. -/
@[inline] instance {p : NumLean.HTuple.Profile} :
    HasEnum (Std.Rco (NumLean.HTuple Nat p)) (NumLean.HTuple.Range.Enum p) where
  enum r := ⟨r⟩

end Std.Rco
