import NumLean.Data.TensorIndex.Basic
import Std.Data.Iterators.Producers.Range

namespace NumLean

namespace HTuple

namespace Range

open Std Std.PRange Std.Iterators

/-- Pointwise membership for half-open hierarchical tuple ranges. -/
@[inline] def Valid {α : Type u} [LE α] [LT α] : {p : Profile} →
    HTuple α p → HTuple α p → HTuple α p → Prop
  | .leaf, .leaf lo, .leaf hi, .leaf idx => idx ∈ (lo...hi)
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁, .prod idx₀ idx₁ =>
      Valid lo₀ hi₀ idx₀ ∧ Valid lo₁ hi₁ idx₁

instance instMembershipRcoHTuple {α : Type u} [LE α] [LT α] {p : Profile} :
    Membership (HTuple α p) (Std.Rco (HTuple α p)) where
  mem r idx := Valid r.lower r.upper idx

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
        forInLeafStep lo hi init fun idx hidx acc => f (.leaf idx) hidx acc

@[always_inline, inline] instance {p q : Profile} [ForInProfile p] [ForInProfile q] :
    ForInProfile (.prod p q) where
  forInRangeStep r init f :=
    match r with
    | ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩ =>
        let r₀ : Std.Rco (HTuple _ p) := lo₀...hi₀
        let r₁ : Std.Rco (HTuple _ q) := lo₁...hi₁
        ForInProfile.forInRangeStep r₀ init fun idx₀ hidx₀ acc =>
          ForInProfile.forInRangeStep r₁ acc fun idx₁ hidx₁ acc =>
            f (.prod idx₀ idx₁) ⟨hidx₀, hidx₁⟩ acc

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

@[always_inline, inline]
instance instForIn'RcoHTuple {α : Type u} [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
    {p : Profile} [ForInProfile p]
    {m : Type v → Type w} [Monad m] [IteratorLoop (Rxo.Iterator α) Id m] :
    ForIn' m (Std.Rco (HTuple α p)) (HTuple α p) inferInstance where
  forIn' r init f :=
    forInRange r init f

/-- Cardinality of a half-open natural tuple range. -/
@[inline] def card : {p : Profile} → HTuple Nat p → HTuple Nat p → Nat
  | .leaf, .leaf lo, .leaf hi => hi - lo
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁ => card lo₀ hi₀ * card lo₁ hi₁

/-- Row-major linear index inside a natural tuple range, with the rightmost coordinate fastest. -/
@[inline] def linearIndex : {p : Profile} → HTuple Nat p → HTuple Nat p → HTuple Nat p → Nat
  | .leaf, .leaf lo, _hi, .leaf idx => idx - lo
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁, .prod idx₀ idx₁ =>
      linearIndex lo₁ hi₁ idx₁ + card lo₁ hi₁ * linearIndex lo₀ hi₀ idx₀

/-- Structural list specification for natural tuple ranges, in row-major order. -/
@[inline] def toList : {p : Profile} → HTuple Nat p → HTuple Nat p → List (HTuple Nat p)
  | .leaf, .leaf lo, .leaf hi => (List.range' lo (hi - lo)).map HTuple.leaf
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁ =>
      (toList lo₀ hi₀).flatMap fun idx₀ =>
        (toList lo₁ hi₁).map fun idx₁ => HTuple.prod idx₀ idx₁

@[simp] theorem card_leaf (lo hi : Nat) : card (.leaf lo) (.leaf hi) = hi - lo := rfl

@[simp] theorem card_prod {p q : Profile}
    (lo₀ hi₀ : HTuple Nat p) (lo₁ hi₁ : HTuple Nat q) :
    card (.prod lo₀ lo₁) (.prod hi₀ hi₁) = card lo₀ hi₀ * card lo₁ hi₁ := rfl

@[simp] theorem toList_leaf (lo hi : Nat) :
    toList (.leaf lo) (.leaf hi) = (List.range' lo (hi - lo)).map HTuple.leaf := rfl

@[simp] theorem toList_prod {p q : Profile}
    (lo₀ hi₀ : HTuple Nat p) (lo₁ hi₁ : HTuple Nat q) :
    toList (.prod lo₀ lo₁) (.prod hi₀ hi₁) =
      (toList lo₀ hi₀).flatMap fun idx₀ =>
        (toList lo₁ hi₁).map fun idx₁ => HTuple.prod idx₀ idx₁ := rfl

theorem length_toList : {p : Profile} → (lo hi : HTuple Nat p) →
    (toList lo hi).length = card lo hi
  | .leaf, .leaf lo, .leaf hi => by simp
  | .prod _ _, .prod lo₀ lo₁, .prod hi₀ hi₁ => by
      simp [length_toList lo₀ hi₀, length_toList lo₁ hi₁]

@[simp] theorem card_zero_shape {p : Profile} (shape : TensorIndex.Shape p) :
    card 0 shape = TensorIndex.Shape.size shape := by
  induction p with
  | leaf => cases shape; rfl
  | prod p q hp hq =>
      cases shape with
      | prod shape₀ shape₁ => simp [hp, hq]

theorem length_toList_zero_shape {p : Profile} (shape : TensorIndex.Shape p) :
    (toList 0 shape).length = TensorIndex.Shape.size shape := by
  rw [length_toList, card_zero_shape]

theorem valid_zero_shape_iff_inBounds {p : Profile}
    {shape : TensorIndex.Shape p} {idx : TensorIndex.TIndex Nat p} :
    idx ∈ ((0 : HTuple Nat p)...shape) ↔ TensorIndex.TIndex.InBounds shape idx := by
  induction p with
  | leaf =>
      cases shape with | leaf dim =>
      cases idx with | leaf i =>
      change (0 ≤ i ∧ i < dim) ↔ i < dim
      omega
  | prod p q hp hq =>
      cases shape with | prod shape₀ shape₁ =>
      cases idx with | prod idx₀ idx₁ =>
      change (idx₀ ∈ ((0 : HTuple Nat p)...shape₀) ∧ idx₁ ∈ ((0 : HTuple Nat q)...shape₁)) ↔
        TensorIndex.TIndex.InBounds shape₀ idx₀ ∧ TensorIndex.TIndex.InBounds shape₁ idx₁
      rw [hp, hq]

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
            f out ⟨hidx, rfl⟩ acc

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
                    let step ← f out ⟨⟨hout₀.1, hout₁.1⟩, rfl⟩ acc
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

theorem enum_valid_zero_shape {p : Profile} {shape : TensorIndex.Shape p}
    {out : Nat × TensorIndex.TIndex Nat p}
    (h : out ∈ (Enum.mk ((0 : HTuple Nat p)...shape) : Enum p)) :
    TensorIndex.TIndex.InBounds shape out.2 ∧
      out.1 = linearIndex (0 : HTuple Nat p) shape out.2 := by
  exact ⟨valid_zero_shape_iff_inBounds.mp h.1, h.2⟩

end Range

end HTuple

end NumLean

namespace Std.Rco

/-- Enumerate a natural hierarchical tuple range with row-major linear indices. -/
@[inline] def enum {p : NumLean.HTuple.Profile}
    (r : Std.Rco (NumLean.HTuple Nat p)) : NumLean.HTuple.Range.Enum p :=
  ⟨r⟩

end Std.Rco
