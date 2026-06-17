import NumLean.Data.HList.Notation
import NumLean.Data.RangeEnum
import Std.Data.Iterators.Producers.Range
import Mathlib.Tactic

namespace NumLean

namespace HList

namespace Range

open Std Std.PRange Std.Iterators

/-- Pointwise membership for raw hierarchical half-open ranges. -/
def Valid {α : Type u} [LE α] [LT α] : HList α → HList α → HList α → Prop
  | .value lo, .value hi, .value idx => idx ∈ (lo...hi)
  | .node [], .node [], .node [] => True
  | .node (lo :: los), .node (hi :: his), .node (idx :: idxs) =>
      Valid lo hi idx ∧ Valid (.node los) (.node his) (.node idxs)
  | _, _, _ => False

theorem valid_leaf_of_get {α : Type u} [LE α] [LT α] {lo hi idx : HPTuple α .leaf} :
    idx.get .leaf ∈ ((lo.get .leaf)...(hi.get .leaf)) → Valid lo.val hi.val idx.val := by
  intro h
  cases lo with
  | mk loVal hlo =>
  cases hlo with
  | value lo =>
  cases hi with
  | mk hiVal hhi =>
  cases hhi with
  | value hi =>
  cases idx with
  | mk idxVal hidx =>
  cases hidx with
  | value idx =>
      simpa [HPTuple.get, Valid] using h

theorem valid_nil {lo hi idx : HPTuple Nat (.node [])} : Valid lo.val hi.val idx.val := by
  cases lo with
  | mk loVal hlo =>
  cases hlo with
  | node_nil =>
  cases hi with
  | mk hiVal hhi =>
  cases hhi with
  | node_nil =>
  cases idx with
  | mk idxVal hidx =>
  cases hidx with
  | node_nil =>
      simp [Valid]

theorem valid_nil_generic {α : Type u} [LE α] [LT α] {lo hi idx : HPTuple α (.node [])} :
    Valid lo.val hi.val idx.val := by
  cases lo with
  | mk loVal hlo =>
  cases hlo with
  | node_nil =>
  cases hi with
  | mk hiVal hhi =>
  cases hhi with
  | node_nil =>
  cases idx with
  | mk idxVal hidx =>
  cases hidx with
  | node_nil =>
      simp [Valid]

theorem valid_node_cons {α : Type u} [LE α] [LT α] {p : Profile} {ps : List Profile}
    {lo hi idx : HPTuple α (.node (p :: ps))} :
    Valid lo.head.val hi.head.val idx.head.val →
    Valid lo.tail.val hi.tail.val idx.tail.val →
    Valid lo.val hi.val idx.val := by
  intro hHead hTail
  cases lo with
  | mk loVal hlo =>
  cases hlo with
  | node_cons hloHead hloTail =>
  cases hi with
  | mk hiVal hhi =>
  cases hhi with
  | node_cons hhiHead hhiTail =>
  cases idx with
  | mk idxVal hidx =>
  cases hidx with
  | node_cons hidxHead hidxTail =>
      simpa [HPTuple.head, HPTuple.tail, Valid] using And.intro hHead hTail

instance instMembershipRcoHPTuple {α : Type u} [LE α] [LT α] {p : Profile} :
    Membership (HPTuple α p) (Std.Rco (HPTuple α p)) where
  mem r idx := Valid r.lower.val r.upper.val idx.val

/-- Enumerated output with its profile and range-membership proofs. -/
structure Out (p : Profile) (lo hi : HList Nat) where
  tuple : HPTuple Nat p
  valid : Valid lo hi tuple.val

/-- Enumerated node payload with its profile and range-membership proofs. -/
structure NodeOut (ps : List Profile) (los his : List (HList Nat)) where
  vals : List (HList Nat)
  of_profile : (HList.node vals).OfProfile (.node ps)
  valid : Valid (.node los) (.node his) (.node vals)

mutual

/-- Structural list specification for natural `HPTuple` ranges. -/
def outs : (p : Profile) → (lo hi : HList Nat) → lo.OfProfile p → hi.OfProfile p →
    List (Out p lo hi)
  | .leaf, .value lo, .value hi, _hlo, _hhi =>
      (List.range' lo (hi - lo)).attach.map fun idx =>
        { tuple := HPTuple.leaf idx.1, valid := by
            have hidx : lo ≤ idx.1 ∧ idx.1 < lo + (hi - lo) := by
              simpa using (List.mem_range'_1 (s := lo) (n := hi - lo) (m := idx.1)).mp idx.2
            have hmem : idx.1 ∈ (lo...hi) := by
              by_cases hle : lo ≤ hi
              · rw [Nat.add_sub_of_le hle] at hidx
                exact hidx
              · have hzero : hi - lo = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hle)
                have hltlo : idx.1 < lo := by simpa [hzero] using hidx.2
                omega
            simpa [HPTuple.leaf, Valid] using hmem }
  | .node ps, .node los, .node his, hlo, hhi =>
      (nodeOuts ps los his hlo hhi).map fun out =>
        { tuple := { val := .node out.vals, of_profile := out.of_profile }, valid := out.valid }
  | _, _, _, _, _ => []

/-- Structural list specification for variadic node payload ranges. -/
def nodeOuts : (ps : List Profile) → (los his : List (HList Nat)) →
    (HList.node los).OfProfile (.node ps) → (HList.node his).OfProfile (.node ps) →
    List (NodeOut ps los his)
  | [], [], [], _hlo, _hhi =>
      [{ vals := [], of_profile := .node_nil, valid := by simp [Valid] }]
  | p :: ps, lo :: los, hi :: his, hlo, hhi =>
      have hlo' : lo.OfProfile p ∧ (HList.node los).OfProfile (.node ps) := by
        cases hlo with
        | node_cons hlo hlos => exact And.intro hlo hlos
      have hhi' : hi.OfProfile p ∧ (HList.node his).OfProfile (.node ps) := by
        cases hhi with
        | node_cons hhi hhis => exact And.intro hhi hhis
      let heads := outs p lo hi hlo'.1 hhi'.1
      let tails := nodeOuts ps los his hlo'.2 hhi'.2
      heads.flatMap fun head =>
        tails.map fun tail =>
          { vals := head.tuple.val :: tail.vals,
            of_profile := by
              exact .node_cons head.tuple.of_profile tail.of_profile,
            valid := by
              simpa [Valid] using And.intro head.valid tail.valid }
  | _, _, _, _, _ => []

end

/-- Structural list specification for natural `HPTuple` ranges, discarding membership proofs. -/
def toList {p : Profile} (lo hi : HPTuple Nat p) : List (HPTuple Nat p) :=
  (outs p lo.val hi.val lo.of_profile hi.of_profile).map (·.tuple)

/-- Cardinality of a half-open natural tuple range. -/
def card : {p : Profile} → HPTuple Nat p → HPTuple Nat p → Nat
  | .leaf, lo, hi => hi.get .leaf - lo.get .leaf
  | .node [], _, _ => 1
  | .node (_ :: _), lo, hi => card lo.head hi.head * card lo.tail hi.tail

/-- Row-major linear index inside a natural tuple range, with the rightmost coordinate fastest. -/
def linearIndex : {p : Profile} → HPTuple Nat p → HPTuple Nat p → HPTuple Nat p → Nat
  | .leaf, lo, _hi, idx => idx.get .leaf - lo.get .leaf
  | .node [], _, _, _ => 0
  | .node (_ :: _), lo, hi, idx =>
      linearIndex lo.tail hi.tail idx.tail + card lo.tail hi.tail * linearIndex lo.head hi.head idx.head

@[simp]
theorem card_leaf (lo hi : Nat) : card (HPTuple.leaf lo) (HPTuple.leaf hi) = hi - lo := by
  simp [card, HPTuple.get, HPTuple.leaf]

@[simp]
theorem card_nil (lo hi : HPTuple Nat (.node [])) : card lo hi = 1 := by
  simp [card]

@[simp]
theorem card_cons {p : Profile} {ps : List Profile}
    (lo₀ hi₀ : HPTuple Nat p) (lo₁ hi₁ : HPTuple Nat (.node ps)) :
    card (HPTuple.cons lo₀ lo₁) (HPTuple.cons hi₀ hi₁) = card lo₀ hi₀ * card lo₁ hi₁ := by
  simp [card]

@[simp]
theorem linearIndex_leaf (lo hi idx : Nat) :
    linearIndex (HPTuple.leaf lo) (HPTuple.leaf hi) (HPTuple.leaf idx) = idx - lo := by
  simp [linearIndex, HPTuple.get, HPTuple.leaf]

@[simp]
theorem linearIndex_nil (lo hi idx : HPTuple Nat (.node [])) : linearIndex lo hi idx = 0 := by
  simp [linearIndex]

@[simp]
theorem linearIndex_cons {p : Profile} {ps : List Profile}
    (lo₀ hi₀ idx₀ : HPTuple Nat p) (lo₁ hi₁ idx₁ : HPTuple Nat (.node ps)) :
    linearIndex (HPTuple.cons lo₀ lo₁) (HPTuple.cons hi₀ hi₁) (HPTuple.cons idx₀ idx₁) =
      linearIndex lo₁ hi₁ idx₁ + card lo₁ hi₁ * linearIndex lo₀ hi₀ idx₀ := by
  simp [linearIndex]

def forInOuts {p : Profile} {lo hi : HList Nat} {m : Type u → Type v} [Monad m] {β : Type u}
    (xs : List (Out p lo hi)) (init : β)
    (f : (idx : HPTuple Nat p) → Valid lo hi idx.val → β → m (ForInStep β)) : m β := do
  let rec go : List (Out p lo hi) → β → m β
    | [], acc => pure acc
    | out :: outs, acc => do
        match ← f out.tuple out.valid acc with
        | .done acc => pure acc
        | .yield acc => go outs acc
  go xs init

/-- Direct non-allocating scalar half-open loop for natural ranges. -/
@[inline, specialize] partial def forInNatRangeStep {m : Type u → Type v} [Monad m] {β : Type u}
    (lo hi idx : Nat) (hlo : lo ≤ idx) (init : β)
    (f : (idx : Nat) → idx ∈ (lo...hi) → β → m (ForInStep β)) : m (ForInStep β) := do
  if hlt : idx < hi then
    let step ← f idx ⟨hlo, hlt⟩ init
    match step with
    | .done acc => pure (.done acc)
    | .yield acc =>
        forInNatRangeStep lo hi (idx + 1) (Nat.le_trans hlo (Nat.le_succ idx)) acc f
  else
    pure (.yield init)

mutual

/-- Direct structural worker for natural `HPTuple` range loops. -/
@[inline, specialize] def forInRangeStep : (p : Profile) → (lo hi : HList Nat) → lo.OfProfile p → hi.OfProfile p →
    {m : Type u → Type v} → [Monad m] → {β : Type u} → β →
    ((idx : HPTuple Nat p) → Valid lo hi idx.val → β → m (ForInStep β)) → m (ForInStep β)
  | .leaf, .value lo, .value hi, _hlo, _hhi, _, _, _, init, f =>
      forInNatRangeStep lo hi lo (Nat.le_refl lo) init fun idx hidx acc =>
        f (HPTuple.leaf idx) (by simpa [Valid, HPTuple.leaf] using hidx) acc
  | .node ps, .node los, .node his, hlo, hhi, _, _, _, init, f =>
      nodeForInRangeStep ps los his hlo hhi init fun out acc =>
        f { val := .node out.vals, of_profile := out.of_profile } out.valid acc
  | _, _, _, _, _, _, _, _, init, _ => pure (.yield init)

/-- Direct structural worker for variadic node payload range loops. -/
@[inline, specialize] def nodeForInRangeStep : (ps : List Profile) → (los his : List (HList Nat)) →
    (HList.node los).OfProfile (.node ps) → (HList.node his).OfProfile (.node ps) →
    {m : Type u → Type v} → [Monad m] → {β : Type u} → β →
    (NodeOut ps los his → β → m (ForInStep β)) → m (ForInStep β)
  | [], [], [], _hlo, _hhi, _, _, _, init, f =>
      f { vals := [], of_profile := .node_nil, valid := by simp [Valid] } init
  | p :: ps, lo :: los, hi :: his, hlo, hhi, _, _, _, init, f =>
      have hloHead : lo.OfProfile p := HList.OfProfile.node_head hlo
      have hloTail : (HList.node los).OfProfile (.node ps) := HList.OfProfile.node_tail hlo
      have hhiHead : hi.OfProfile p := HList.OfProfile.node_head hhi
      have hhiTail : (HList.node his).OfProfile (.node ps) := HList.OfProfile.node_tail hhi
      forInRangeStep p lo hi hloHead hhiHead init fun head hHead acc =>
        nodeForInRangeStep ps los his hloTail hhiTail acc fun tail acc =>
          f {
            vals := head.val :: tail.vals,
            of_profile := .node_cons head.of_profile tail.of_profile,
            valid := by simpa [Valid] using And.intro hHead tail.valid
          } acc
  | _, _, _, _, _, _, _, _, init, _ => pure (.yield init)

end

/-- Direct loop over a natural `HPTuple` range, returning loop control to callers. -/
@[inline, specialize] def forInRangeStepOfRco {p : Profile} {m : Type u → Type v} [Monad m] {β : Type u}
    (r : Std.Rco (HPTuple Nat p)) (init : β)
    (f : (idx : HPTuple Nat p) → idx ∈ r → β → m (ForInStep β)) : m (ForInStep β) :=
  forInRangeStep p r.lower.val r.upper.val r.lower.of_profile r.upper.of_profile init f

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

/-- Typeclass-specialized structural loop for a fixed `HPTuple` profile. -/
class ForInProfile (p : Profile) where
  forInProfileRangeStep {α : Type u} [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
    {m : Type v → Type w} [Monad m] [IteratorLoop (Rxo.Iterator α) Id m] {β : Type v}
    (r : Std.Rco (HPTuple α p)) (init : β)
    (f : (idx : HPTuple α p) → idx ∈ r → β → m (ForInStep β)) : m (ForInStep β)

attribute [inline, specialize] ForInProfile.forInProfileRangeStep

@[inline] instance : ForInProfile .leaf where
  forInProfileRangeStep r init f :=
    forInLeafStep (r.lower.get .leaf) (r.upper.get .leaf) init fun idx hidx acc =>
      f (HPTuple.leaf idx) (valid_leaf_of_get (lo := r.lower) (hi := r.upper) (idx := HPTuple.leaf idx) (by simpa using hidx)) acc

@[inline] instance : ForInProfile (.node []) where
  forInProfileRangeStep r init f :=
    f HPTuple.nil (valid_nil_generic (lo := r.lower) (hi := r.upper) (idx := HPTuple.nil)) init

@[inline] instance {p : Profile} {ps : List Profile} [ForInProfile p] [ForInProfile (.node ps)] :
    ForInProfile (.node (p :: ps)) where
  forInProfileRangeStep r init f := do
    let rHead : Std.Rco (HPTuple _ p) := r.lower.head...r.upper.head
    let rTail : Std.Rco (HPTuple _ (.node ps)) := r.lower.tail...r.upper.tail
    ForInProfile.forInProfileRangeStep rHead init fun idxHead hHead acc => do
      let inner ← ForInProfile.forInProfileRangeStep rTail acc fun idxTail hTail acc =>
        f (HPTuple.cons idxHead idxTail) (by
          have hHead' : Valid r.lower.head.val r.upper.head.val (HPTuple.cons idxHead idxTail).head.val := by
            simpa using hHead
          have hTail' : Valid r.lower.tail.val r.upper.tail.val (HPTuple.cons idxHead idxTail).tail.val := by
            simpa using hTail
          exact valid_node_cons (lo := r.lower) (hi := r.upper)
            (idx := HPTuple.cons idxHead idxTail) hHead' hTail') acc
      match inner with
      | .done acc => pure (.done acc)
      | .yield acc => pure (.yield acc)

@[inline] instance instForIn'RcoHPTuple {α : Type u} [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
    {p : Profile} [ForInProfile p]
    {m : Type v → Type w} [Monad m] [IteratorLoop (Rxo.Iterator α) Id m] :
    ForIn' m (Std.Rco (HPTuple α p)) (HPTuple α p) inferInstance where
  forIn' r init f := do
    let step ← ForInProfile.forInProfileRangeStep r init f
    match step with
    | .done acc => pure acc
    | .yield acc => pure acc

/-- Explicit loop over a natural `HPTuple` range. -/
@[inline, specialize] def forInRange {α : Type u} [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [Finite (Rxo.Iterator α) Id]
    {p : Profile} [ForInProfile p]
    {m : Type v → Type w} [Monad m] [IteratorLoop (Rxo.Iterator α) Id m] {β : Type v}
    (r : Std.Rco (HPTuple α p)) (init : β)
    (f : (idx : HPTuple α p) → idx ∈ r → β → m (ForInStep β)) : m β :=
  instForIn'RcoHPTuple.forIn' r init f

/-- Explicit indexed view of a natural tuple range. -/
structure Enum (p : Profile) where
  range : Std.Rco (HPTuple Nat p)

/-- Membership for `Enum`: the natural number is the row-major linear index of the tuple. -/
def Enum.Valid {p : Profile} (r : Std.Rco (HPTuple Nat p)) (out : Nat × HPTuple Nat p) : Prop :=
  out.2 ∈ r ∧ out.1 = linearIndex r.lower r.upper out.2

instance instMembershipEnum {p : Profile} : Membership (Nat × HPTuple Nat p) (Enum p) where
  mem e out := Enum.Valid e.range out

def forInEnumOuts {p : Profile} {m : Type u → Type v} [Monad m] {β : Type u}
    (r : Std.Rco (HPTuple Nat p)) (xs : List (Out p r.lower.val r.upper.val)) (init : β)
    (f : (out : Nat × HPTuple Nat p) → out ∈ (Enum.mk r : Enum p) → β → m (ForInStep β)) : m β := do
  let rec go : List (Out p r.lower.val r.upper.val) → β → m β
    | [], acc => pure acc
    | out :: outs, acc => do
        let indexed : Nat × HPTuple Nat p := (linearIndex r.lower r.upper out.tuple, out.tuple)
        let valid : indexed ∈ (Enum.mk r : Enum p) := ⟨out.valid, rfl⟩
        match ← f indexed valid acc with
        | .done acc => pure acc
        | .yield acc => go outs acc
  go xs init

instance instForIn'Enum {p : Profile} [ForInProfile p]
    {m : Type u → Type v} [Monad m] [IteratorLoop (Rxo.Iterator Nat) Id m] :
    ForIn' m (Enum p) (Nat × HPTuple Nat p) inferInstance where
  forIn' e init f :=
    forInRange e.range init fun idx hidx acc =>
      let out : Nat × HPTuple Nat p := (linearIndex e.range.lower e.range.upper idx, idx)
      f out ⟨hidx, rfl⟩ acc

/-- Explicit loop over a natural `HPTuple` range with row-major linear indices. -/
def forInEnum {p : Profile} [ForInProfile p]
    {m : Type u → Type v} [Monad m] [IteratorLoop (Rxo.Iterator Nat) Id m] {β : Type u}
    (e : Enum p) (init : β)
    (f : (out : Nat × HPTuple Nat p) → out ∈ e → β → m (ForInStep β)) : m β :=
  instForIn'Enum.forIn' e init f

end Range

end HList

end NumLean

namespace Std.Rco

/-- Enumerate a natural hierarchical tuple range with row-major linear indices. -/
instance instHasEnumRcoHPTuple {p : NumLean.HList.Profile} :
    HasEnum (Std.Rco (NumLean.HList.HPTuple Nat p)) (NumLean.HList.Range.Enum p) where
  enum r := ⟨r⟩

end Std.Rco

namespace NumLean

namespace HList

namespace Range

section Examples

example : (toList (hl(0) : HPTuple Nat hlp(•)) (hl(3) : HPTuple Nat hlp(•))).map HPTuple.toList =
    [[0], [1], [2]] := by
  native_decide

example : (toList (hl(0, 0) : HPTuple Nat hlp(•, •))
      (hl(2, 2) : HPTuple Nat hlp(•, •))).map HPTuple.toList =
    [[0, 0], [0, 1], [1, 0], [1, 1]] := by
  native_decide

example : (hl(1, 1) : HPTuple Nat hlp(•, •)) ∈
    ((hl(0, 0) : HPTuple Nat hlp(•, •))...(hl(2, 2) : HPTuple Nat hlp(•, •))) := by
  simp [Membership.mem, HPTuple.cons, HPTuple.leaf, Valid]

example : (Id.run do
    let mut acc := []
    for i in ((hl(0, 0) : HPTuple Nat hlp(•, •))...(hl(2, 2) : HPTuple Nat hlp(•, •))) do
      acc := i.toList :: acc
    pure acc.reverse) = [[0, 0], [0, 1], [1, 0], [1, 1]] := by
  native_decide

example : (Id.run do
    let mut acc := []
    for i in ((hl(0) : HPTuple Nat hlp(•))...(hl(5) : HPTuple Nat hlp(•))) do
      if i.toList = [3] then
        break
      acc := i.toList :: acc
    pure acc.reverse) = [[0], [1], [2]] := by
  native_decide

example : (Id.run do
    let mut acc := []
    for out in (((hl(0, 0) : HPTuple Nat hlp(•, •))...(hl(2, 2) : HPTuple Nat hlp(•, •))).enum) do
      acc := (out.1, out.2.toList) :: acc
    pure acc.reverse) = [(0, [0, 0]), (1, [0, 1]), (2, [1, 0]), (3, [1, 1])] := by
  native_decide

end Examples

end Range

end HList

end NumLean
