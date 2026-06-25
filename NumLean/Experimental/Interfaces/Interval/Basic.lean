import Mathlib.Data.Set.Basic

namespace NumLean

namespace Interval

/-- A type `I` represents intervals over exact values in `R`. -/
class IntervalType (I : Type u) (R : outParam (Type v)) where
  interval : I → Set R
  split : I → I × I
  mem_split : ∀ {x : R} {i : I}, x ∈ interval i → x ∈ interval (split i).1 ∨ x ∈ interval (split i).2

export IntervalType (interval split mem_split)

variable {I : Type u} {R : Type v} [IntervalType I R]

instance : Membership R I where
  mem i x := x ∈ interval i

theorem mem_interval_iff {i : I} {x : R} : x ∈ i ↔ x ∈ interval i := Iff.rfl

end Interval

end NumLean
