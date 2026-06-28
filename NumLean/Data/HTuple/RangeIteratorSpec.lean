module

public import NumLean.Data.HTuple.RangeIterator
public import Std.Tactic.Do

@[expose] public section

namespace NumLean

namespace HTuple

namespace Range

open Std.Do Std Std.PRange Std.Iterators

/-- Reference semantics for profile-specialized, breakable HTuple range traversal.

The executable `ForInProfile` class alone contains only code. This law-bearing companion states that
the corresponding `forIn'` traverses the row-major list model `Range.toList`. -/
class LawfulForInProfile (p : Profile) [ForInProfile p] : Prop where
  forIn'_spec {β : Type u} {m : Type u → Type v} {ps : PostShape}
      [Monad m] [WPMonad m ps]
      [IteratorLoop (Rxo.Iterator Nat) Id m]
      {xs : Std.Rco (HTuple Nat p)} {init : β}
      {f : (a : HTuple Nat p) → a ∈ xs → β → m (ForInStep β)}
      (inv : Invariant (toList xs.lower xs.upper) β ps)
      (step : ∀ pref cur suff
        (h : toList xs.lower xs.upper = pref ++ cur :: suff) b,
        Triple
          (f cur (HTuple.Range.mem_of_mem_toList (by simp [h])) b)
          (inv.1 (⟨pref, cur :: suff, h.symm⟩, b))
          (fun r => match r with
            | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
            | .done b' => inv.1 (⟨toList xs.lower xs.upper, [], by simp⟩, b'), inv.2)) :
      Triple (forIn' xs init f)
        (inv.1 (⟨[], toList xs.lower xs.upper, rfl⟩, init))
        (fun b => inv.1 (⟨toList xs.lower xs.upper, [], by simp⟩, b), inv.2)

-- instance : HTuple.Range.LawfulForInProfile .leaf where
--   forIn'_spec {β} {m} {ps} _ _ _ {xs} {init} {f} inv step := by
--     cases xs with
--     | mk lower upper =>
--       cases lower with | leaf lo =>
--       cases upper with | leaf hi =>
--       -- TODO: reduce `ForInProfile.forInRangeStep` to the scalar `Std.Rco Nat` spec.
--       -- The executable leaf loop delegates to `Rco.Internal.iter`; the proof needs the bridge
--       -- between that iterator-level loop and `Spec.forIn'_rco`'s `toList` model.
--       sorry

-- instance {p q : Profile} [ForInProfile p] [ForInProfile q]
--     [HTuple.Range.LawfulForInProfile p] [HTuple.Range.LawfulForInProfile q] :
--     HTuple.Range.LawfulForInProfile (.prod p q) where
--   forIn'_spec {β} {m} {ps} _ _ _ {xs} {init} {f} inv step := by
--     cases xs with
--     | mk lower upper =>
--       cases lower with | prod lo₀ lo₁ =>
--       cases upper with | prod hi₀ hi₁ =>
--       -- TODO: compose the recursive laws for `p` and `q` using a flattened cursor invariant over
--       -- `(toList lo₀ hi₀).flatMap fun idx₀ => (toList lo₁ hi₁).map (HTuple.prod idx₀ ·)`.
--       -- This is the product analogue of the executable nested loop in `ForInProfile`.
--       sorry

end Range

end HTuple

end NumLean

namespace Std.Do

open NumLean
open Std Std.PRange Std.Iterators

/-- `mvcgen` support for `for h : i in lo...hi` over hierarchical tuple ranges.

This mirrors the core `Std.Do.Spec.forIn'_rco` theorem: invariants are stated over the
row-major list specification `HTuple.Range.toList xs.lower xs.upper`, while the actual program keeps
using the custom `ForIn'` instance from `HTuple.Range.ForInProfile`. -/
@[spec]
theorem Spec.forIn'_rco_htuple
    {β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [IteratorLoop (Rxo.Iterator Nat) Id m]
    {p : HTuple.Profile} [HTuple.Range.ForInProfile p] [HTuple.Range.LawfulForInProfile p]
    {xs : Std.Rco (HTuple Nat p)} {init : β}
    {f : (a : HTuple Nat p) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant (HTuple.Range.toList xs.lower xs.upper) β ps)
    (step : ∀ pref cur suff
      (h : HTuple.Range.toList xs.lower xs.upper = pref ++ cur :: suff) b,
      Triple
        (f cur (HTuple.Range.mem_of_mem_toList (by simp [h])) b)
        (inv.1 (⟨pref, cur :: suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨HTuple.Range.toList xs.lower xs.upper, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f)
      (inv.1 (⟨[], HTuple.Range.toList xs.lower xs.upper, rfl⟩, init))
      (fun b => inv.1 (⟨HTuple.Range.toList xs.lower xs.upper, [], by simp⟩, b), inv.2) := by
  exact HTuple.Range.LawfulForInProfile.forIn'_spec inv step

end Std.Do
