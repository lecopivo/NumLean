import NumLean.Data.HTuple.RangeIterator
import NumLean.Data.HTuple.GetElemTacticInit

open Lean Std PRange

namespace NumLean.HTuple.Range

attribute [get_tensor_elem =] Valid

@[get_tensor_elem =]
theorem mem_iff_Valid {p : Profile} [LT α] [LE α]
    {idx : TensorIndex.TIndex α p} (lo hi : HTuple α p) :
    idx ∈ (lo...hi) ↔ Valid lo hi idx := by rfl

/-- `grind` helper for zero-origin product ranges.

The generic product equation for `Valid` only triggers when the lower bound is syntactically a
`HTuple.prod`.  In goals like `idx ∈ 0...hi`, `grind` knows `0 = .prod 0 0` only as an equality and
does not use that equality to create a new E-matching instance for the `Valid` product rule.  This
theorem exposes the product split at the `Valid` level, where the trigger contains the zero lower
bound directly. -/
@[get_tensor_elem =]
theorem valid_zero_prod {p p' : Profile} [LT α] [LE α] [Zero α]
    {idx : TensorIndex.TIndex α p} {idx' : TensorIndex.TIndex α p'}
    {hi : HTuple α p} {hi' : HTuple α p'} :
    Valid 0 (hi.prod hi') (idx.prod idx') ↔ Valid 0 hi idx ∧ Valid 0 hi' idx' := by rfl

attribute [get_tensor_elem →, get_tensor_elem ←] Rco.lower_le_of_mem Rco.lt_upper_of_mem
attribute [get_tensor_elem ←] HTuple.zero_leaf

/-- Prove simple scalar bounds from `HTuple` half-open range membership hypotheses. -/
macro "get_tensor_elem_tactic" : tactic =>
  `(tactic| grind only [$(mkIdent `get_tensor_elem):ident])

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| get_tensor_elem_tactic)

example (i1 i2 i3 h1 h2 h3 : Nat) (h : h(i1,i2,i3) ∈ h(0,0,0)...h(h1,h2,h3)) :
    i1 < h1 ∧ i2 < h2 ∧ i3 < h3 := by
  -- grind only [get_tensor_elem]
  get_elem_tactic

example (i1 i2 i3 l1 l2 l3 h1 h2 h3 : Nat) (h : h(i1,i2,i3) ∈ h(l1,l2,l3)...h(h1,h2,h3)) :
    l1 ≤ i1 ∧ i1 < h1 ∧ l2 < h2 := by
  -- grind only [get_tensor_elem]
  get_elem_tactic


example (i1 i2 i3 l1 l2 l3 h1 h2 h3 : Int) (h : h(i1,i2,i3) ∈ h(l1,l2,l3)...h(h1,h2,h3)) :
    l1 ≤ i1 ∧ i1 < h1 ∧ l2 < h2 := by
  -- grind only [get_tensor_elem]
  get_elem_tactic


example (i1 i2 i3 h1 h2 h3 : Int) (h : h(i1,i2,i3) ∈ h(0,0,0)...h(h1,h2,h3)) :
    0 ≤ i1 ∧ i1 < h1 ∧ i2 < h2 := by
  -- grind only [get_tensor_elem]
  get_elem_tactic


example (i1 i2 i3 h1 h2 h3 : Int) (h : h(i1,i2,i3) ∈ 0...h(h1,h2,h3)) :
    0 ≤ i1 ∧ i1 < h1 ∧ i2 < h2 := by
  -- grind only [get_tensor_elem]
  get_elem_tactic
