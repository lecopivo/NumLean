import NumLean.Data.HTuple.RangeIterator
import NumLean.Data.HTuple.GetElemTacticInit

open Lean Std PRange

namespace NumLean.HTuple.Range

attribute [get_tensor_elem =] Valid

@[get_tensor_elem =]
theorem mem_iff_Valid {p : Profile} [LT α] [LE α]
    {idx : TensorIndex.TIndex α p} {lo hi : HTuple α p} :
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

/-- Pointwise upper-bound comparison for natural tuple ranges. -/
@[get_tensor_elem =]
def UpperLe : {p : Profile} → HTuple Nat p → HTuple Nat p → Prop
  | .leaf, .leaf hi, .leaf hi' => hi ≤ hi'
  | .prod _ _, .prod hi₀ hi₁, .prod hi₀' hi₁' => UpperLe hi₀ hi₀' ∧ UpperLe hi₁ hi₁'

@[get_tensor_elem =]
theorem upperLe_leaf {hi hi' : Nat} : UpperLe (.leaf hi) (.leaf hi') ↔ hi ≤ hi' := by rfl

@[get_tensor_elem =]
theorem upperLe_prod {p q : Profile}
    {hi₀ hi₀' : HTuple Nat p} {hi₁ hi₁' : HTuple Nat q} :
    UpperLe (.prod hi₀ hi₁) (.prod hi₀' hi₁') ↔ UpperLe hi₀ hi₀' ∧ UpperLe hi₁ hi₁' := by rfl

/-- A natural tuple range is contained in the zero-origin range with larger upper bounds. -/
@[get_tensor_elem →]
theorem valid_zero_of_valid_of_upperLe {p : Profile}
    {lo hi hi' idx : HTuple Nat p} :
    Valid lo hi idx → UpperLe hi hi' → Valid 0 hi' idx := by
  induction p with
  | leaf =>
      intro hvalid hupper
      cases lo with | leaf lo =>
      cases hi with | leaf hi =>
      cases hi' with | leaf hi' =>
      cases idx with | leaf idx =>
      change lo ≤ idx ∧ idx < hi at hvalid
      change hi ≤ hi' at hupper
      change 0 ≤ idx ∧ idx < hi'
      omega
  | prod p q hp hq =>
      intro hvalid hupper
      cases lo; cases hi; cases hi'; cases idx
      exact ⟨hp hvalid.1 hupper.1, hq hvalid.2 hupper.2⟩

@[get_tensor_elem →]
theorem mem_zero_of_mem_of_upperLe {p : Profile}
    {lo hi hi' idx : HTuple Nat p} :
    idx ∈ (lo...hi) → UpperLe hi hi' → idx ∈ ((0 : HTuple Nat p)...hi') := by
  intro hmem hupper
  exact mem_iff_Valid.2 (valid_zero_of_valid_of_upperLe (mem_iff_Valid.1 hmem) hupper)

attribute [get_tensor_elem →, get_tensor_elem ←] Rco.lower_le_of_mem Rco.lt_upper_of_mem
attribute [get_tensor_elem =] Rco.mem_iff
attribute [get_tensor_elem ←] HTuple.zero_leaf

/-- Prove simple scalar bounds from `HTuple` half-open range membership hypotheses. -/
macro "get_tensor_elem_tactic" : tactic =>
  `(tactic|
    first
    | grind only [$(mkIdent `get_tensor_elem):ident]
    | exact mem_zero_of_mem_of_upperLe (by assumption) (by simp [UpperLe] <;> omega))

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| get_tensor_elem_tactic)



example (i1 i2 i3 h1 h2 h3 : Nat) (h : h(i1,i2,i3) ∈ h(0,0,0)...h(h1,h2,h3)) :
    i1 < h1 ∧ i2 < h2 ∧ i3 < h3 := by
  get_elem_tactic

example (i1 i2 i3 h1 h2 h3 : Nat) (h : h(i1,i2,i3) ∈ h(0,0,0)...h(h1,h2,h3)) :
    i1 < h1 ∧ i2 < h2 ∧ i3 < h3 := by
  get_tensor_elem_tactic



example (i1 i2 i3 l1 l2 l3 h1 h2 h3 : Nat) (h : h(i1,i2,i3) ∈ h(l1,l2,l3)...h(h1,h2,h3)) :
    l1 ≤ i1 ∧ i1 < h1 ∧ l2 < h2 := by
  get_elem_tactic

example (i1 i2 i3 l1 l2 l3 h1 h2 h3 : Nat) (h : h(i1,i2,i3) ∈ h(l1,l2,l3)...h(h1,h2,h3)) :
    l1 ≤ i1 ∧ i1 < h1 ∧ l2 < h2 := by
  get_tensor_elem_tactic



example (i1 i2 i3 l1 l2 l3 h1 h2 h3 : Int) (h : h(i1,i2,i3) ∈ h(l1,l2,l3)...h(h1,h2,h3)) :
    l1 ≤ i1 ∧ i1 < h1 ∧ l2 < h2 := by
  get_elem_tactic

example (i1 i2 i3 l1 l2 l3 h1 h2 h3 : Int) (h : h(i1,i2,i3) ∈ h(l1,l2,l3)...h(h1,h2,h3)) :
    l1 ≤ i1 ∧ i1 < h1 ∧ l2 < h2 := by
  get_tensor_elem_tactic



example (i1 i2 i3 h1 h2 h3 : Int) (h : h(i1,i2,i3) ∈ h(0,0,0)...h(h1,h2,h3)) :
    0 ≤ i1 ∧ i1 < h1 ∧ i2 < h2 := by
  get_elem_tactic

example (i1 i2 i3 h1 h2 h3 : Int) (h : h(i1,i2,i3) ∈ h(0,0,0)...h(h1,h2,h3)) :
    0 ≤ i1 ∧ i1 < h1 ∧ i2 < h2 := by
  get_tensor_elem_tactic



example (i1 i2 i3 h1 h2 h3 : Int) (h : h(i1,i2,i3) ∈ 0...h(h1,h2,h3)) :
    0 ≤ i1 ∧ i1 < h1 ∧ i2 < h2 := by
  get_elem_tactic

example (i1 i2 i3 h1 h2 h3 : Int) (h : h(i1,i2,i3) ∈ 0...h(h1,h2,h3)) :
    0 ≤ i1 ∧ i1 < h1 ∧ i2 < h2 := by
  get_tensor_elem_tactic



example (i1 h1 : Nat) (h : i1 < h1) :
    h(i1) ∈ h(0)...h(h1) := by
  get_tensor_elem_tactic


example (i1 i2 l1 l2 h1 h2 : Int) (h : l1 ≤ i1 ∧ i1 < h1 ∧ l2 ≤ i2 ∧ i2 < h2) :
    h(i1,i2) ∈ h(l1,l2)...h(h1,h2) := by
  get_tensor_elem_tactic



example (_h : 2 < 10) (_h' : 3 < 20) : h(2,3) ∈ h(0,0)...h(10,20) := by
  get_elem_tactic

example (_h : 2 < 10) (_h' : 3 < 20) : h(2,3) ∈ h(0,0)...h(10,20) := by
  get_tensor_elem_tactic




example (n : Nat) (h : n > 10) : h(n-2) ∈ h(n-3)...h(n)  := by
  get_elem_tactic


example (i) (h : i ∈ h(0, 0, 5)...h(10, 20, 10)) : i ∈ 0...h(10, 20, 30) := by get_elem_tactic




section Tensor

private structure Tensor {p} (shape : HTuple Nat p) where

private instance  {p} (shape : HTuple Nat p) :
    GetElem (Tensor shape) (HTuple Nat p) Float (fun _ idx => idx ∈ 0...shape) where
  getElem _xs _i _h := 0


variable {n} (t : Tensor h(n,20,30)) (hn : n > 10)

/-- info: t[h(2, 3, 4)] : Float -/
#guard_msgs in
#check t[h(2,3,4)]


/-- info: fun i h => t[i] : (i : HTuple ℕ (hp(•, •, •))) → (i ∈ h(0, 0, 5)...h(10, 20, 10)) → Float -/
#guard_msgs in
#check fun (i) (h : i ∈ h(0, 0, 5)...h(10, 20, 10)) => t[i]


end Tensor


end NumLean.HTuple.Range
