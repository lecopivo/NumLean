import NumLean.Data.HTuple
import NumLean.Data.FinHTuple

open Lean Std PRange

namespace NumLean.HTuple.Range.Tests

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

example (i) (h : i ∈ h(0, 0, 5)...h(10, 20, 10)) : i ∈ 0...h(10, 20, 30) := by
  get_elem_tactic

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

section ExamplesFromWild

section ToUpstream

end ToUpstream

example {a b : HTuple Nat p} {c d : HTuple Nat q} : (a.prod c) <ₑ (b.prod d) → ¬(b ≤ₑ a) := by
  grind only [grind_htuple_order]

example [LE α] {a : α} {b : HTuple α .leaf} :
    (a ≤ b.toScalar) ↔ (h(a) ≤ₑ b) := by
  grind only [grind_htuple_order]

example {m : Nat} {r : HTuple.Profile} {shape : HTuple Nat r}
    {dstMap : FinHTupleMap shape h(m)} {i : HTuple ℕ r} {h : i ∈ 0...shape} :
    ¬(h(m) ≤ₑ dstMap i) := by grind [grind_htuple_order]

example (a : HTuple ℕ .leaf) (b c : Nat) : (a <ₑ h(b)) → a.toScalar < b + c := by grind

example {n} (a : FinHTuple h(n)) : a < n := by
  fail_if_success grind only [grind_htuple_order]
  have ⟨a,_⟩ := a
  simp
  grind only [grind_htuple_order]

example {n m} (a : FinHTuple h(n)) : a < n + m := by
  fail_if_success grind only [grind_htuple_order]
  have ⟨a,_⟩ := a
  simp
  grind only [grind_htuple_order]

-- `Nat.cast` into `HTuple Nat .leaf` is normalized by the leaf order bridge lemmas.
example (a : HTuple ℕ .leaf) (b c : Nat) : (a <ₑ b) → a.toScalar < b + c := by
  grind only [grind_htuple_order]

example {p q : HTuple.Profile} {src : HTuple Nat p} {dst : HTuple Nat q}
    {map : FinHTupleMap src dst} {i : HTuple ℕ p} {h : i ∈ 0...src}
    {h' : dst ≤ₑ map i} :
    False := by
  grind only [grind_htuple_order]

example {m : Nat}
    {r : HTuple.Profile} {shape : HTuple Nat r} {dstMap : FinHTupleMap shape h(m)} {i : HTuple ℕ r}
    {h : i ∈ 0...shape} :
    (dstMap i).toScalar < m := by
  grind only [grind_htuple_order]

example {m n : Nat}
    {r : HTuple.Profile} {shape : HTuple Nat r} {dstMap : FinHTupleMap shape h(m)} {i : HTuple ℕ r}
    {h : i ∈ 0...shape} :
    (dstMap i).toScalar < m + n := by
  fail_if_success grind only [grind_htuple_order]
  have : (dstMap i).toScalar < m := by grind only [grind_htuple_order]
  grind only [grind_htuple_order]

-- todo: clean up and systematize
theorem t4 {p} (x : HTuple ℕ p) : 0 ≤ₑ x := by grind only [grind_htuple_order]
theorem t5 {p} {shape : HTuple ℕ p} (x : FinHTuple shape) : x.1 <ₑ shape := by grind only [grind_htuple_order]
theorem t6 {p q} {src : HTuple ℕ p} {dst : HTuple ℕ q} (f : FinHTupleMap src dst) (i : HTuple ℕ p) (h : i <ₑ src) : f i <ₑ dst := by grind
theorem t9 {i : HTuple ℕ .leaf} {n : Nat} : n ≤ (i : Nat) ↔ h(n) ≤ₑ i := by grind only [= HTuple.elementwiseLE_leaf']
variable {p} {src : HTuple ℕ p} {n} (f : FinHTupleMap src h(n)) (xs : Vector α n) (i : HTuple ℕ p) (hi : i ∈ 0...src)

example : f i <ₑ h(n) := by grind
example : (f i : Nat) < n := by  get_elem_tactic


end ExamplesFromWild

end NumLean.HTuple.Range.Tests
