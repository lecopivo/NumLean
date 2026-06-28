module

public meta import NumLean.Data.FinHTuple.FinHTupleMap

@[expose] public section

open NumLean
open NumLean.HTuple

namespace Tests.HTupleCoercions

section HTupleLeaf

variable {α : Type} (a : α) (x y : HTuple α .leaf)

example : (HTuple.leaf a).toScalar = a := by simp

example : ((HTuple.leaf a : HTuple α .leaf) : α) = a := by simp

example : HTuple.leaf x.toScalar = x := by simp

example : (HTuple.leaf (x : α) : HTuple α .leaf) = x := by simp

example (hxy : (x : α) = (y : α)) : x = y := HTuple.toScalar_injective hxy

example : Function.Injective (HTuple.toScalar : HTuple α .leaf → α) :=
  HTuple.toScalar_injective

end HTupleLeaf

section ToString

example : toString h((2, 3), 4, 5) = "h((2,3),4,5)" := by native_decide

example : toString hp((•, •), •, •) = "hp((•,•),•,•)" := by native_decide

end ToString

section HTupleNatCast

example (n : Nat) : ((n : HTuple Nat .leaf) : Nat) = n := by simp

example (n : Nat) : (n : HTuple Nat .leaf) = .leaf n := by simp

example (n : Nat) : (Nat.cast n : HTuple Nat .leaf) = .leaf n := by simp

example (n : Nat) : (Nat.cast n : HTuple Nat .leaf).toScalar = n := by simp

example (a b : Nat) : ((HTuple.leaf a : HTuple Nat .leaf) ≤ₑ HTuple.leaf b) ↔ a ≤ b := by
  simp

example (a b : Nat) : ((HTuple.leaf a : HTuple Nat .leaf) <ₑ HTuple.leaf b) ↔ a < b := by
  simp

example (a : HTuple Nat .leaf) (b : Nat) : (a ≤ₑ .leaf b) ↔ (a : Nat) ≤ b := by
  simp

example (a : HTuple Nat .leaf) (b : Nat) : (a <ₑ .leaf b) ↔ (a : Nat) < b := by
  simp

example (a : Nat) (b : HTuple Nat .leaf) : (.leaf a ≤ₑ b) ↔ a ≤ (b : Nat) := by
  simp

example (a : Nat) (b : HTuple Nat .leaf) : (.leaf a <ₑ b) ↔ a < (b : Nat) := by
  simp

example (a : HTuple Nat .leaf) (b : Nat) :
    (a ≤ₑ (Nat.cast b : HTuple Nat .leaf)) ↔ (a : Nat) ≤ b := by
  simp

example (a : HTuple Nat .leaf) (b : Nat) :
    (a <ₑ (Nat.cast b : HTuple Nat .leaf)) ↔ (a : Nat) < b := by
  simp

example (a : Nat) (b : HTuple Nat .leaf) :
    ((Nat.cast a : HTuple Nat .leaf) ≤ₑ b) ↔ a ≤ (b : Nat) := by
  simp

example (a : Nat) (b : HTuple Nat .leaf) :
    ((Nat.cast a : HTuple Nat .leaf) <ₑ b) ↔ a < (b : Nat) := by
  simp

example (a : HTuple Nat .leaf) (b c : Nat) :
    (a <ₑ (Nat.cast b : HTuple Nat .leaf)) → (a : Nat) < b + c := by
  intro hab
  have : (a : Nat) < b := by simpa using hab
  omega

example (a : HTuple Nat .leaf) (b c : Nat) :
    (a <ₑ (Nat.cast b : HTuple Nat .leaf)) → a.toScalar < b + c := by
  intro hab
  have : a.toScalar < b := by simpa using hab
  omega

end HTupleNatCast

section GetElemSetElem

example (xs : Array α) (i : HTuple Nat .leaf) (hi : i.toScalar < xs.size) :
    xs[i]'hi = xs[i.toScalar]'hi := by
  rfl

example [SetElem cont idx elem dom] (xs : cont) (i : HTuple idx .leaf) (x : elem) (hi : dom xs i) :
    setElem xs i x hi = setElem xs i.toScalar x hi := by
  rfl

end GetElemSetElem

section FinHTupleLeaf

variable {n : Nat}

example (i : FinHTuple h(n)) : (((i : Fin n) : Nat) = (i : Nat)) := by simp

example (i : FinHTuple h(n)) : i.toNat = i.val.toScalar := by simp

example (i : FinHTuple h(n)) : (i.toFin : Nat) = i.val.toScalar := by simp

example (i : FinHTuple h(n)) : FinHTuple.ofFin i.toFin = i := by simp

example (i : Fin n) : (FinHTuple.ofFin i).toFin = i := by simp

example (i : Nat) (hi : i < n) : (FinHTuple.ofNatLt i hi : FinHTuple h(n)).toNat = i := by
  simp

example (i : Nat) (hi : i < n) : ((FinHTuple.ofNatLt i hi : FinHTuple h(n)) : Nat) = i := by
  simp

example (i j : FinHTuple h(n)) (hij : i.val = j.val) : i = j := by
  ext
  exact hij

example : Function.Injective (FinHTuple.val : FinHTuple h(n) → HTuple Nat .leaf) :=
  FinHTuple.val_injective

example (xs : Vector α n) (i : FinHTuple h(n)) : xs[i] = xs[(i : Fin n)] := by
  rfl

example [SetElem cont (Fin n) elem dom]
    (xs : cont) (i : FinHTuple h(n)) (x : elem) (hi : dom xs i.toFin) :
    setElem xs i x hi = setElem xs i.toFin x hi := by
  rfl

example (i : Nat) (hi : i < n) : True := by
  lift i to FinHTuple h(n) using hi
  trivial

end FinHTupleLeaf

section FinHTupleGeneral

variable {p : HTuple.Profile} {shape : HTuple Nat p}

example (i : FinHTuple shape) : (i : HTuple Nat p) = i.val := by
  rfl

example (i j : FinHTuple shape) (hij : (i : HTuple Nat p) = (j : HTuple Nat p)) : i = j := by
  ext
  exact hij

example : Function.Injective (FinHTuple.val : FinHTuple shape → HTuple Nat p) :=
  FinHTuple.val_injective

example (idx : HTuple Nat p) (hidx : idx <ₑ shape) : True := by
  lift idx to FinHTuple shape using hidx
  trivial

example (i : FinHTuple shape) : i.val ∈ ((0 : HTuple Nat p)...shape) :=
  FinHTuple.val_mem_zero_shape i

example : Fintype.card (FinHTuple shape) = shape.numel :=
  FinHTuple.card_eq_htuple_card shape

end FinHTupleGeneral

section FinHTupleMap

variable {p q : HTuple.Profile} {src : HTuple Nat p} {dst : HTuple Nat q}

example (f : FinHTupleMap src dst) (i : FinHTuple src) :
    (f.evalFin i).val = f i.val := by
  rfl

example (f : FinHTupleMap src dst) (i : FinHTuple src) :
    (f.evalFin i).isLt = f.inBounds i.val i.isLt := by
  rfl

example (f : FinHTupleMap src dst) (i : HTuple Nat p) (hi : i <ₑ src) :
    (f[i]'hi).val = f i := by
  rfl

example (f : FinHTupleMap src dst) (i : HTuple Nat p) (hi : i <ₑ src) :
    (f[i]'hi).isLt = f.inBounds i hi := by
  rfl

example (f : FinHTupleMap src dst) (i : HTuple Nat p) (hi : i <ₑ src) :
    (f[i]'hi).val <ₑ dst := by
  exact (f[i]'hi).isLt

example {n : Nat} (f : FinHTupleMap src h(n)) (i : HTuple Nat p) (hi : i <ₑ src) :
    ((((f[i]'hi) : FinHTuple h(n)) : Fin n) : Nat) = ((f[i]'hi : FinHTuple h(n)) : Nat) := by
  simp

example {n : Nat} (f : FinHTupleMap src h(n)) (i : HTuple Nat p) (hi : i <ₑ src) :
    ((f[i]'hi : FinHTuple h(n)) : Nat) < n := by
  simpa using (f[i]'hi).isLt

end FinHTupleMap

end Tests.HTupleCoercions
