module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace NumLean

class UntypedIndex (idx : Type u) (idx' : outParam (Type v)) (dom : outParam (idx' → Prop)) where
  equiv : idx ≃ { i : idx' // dom i }

open UntypedIndex

variable [UntypedIndex I I' dom]

@[simp]
theorem dom_equiv (i : I) : dom (equiv i) := (equiv i).2

instance : UntypedIndex (Fin n) Nat (· < n) where
  equiv := {
    toFun x := ⟨x.1, x.2⟩
    invFun x := ⟨x.1, x.2⟩
    left_inv := by intro; rfl
    right_inv := by intro; rfl
  }

instance [UntypedIndex I I' idom] [UntypedIndex J J' jdom] :
    UntypedIndex (I × J) (I' × J') (fun ij => idom ij.1 ∧ jdom ij.2) where
  equiv := {
    toFun := fun ⟨i,j⟩ => ⟨(equiv i, equiv j), by simp⟩
    invFun := fun ⟨(i,j),h⟩ => (equiv.symm ⟨i, by simp_all⟩, equiv.symm ⟨j, by simp_all⟩)
    left_inv := by intro; simp
    right_inv := by intro; simp
  }
