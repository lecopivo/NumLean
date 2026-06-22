import NumLean.Mathlib.FiberedAddTorsor.Basic
import Mathlib.Algebra.Group.PUnit
import Mathlib.Topology.Order

namespace NumLean

namespace FiberedAddTorsor

/-- Type tag saying that the type `α` should be regarded as a discrete fiber index for the
purpose of `FiberedAddTorsor`. -/
class Discrete (α : Type u)

instance : Discrete Nat := ⟨⟩
instance : Discrete Int := ⟨⟩
instance : Discrete UInt8 := ⟨⟩
instance : Discrete UInt16 := ⟨⟩
instance : Discrete UInt32 := ⟨⟩
instance : Discrete UInt64 := ⟨⟩
instance : Discrete Int8 := ⟨⟩
instance : Discrete Int16 := ⟨⟩
instance : Discrete Int32 := ⟨⟩
instance : Discrete Int64 := ⟨⟩
instance [Discrete α] : Discrete (List α) := ⟨⟩
instance [Discrete α] : Discrete (Array α) := ⟨⟩
instance [Discrete α] {n} : Discrete (_root_.Vector α n) := ⟨⟩
instance [Discrete α] [Discrete β] : Discrete (α ⊕ β) := ⟨⟩
instance [Discrete α] [Discrete β] : Discrete (α × β) := ⟨⟩
instance [Discrete α] [Discrete β] : Discrete (MProd α β) := ⟨⟩

instance : TopologicalSpace UInt8 := ⊥
instance : DiscreteTopology UInt8 := ⟨rfl⟩
instance : TopologicalSpace UInt16 := ⊥
instance : DiscreteTopology UInt16 := ⟨rfl⟩
instance : TopologicalSpace UInt32 := ⊥
instance : DiscreteTopology UInt32 := ⟨rfl⟩
instance : TopologicalSpace UInt64 := ⊥
instance : DiscreteTopology UInt64 := ⟨rfl⟩
instance : TopologicalSpace Int8 := ⊥
instance : DiscreteTopology Int8 := ⟨rfl⟩
instance : TopologicalSpace Int16 := ⊥
instance : DiscreteTopology Int16 := ⟨rfl⟩
instance : TopologicalSpace Int32 := ⊥
instance : DiscreteTopology Int32 := ⟨rfl⟩
instance : TopologicalSpace Int64 := ⊥
instance : DiscreteTopology Int64 := ⟨rfl⟩

@[reducible]
def unitFiberedAddTorsor (I : Type*) : FiberedAddTorsor Unit I where
  vadd := fun _ i => i
  zero_vadd _ := rfl
  add_vadd _ _ _ := rfl
  vsub := fun _ _ => ()
  fiber := fun i j => i = j
  fiber_equiv := by
    constructor <;> grind
  vsub_vadd' := by
    intro i j h
    exact h.symm
  vadd_vsub' := by
    intros
    rfl
  vadd_fiber := by
    intros
    rfl

instance : FiberedAddTorsor Unit Nat := unitFiberedAddTorsor Nat
instance : FiberedAddTorsor Unit Int := unitFiberedAddTorsor Int
instance : FiberedAddTorsor Unit UInt8 := unitFiberedAddTorsor UInt8
instance : FiberedAddTorsor Unit UInt16 := unitFiberedAddTorsor UInt16
instance : FiberedAddTorsor Unit UInt32 := unitFiberedAddTorsor UInt32
instance : FiberedAddTorsor Unit UInt64 := unitFiberedAddTorsor UInt64
instance : FiberedAddTorsor Unit Int8 := unitFiberedAddTorsor Int8
instance : FiberedAddTorsor Unit Int16 := unitFiberedAddTorsor Int16
instance : FiberedAddTorsor Unit Int32 := unitFiberedAddTorsor Int32
instance : FiberedAddTorsor Unit Int64 := unitFiberedAddTorsor Int64

end FiberedAddTorsor

end NumLean
