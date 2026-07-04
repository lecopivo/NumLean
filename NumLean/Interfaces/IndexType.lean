module

public import NumLean.Data.Idx
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace NumLean

open Function

/-- Attach size to a type. -/
class Size (α : Type u) (n : outParam Nat)

/--
Type `I` is isomorphic to `Idx n` (and hence to `Fin n`).

`toIdx`/`fromIdx` are the primitive conversions, computed natively on `UInt64` — no `Nat`
arithmetic. They are required to be mutually inverse only when `n < 2 ^ 64`; for larger `n` the
type `Idx n` cannot represent every index (there are only `2 ^ 64` machine integers), so the
functions are allowed to be junk there. This is why `left_inv` and `right_inv` both carry the
hypothesis `n < 2 ^ 64`, and it lets `Idx n` itself be an `IndexType` with no side condition.
-/
class IndexType (I : Type*) (n : outParam Nat) extends Fintype I, Size I n where
  toFin : I → Fin n
  fromFin : Fin n → I

  left_inv : LeftInverse fromFin toFin
  right_inv : RightInverse fromFin toFin


export IndexType (toFin fromFin)

namespace IndexType

variable {I n} [IndexType I n]

@[simp]
theorem fromFin_toFin (i : I) : fromFin (toFin i) = i :=
  IndexType.left_inv i

@[simp]
theorem toFin_fromFin (i : Fin n) : toFin (fromFin i : I) = i :=
  IndexType.right_inv i

/-- `I` is in bijection with `Fin n`. -/
def equivFin : I ≃ Fin n where
  toFun := toFin
  invFun := fromFin
  left_inv := IndexType.left_inv
  right_inv := IndexType.right_inv

/-- The full enumeration of `I` by `fromFin` over all of `Fin n` is complete. -/
theorem enum_complete [DecidableEq I] :
    (Finset.univ : Finset I) = (List.ofFn (fun i : Fin n => fromFin i)).toFinset := by
  symm
  rw [Finset.eq_univ_iff_forall]
  intro x
  rw [List.mem_toFinset, List.mem_ofFn]
  exact ⟨toFin x, by simp⟩

/-- Transport an `IndexType` structure along an equivalence `e : I ≃ J`. -/
@[reducible]
def ofEquiv {J : Type*} (I : Type*) {n} [IndexType I n] (e : I ≃ J) : IndexType J n where
  toFintype := Fintype.ofEquiv I e
  toFin y := toFin (e.symm y)
  fromFin i := e (fromFin i)
  left_inv := fun y => by
    dsimp only
    rw [IndexType.fromFin_toFin, Equiv.apply_symm_apply]
  right_inv := fun i => by
    dsimp only
    rw [Equiv.symm_apply_apply]
    exact IndexType.toFin_fromFin i
  toSize := ⟨⟩

end IndexType


namespace IndexType

----------------------------------------------------------------------------------------------------
-- Instances ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Instances

instance : IndexType Empty 0 where
  toFin x := x.elim
  fromFin i := i.elim0
  left_inv := fun x => x.elim
  right_inv := fun i => i.elim0
  toSize := ⟨⟩

instance : IndexType Unit 1 where
  toFin _ := 0
  fromFin _ := ()
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fun _ => Subsingleton.elim _ _
  toSize := ⟨⟩

instance : IndexType (Fin n) n where
  toFin x := x
  fromFin i := i
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  toSize := ⟨⟩

instance : IndexType Bool 2 := IndexType.ofEquiv (Fin 2) finTwoEquiv

@[inline]
instance instProd {I J nI nJ} [IndexType I nI] [IndexType J nJ] : IndexType (I × J) (nI * nJ) where
  -- row-major: `nJ * (index of a) + (index of b)`, computed natively in `UInt64`
  toFin := fun ab => finProdFinEquiv (toFin ab.1, toFin ab.2)
  fromFin := fun i =>
    let ab := finProdFinEquiv.symm i
    (fromFin ab.1, fromFin ab.2)
  left_inv := fun ab => by
    change
      (fromFin (finProdFinEquiv.symm (finProdFinEquiv (toFin ab.1, toFin ab.2))).1,
        fromFin (finProdFinEquiv.symm (finProdFinEquiv (toFin ab.1, toFin ab.2))).2) = ab
    rw [Equiv.symm_apply_apply]
    simp
  right_inv := fun i => by
    dsimp only
    rw [IndexType.toFin_fromFin, IndexType.toFin_fromFin, Equiv.apply_symm_apply]
  toSize := ⟨⟩

instance instSum {α β} [IndexType α m] [IndexType β n] : IndexType (α ⊕ β) (m + n) where
  toFin := fun x => finSumFinEquiv (Sum.map toFin toFin x)
  fromFin := fun i => Sum.map fromFin fromFin (finSumFinEquiv.symm i)
  left_inv := fun x => by
    cases x with
    | inl a => simp
    | inr b => simp
  right_inv := fun i => by
    calc
      finSumFinEquiv (Sum.map toFin toFin (Sum.map fromFin fromFin (finSumFinEquiv.symm i)))
          = finSumFinEquiv (finSumFinEquiv.symm i) := by
            cases finSumFinEquiv.symm i <;> simp
      _ = i := Equiv.apply_symm_apply _ _
  toSize := ⟨⟩

end Instances

end IndexType

end NumLean
