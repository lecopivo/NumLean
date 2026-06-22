import NumLean.Data.Idx
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic

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
  toIdx : I → Idx n
  fromIdx : Idx n → I

  left_inv : n < 2 ^ 64 → LeftInverse fromIdx toIdx
  right_inv : n < 2 ^ 64 → RightInverse fromIdx toIdx

  toFin : I → Fin n
  fromFin : Fin n → I

  left_inv' : LeftInverse fromFin toFin
  right_inv' : RightInverse fromFin toFin

  -- toIdx_eq_toFin : n < 2 ^ 64 → ∀ i, (toIdx i).1.toNat = (toFin i).1



export IndexType (toIdx fromIdx toFin fromFin)

namespace IndexType

variable {I n} [IndexType I n]

@[simp]
theorem fromIdx_toIdx (h : n < 2 ^ 64) (i : I) : fromIdx (toIdx i) = i :=
  IndexType.left_inv h i

@[simp]
theorem toIdx_fromIdx (h : n < 2 ^ 64) (i : Idx n) : toIdx (fromIdx i : I) = i :=
  IndexType.right_inv h i

@[simp]
theorem fromFin_toFin (i : I) : fromFin (toFin i) = i :=
  IndexType.left_inv' i

@[simp]
theorem toFin_fromFin (i : Fin n) : toFin (fromFin i : I) = i :=
  IndexType.right_inv' i

/-- `I` is in bijection with `Fin n`. -/
def equivFin : I ≃ Fin n where
  toFun := toFin
  invFun := fromFin
  left_inv := IndexType.left_inv'
  right_inv := IndexType.right_inv'

/-- For `n < 2 ^ 64`, `I` is in bijection with `Idx n`. -/
def equivIdx (h : n < 2 ^ 64) : I ≃ Idx n where
  toFun := toIdx
  invFun := fromIdx
  left_inv := IndexType.left_inv h
  right_inv := IndexType.right_inv h

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
  toIdx y := toIdx (e.symm y)
  fromIdx i := e (fromIdx i)
  toFin y := toFin (e.symm y)
  fromFin i := e (fromFin i)
  left_inv := fun h y => by
    dsimp only
    rw [IndexType.fromIdx_toIdx h, Equiv.apply_symm_apply]
  right_inv := fun h i => by
    dsimp only
    rw [Equiv.symm_apply_apply]
    exact IndexType.toIdx_fromIdx h i
  left_inv' := fun y => by
    dsimp only
    rw [IndexType.fromFin_toFin, Equiv.apply_symm_apply]
  right_inv' := fun i => by
    dsimp only
    rw [Equiv.symm_apply_apply]
    exact IndexType.toFin_fromFin i
  toSize := ⟨⟩

end IndexType

/-- For `n < 2 ^ 64`, `I` is in bijection with `Idx n`. -/
def idxEquiv (I : Type*) {n} [IndexType I n] (h : n < 2 ^ 64) : I ≃ Idx n :=
  IndexType.equivIdx h

namespace IndexType

----------------------------------------------------------------------------------------------------
-- Instances ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Instances

instance : IndexType Empty 0 where
  toIdx x := x.elim
  fromIdx i := i.elim0
  toFin x := x.elim
  fromFin i := i.elim0
  left_inv := fun _ x => x.elim
  right_inv := fun _ i => i.elim0
  left_inv' := fun x => x.elim
  right_inv' := fun i => i.elim0
  toSize := ⟨⟩

instance : IndexType Unit 1 where
  toIdx _ := 0
  fromIdx _ := ()
  toFin _ := 0
  fromFin _ := ()
  left_inv := fun _ _ => Subsingleton.elim _ _
  right_inv := fun _ _ => Subsingleton.elim _ _
  left_inv' := fun _ => Subsingleton.elim _ _
  right_inv' := fun _ => Subsingleton.elim _ _
  toSize := ⟨⟩

instance : IndexType (Fin n) n where
  toIdx x := Fin.toIdx x
  fromIdx i := Idx.toFin i
  toFin x := x
  fromFin i := i
  left_inv := fun h x => Idx.toFin_toIdx x h
  right_inv := fun _ i => Idx.toIdx_toFin i
  left_inv' := fun _ => rfl
  right_inv' := fun _ => rfl
  toSize := ⟨⟩

instance [Fact (n < 2 ^ 64)] : IndexType (Idx n) n where
  toIdx x := x
  fromIdx x := x
  toFin x := Idx.toFin x
  fromFin x := Fin.toIdx x
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl
  left_inv' := fun x => Idx.toIdx_toFin x
  right_inv' := fun x => Idx.toFin_toIdx x (Fact.out)
  toSize := ⟨⟩

instance : IndexType Bool 2 := IndexType.ofEquiv (Fin 2) finTwoEquiv

@[inline]
instance instProd {I J nI nJ} [IndexType I nI] [IndexType J nJ] : IndexType (I × J) (nI * nJ) where
  -- row-major: `nJ * (index of a) + (index of b)`, computed natively in `UInt64`
  toIdx := fun ab => Idx.merge (toIdx ab.1) (toIdx ab.2)
  fromIdx := fun i => (fromIdx (Idx.divIdx nI nJ i), fromIdx (Idx.modIdx nI nJ i))
  toFin := fun ab => finProdFinEquiv (toFin ab.1, toFin ab.2)
  fromFin := fun i =>
    let ab := finProdFinEquiv.symm i
    (fromFin ab.1, fromFin ab.2)
  left_inv := fun h ab => by
    obtain ⟨a, b⟩ := ab
    have hnI : 0 < nI := by have := (toIdx a : Idx nI).isLt; omega
    have hnJ : 0 < nJ := by have := (toIdx b : Idx nJ).isLt; omega
    have hnIlt : nI < 2 ^ 64 := by have : nI ≤ nI * nJ := Nat.le_mul_of_pos_right nI hnJ; omega
    have hnJlt : nJ < 2 ^ 64 := by have : nJ ≤ nI * nJ := Nat.le_mul_of_pos_left nJ hnI; omega
    change (fromIdx (Idx.divIdx nI nJ (Idx.merge (toIdx a) (toIdx b))),
          fromIdx (Idx.modIdx nI nJ (Idx.merge (toIdx a) (toIdx b)))) = (a, b)
    rw [Idx.divIdx_merge (toIdx a) (toIdx b) h, Idx.modIdx_merge (toIdx a) (toIdx b) h,
        IndexType.left_inv hnIlt a, IndexType.left_inv hnJlt b]
  right_inv := fun h i => by
    have hpos : 0 < nI * nJ := by have := i.isLt; omega
    have hnIlt : nI < 2 ^ 64 := by
      have : nI ≤ nI * nJ := Nat.le_mul_of_pos_right nI (Nat.pos_right_of_mul_pos hpos); omega
    have hnJlt : nJ < 2 ^ 64 := by
      have : nJ ≤ nI * nJ := Nat.le_mul_of_pos_left nJ (Nat.pos_left_of_mul_pos hpos); omega
    change Idx.merge (toIdx (fromIdx (Idx.divIdx nI nJ i)))
          (toIdx (fromIdx (Idx.modIdx nI nJ i))) = i
    rw [IndexType.right_inv hnIlt (Idx.divIdx nI nJ i),
        IndexType.right_inv hnJlt (Idx.modIdx nI nJ i), Idx.merge_divIdx_modIdx i h]
  left_inv' := fun ab => by
    change
      (fromFin (finProdFinEquiv.symm (finProdFinEquiv (toFin ab.1, toFin ab.2))).1,
        fromFin (finProdFinEquiv.symm (finProdFinEquiv (toFin ab.1, toFin ab.2))).2) = ab
    rw [Equiv.symm_apply_apply]
    simp
  right_inv' := fun i => by
    dsimp only
    rw [IndexType.toFin_fromFin, IndexType.toFin_fromFin, Equiv.apply_symm_apply]
  toSize := ⟨⟩

instance instSum {α β} [IndexType α m] [IndexType β n] : IndexType (α ⊕ β) (m + n) where
  toIdx := fun x => Idx.sumEncode m n (Sum.map toIdx toIdx x)
  fromIdx := fun i => Sum.map fromIdx fromIdx (Idx.sumDecode m n i)
  toFin := fun x => finSumFinEquiv (Sum.map toFin toFin x)
  fromFin := fun i => Sum.map fromFin fromFin (finSumFinEquiv.symm i)
  left_inv := fun h x => by
    have hmlt : m < 2 ^ 64 := by omega
    have hnlt : n < 2 ^ 64 := by omega
    change
      Sum.map fromIdx fromIdx (Idx.sumDecode m n (Idx.sumEncode m n (Sum.map toIdx toIdx x))) = x
    rw [Idx.sumDecode_encode m n h]
    cases x with
    | inl a => exact congrArg Sum.inl (IndexType.left_inv hmlt a)
    | inr b => exact congrArg Sum.inr (IndexType.left_inv hnlt b)
  right_inv := fun h i => by
    have hmlt : m < 2 ^ 64 := by omega
    have hnlt : n < 2 ^ 64 := by omega
    change Idx.sumEncode m n
          (Sum.map toIdx toIdx (Sum.map fromIdx fromIdx (Idx.sumDecode m n i))) = i
    conv_rhs => rw [← Idx.sumEncode_decode m n h i]
    refine congrArg (Idx.sumEncode m n) ?_
    cases hd : Idx.sumDecode m n i with
    | inl a => exact congrArg Sum.inl (IndexType.right_inv (I := α) hmlt a)
    | inr b => exact congrArg Sum.inr (IndexType.right_inv (I := β) hnlt b)
  left_inv' := fun x => by
    cases x with
    | inl a => simp
    | inr b => simp
  right_inv' := fun i => by
    calc
      finSumFinEquiv (Sum.map toFin toFin (Sum.map fromFin fromFin (finSumFinEquiv.symm i)))
          = finSumFinEquiv (finSumFinEquiv.symm i) := by
            cases finSumFinEquiv.symm i <;> simp
      _ = i := Equiv.apply_symm_apply _ _
  toSize := ⟨⟩

end Instances

-- #eval toIdx ((101 : Idx (2^64+5)), ())

-- instance {n} : ToString (Idx n) := ⟨fun x => toString x.val⟩

-- #eval
--   let a := fromIdx (I:=Idx (2^64+5) × Unit) (toIdx ((100 : Idx (2^64+5)), ()))
--   a

end IndexType

end NumLean
