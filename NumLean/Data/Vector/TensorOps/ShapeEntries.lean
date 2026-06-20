import NumLean.Data.Vector.TensorOps.Defs
import NumLean.Data.TensorIndex.Basic

namespace NumLean

namespace Vector

namespace ForAll

open TensorIndex

/-- Canonical row-major entries for the tensor-shaped range `0...shape`. -/
def rowMajorEntries {r} (shape : Shape r) :
    List {idx : HTuple Nat r // idx ∈ ((0 : HTuple Nat r)...shape)} :=
  (List.finRange shape.numel).map fun lin =>
    let idx := (FinHTuple.equivFin shape).symm lin
    ⟨idx.val, FinHTuple.val_mem_zero_shape idx⟩

theorem rowMajorEntries_nodup {r} (shape : Shape r) :
    (rowMajorEntries shape).Nodup := by
  classical
  unfold rowMajorEntries
  apply List.Nodup.map
  · intro a b h
    apply Fin.ext
    have hval := congrArg Subtype.val h
    change ((FinHTuple.equivFin shape).symm a).val = ((FinHTuple.equivFin shape).symm b).val at hval
    have hidx : (FinHTuple.equivFin shape).symm a = (FinHTuple.equivFin shape).symm b :=
      FinHTuple.ext hval
    have hfin := congrArg (FinHTuple.equivFin shape) hidx
    simpa using congrArg Fin.val hfin
  · exact List.nodup_finRange _

theorem lawful_entries_nodup {r} (shape : Shape r) :
    (LawfulFold.entries
      (ρ := Std.Rco (HTuple Nat r)) (α := HTuple Nat r)
      ((0 : HTuple Nat r)...shape)).Nodup := by
  exact LawfulFold.entries_nodup
    (ρ := Std.Rco (HTuple Nat r)) (α := HTuple Nat r)
    ((0 : HTuple Nat r)...shape)

end ForAll

end Vector

end NumLean
