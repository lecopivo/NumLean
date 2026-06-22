import NumLean.Interfaces.Algebra.Group.Lawful
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Notation.Prod

namespace NumLean
namespace Interfaces
namespace Algebra

instance {A B : Type _} [AddMonoidOps A] [AddMonoidOps B] : AddMonoidOps (A × B) where
  nsmul n a := ⟨AddMonoidOps.nsmul n a.1, AddMonoidOps.nsmul n a.2⟩

instance {A B : Type _} [AddMonoidOps A] [LawfulAddMonoidOps A]
    [AddMonoidOps B] [LawfulAddMonoidOps B] : LawfulAddMonoidOps (A × B) := by
  letI : AddCommMonoid A := instAddCommMonoidOfOps
  letI : AddCommMonoid B := instAddCommMonoidOfOps
  exact instLawfulAddMonoidOpsOfAddCommMonoid

instance {A B : Type _} [MonoidOps A] [MonoidOps B] : MonoidOps (A × B) where
  npow n a := ⟨MonoidOps.npow n a.1, MonoidOps.npow n a.2⟩

instance {A B : Type _} [MonoidOps A] [LawfulMonoidOps A]
    [MonoidOps B] [LawfulMonoidOps B] : LawfulMonoidOps (A × B) := by
  letI : CommMonoid A := instCommMonoidOfOps
  letI : CommMonoid B := instCommMonoidOfOps
  exact instLawfulMonoidOpsOfCommMonoid

instance {A B : Type _} [AddGroupOps A] [AddGroupOps B] : AddGroupOps (A × B) where
  zsmul n a := ⟨AddGroupOps.zsmul n a.1, AddGroupOps.zsmul n a.2⟩

instance {A B : Type _} [AddGroupOps A] [LawfulAddGroupOps A]
    [AddGroupOps B] [LawfulAddGroupOps B] : LawfulAddGroupOps (A × B) := by
  letI : AddCommGroup A := instAddCommGroupOfOps
  letI : AddCommGroup B := instAddCommGroupOfOps
  exact instLawfulAddGroupOpsOfAddCommGroup

instance {A B : Type _} [GroupOps A] [GroupOps B] : GroupOps (A × B) where
  zpow n a := ⟨GroupOps.zpow n a.1, GroupOps.zpow n a.2⟩

instance {A B : Type _} [GroupOps A] [LawfulGroupOps A]
    [GroupOps B] [LawfulGroupOps B] : LawfulGroupOps (A × B) := by
  letI : CommGroup A := instCommGroupOfOps
  letI : CommGroup B := instCommGroupOfOps
  exact instLawfulGroupOpsOfCommGroup

example {A B : Type _} [AddCommMonoid A] [AddCommMonoid B] :
    (instAddCommMonoidOfOps : AddCommMonoid (A × B)) =
      (inferInstance : AddCommMonoid (A × B)) :=
  rfl

example {A B : Type _} [CommMonoid A] [CommMonoid B] :
    (instCommMonoidOfOps : CommMonoid (A × B)) = (inferInstance : CommMonoid (A × B)) :=
  rfl

example {A B : Type _} [AddCommGroup A] [AddCommGroup B] :
    (instAddCommGroupOfOps : AddCommGroup (A × B)) =
      (inferInstance : AddCommGroup (A × B)) :=
  rfl

example {A B : Type _} [CommGroup A] [CommGroup B] :
    (instCommGroupOfOps : CommGroup (A × B)) = (inferInstance : CommGroup (A × B)) :=
  rfl

end Algebra
end Interfaces
end NumLean
