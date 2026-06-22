import NumLean.Interfaces.Algebra.Ring.Lawful
import NumLean.Interfaces.Module.Basic

namespace NumLean
namespace Interfaces
namespace Module

open Interfaces.Algebra

class LawfulModuleOps (K : Type u) (X : Type v) [One K] [Mul K] [Zero K] [Add K]
    [AddMonoidOps X] [SMul K X] : Prop where
  one_smul : ∀ x : X, (1 : K) • x = x
  mul_smul : ∀ (r s : K) (x : X), (r * s) • x = r • s • x
  smul_zero : ∀ r : K, r • (0 : X) = 0
  smul_add : ∀ (r : K) (x y : X), r • (x + y) = r • x + r • y
  add_smul : ∀ (r s : K) (x : X), (r + s) • x = r • x + s • x
  zero_smul : ∀ x : X, (0 : K) • x = 0

instance (priority := 100) instLawfulModuleOpsOfModule {K : Type u} {X : Type v}
    [CommSemiring K] [AddCommMonoid X] [Module K X] : LawfulModuleOps K X where
  one_smul := one_smul K
  mul_smul := mul_smul
  smul_zero := smul_zero
  smul_add := smul_add
  add_smul := add_smul
  zero_smul := zero_smul K

instance (priority := 50) instModuleOfOps {K : Type u} {X : Type v}
    [SemiringOps K] [LawfulSemiringOps K] [AddMonoidOps X] [LawfulAddMonoidOps X]
    [SMul K X] [LawfulModuleOps K X] : Module K X where
  one_smul := LawfulModuleOps.one_smul
  mul_smul := LawfulModuleOps.mul_smul
  smul_zero := LawfulModuleOps.smul_zero
  smul_add := LawfulModuleOps.smul_add
  add_smul := LawfulModuleOps.add_smul
  zero_smul := LawfulModuleOps.zero_smul

example {K : Type u} {X : Type v} [instK : CommSemiring K] [instX : AddCommMonoid X]
    [inst : Module K X] : (instModuleOfOps : Module K X) = inst :=
  rfl

end Module
end Interfaces
end NumLean
