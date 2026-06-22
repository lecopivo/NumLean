import Mathlib.Analysis.Normed.Group.Defs
import NumLean.Algebra.Ops

namespace NumLean

class NormedAddMonoidOps (R : outParam (Type u)) (E : Type v) extends RNorm E R,
    AddMonoidOps E

class LawfulDataRNorm {R : outParam (Type u)} (E : Type v) [RNorm E R] extends
    Norm E, MetricSpace E where
  requiv : R ≃ ℝ
  rnorm_eq_norm : ∀ x : E, ‖x‖ = requiv (RNorm.rnorm (R := R) x)

class LawfulDataNormedAddMonoidOps {R : outParam (Type u)} (E : Type v)
    [NormedAddMonoidOps R E] extends LawfulDataRNorm E

class LawfulNormedAddMonoidOps {R : outParam (Type u)} (E : Type v)
    [NormedAddMonoidOps R E] [LawfulDataNormedAddMonoidOps E] : Prop extends
    LawfulAddMonoidOps E

class NormedMonoidOps (R : outParam (Type u)) (E : Type v) extends RNorm E R, MonoidOps E

class LawfulDataNormedMonoidOps {R : outParam (Type u)} (E : Type v)
    [NormedMonoidOps R E] extends LawfulDataRNorm E

class LawfulNormedMonoidOps {R : outParam (Type u)} (E : Type v) [NormedMonoidOps R E]
    [LawfulDataNormedMonoidOps E] : Prop extends LawfulMonoidOps E

class NormedAddGroupOps (R : outParam (Type u)) (E : Type v) extends
    NormedAddMonoidOps R E, AddGroupOps E

class LawfulDataNormedAddGroupOps {R : outParam (Type u)} (E : Type v)
    [NormedAddGroupOps R E] extends LawfulDataNormedAddMonoidOps E

class LawfulNormedAddGroupOps {R : outParam (Type u)} (E : Type v)
    [NormedAddGroupOps R E] [LawfulDataNormedAddGroupOps E] : Prop extends
    LawfulAddGroupOps E where
  dist_eq : ∀ x y : E, dist x y = ‖-x + y‖

class NormedGroupOps (R : outParam (Type u)) (E : Type v) extends NormedMonoidOps R E,
    GroupOps E

class LawfulDataNormedGroupOps {R : outParam (Type u)} (E : Type v)
    [NormedGroupOps R E] extends LawfulDataNormedMonoidOps E

class LawfulNormedGroupOps {R : outParam (Type u)} (E : Type v) [NormedGroupOps R E]
    [LawfulDataNormedGroupOps E] : Prop extends LawfulGroupOps E where
  dist_eq : ∀ x y : E, dist x y = ‖x⁻¹ * y‖

end NumLean
