import Mathlib.Analysis.Normed.Group.Defs
import NumLean.Interfaces.Algebra.RNorm

namespace NumLean

@[hierarchy_graph algebra_ops]
class NormedAddMonoidOps (R : outParam (Type u)) (E : Type v) extends RNorm E R,
    AddMonoidOps E

attribute [instance 200] NormedAddMonoidOps.toRNorm NormedAddMonoidOps.toAddMonoidOps

@[hierarchy_graph algebra_lawful]
class LawfulDataRNorm {R : outParam (Type u)} (E : Type v) [RNorm E R] extends
    Norm E, MetricSpace E where
  requiv : R ≃ ℝ
  rnorm_eq_norm : ∀ x : E, ‖x‖ = requiv (RNorm.rnorm (R := R) x)

@[hierarchy_graph algebra_lawful]
class LawfulDataNormedAddMonoidOps {R : outParam (Type u)} (E : Type v)
    [NormedAddMonoidOps R E] extends LawfulDataRNorm E

@[hierarchy_graph algebra_lawful]
class LawfulNormedAddMonoidOps {R : outParam (Type u)} (E : Type v)
    [NormedAddMonoidOps R E] [LawfulDataNormedAddMonoidOps E] : Prop extends
    LawfulAddMonoidOps E

@[hierarchy_graph algebra_ops]
class NormedMonoidOps (R : outParam (Type u)) (E : Type v) extends RNorm E R, MonoidOps E

attribute [instance 200] NormedMonoidOps.toRNorm NormedMonoidOps.toMonoidOps

@[hierarchy_graph algebra_lawful]
class LawfulDataNormedMonoidOps {R : outParam (Type u)} (E : Type v)
    [NormedMonoidOps R E] extends LawfulDataRNorm E

@[hierarchy_graph algebra_ops]
class LawfulNormedMonoidOps {R : outParam (Type u)} (E : Type v) [NormedMonoidOps R E]
    [LawfulDataNormedMonoidOps E] : Prop extends LawfulMonoidOps E

@[hierarchy_graph algebra_ops]
class NormedAddGroupOps (R : outParam (Type u)) (E : Type v) extends
    NormedAddMonoidOps R E, AddGroupOps E

attribute [instance 200] NormedAddGroupOps.toNormedAddMonoidOps NormedAddGroupOps.toAddGroupOps

@[hierarchy_graph algebra_lawful]
class LawfulDataNormedAddGroupOps {R : outParam (Type u)} (E : Type v)
    [NormedAddGroupOps R E] extends LawfulDataNormedAddMonoidOps E

@[hierarchy_graph algebra_lawful]
class LawfulNormedAddGroupOps {R : outParam (Type u)} (E : Type v)
    [NormedAddGroupOps R E] [LawfulDataNormedAddGroupOps E] : Prop extends
    LawfulAddGroupOps E where
  dist_eq : ∀ x y : E, dist x y = ‖-x + y‖

@[hierarchy_graph algebra_ops]
class NormedGroupOps (R : outParam (Type u)) (E : Type v) extends NormedMonoidOps R E,
    GroupOps E

attribute [instance 200] NormedGroupOps.toNormedMonoidOps NormedGroupOps.toGroupOps

@[hierarchy_graph algebra_lawful]
class LawfulDataNormedGroupOps {R : outParam (Type u)} (E : Type v)
    [NormedGroupOps R E] extends LawfulDataNormedMonoidOps E

@[hierarchy_graph algebra_lawful]
class LawfulNormedGroupOps {R : outParam (Type u)} (E : Type v) [NormedGroupOps R E]
    [LawfulDataNormedGroupOps E] : Prop extends LawfulGroupOps E where
  dist_eq : ∀ x y : E, dist x y = ‖x⁻¹ * y‖

end NumLean
