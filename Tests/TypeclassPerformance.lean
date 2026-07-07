module

public import NumLean

@[expose] public section

/-!
Regression tests for typeclass searches that became expensive when scalar algebra instances are
imported together with the generic `Tensor` lawful group file.

These are intentionally small syntheses: if any of them needs a large search through the custom
normed hierarchy, the instance priorities/hierarchy should be fixed rather than raising the bounds.
-/

namespace NumLean.TypeclassPerformance

variable {K X I : Type} {Ks : Nat → Type} {nX nI : Nat}
variable [VectorType Ks K] [HasDefaultFlatRepr X Ks] [HasFlatRepr X Ks nX] [IndexType I nI]

section RingProjections

variable [Ring K]

set_option maxHeartbeats 1800 in
example : Add K := inferInstance

set_option maxHeartbeats 1800 in
example : Zero K := inferInstance

set_option maxHeartbeats 1800 in
example : One K := inferInstance

set_option maxHeartbeats 1800 in
example : SMul ℕ K := inferInstance


end RingProjections

section RingOpsProjections

variable [RingOps K]

set_option maxHeartbeats 1800 in
example : Add K := inferInstance

set_option maxHeartbeats 1800 in
example : Zero K := inferInstance

set_option maxHeartbeats 200 in
example : One K := inferInstance

set_option maxHeartbeats 1800 in
example : SMul ℕ K := inferInstance

end RingOpsProjections

section CommRingProjections

variable [CommRing K]

set_option maxHeartbeats 1600 in
example : Sub K := inferInstance

set_option maxHeartbeats 1600 in
example : Neg K := inferInstance

set_option maxHeartbeats 1600 in
example : IntCast K := inferInstance

end CommRingProjections

section NormedAddCommGroupProjections

variable [NormedAddCommGroup X]

set_option maxHeartbeats 600 in
example : Zero X := inferInstance

set_option maxHeartbeats 600 in
example : Add X := inferInstance

set_option maxHeartbeats 600 in
example : Sub X := inferInstance

set_option maxHeartbeats 600 in
example : Neg X := inferInstance

set_option maxHeartbeats 600 in
example : TopologicalSpace X := inferInstance

set_option maxHeartbeats 600 in
example : PseudoMetricSpace X := inferInstance

end NormedAddCommGroupProjections

section NormedAddGroupOpsProjections

variable [NormedAddGroupOps R X] [LawfulDataNormedAddGroupOps (R := R) X]

set_option maxHeartbeats 600 in
example : Zero X := inferInstance

set_option maxHeartbeats 600 in
example : Add X := inferInstance

set_option maxHeartbeats 600 in
example : Sub X := inferInstance

set_option maxHeartbeats 600 in
example : Neg X := inferInstance

-- example : RNorm X R := inferInstance

set_option maxHeartbeats 600 in
example : TopologicalSpace X := inferInstance

set_option maxHeartbeats 600 in
example : PseudoMetricSpace X := inferInstance

end NormedAddGroupOpsProjections

section ModuleProjections

variable [Ring K] [AddCommMonoid X] [Module K X]

set_option maxHeartbeats 5000 in
example : SMul K X := inferInstance

set_option maxHeartbeats 6200 in
example : DistribSMul K X := inferInstance

set_option maxHeartbeats 6600 in
example : DistribMulAction K X := inferInstance

end ModuleProjections

section TensorInstances

variable [CommRing K] [AddCommMonoid X] [Module K X]
variable [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
variable [HasFlatRepr.LawfulAddMonoidOps X Ks]

set_option maxHeartbeats 9200 in
example : AddCommMonoid (Tensor X I) := inferInstance

set_option maxHeartbeats 20000 in
example : Module K (Tensor X I) := inferInstance

end TensorInstances

section NormedTensorInstances

noncomputable section

variable [CommRing K] [NormedAddCommGroup X] [Module K X]
variable [TensorRingOps Ks K] [LawfulTensorRingOps Ks K]
variable [HasFlatRepr.LawfulAddGroupOps X Ks]

set_option maxHeartbeats 20000 in
example : NormedAddCommGroup (Tensor X I) := inferInstance

set_option maxHeartbeats 20000 in
example : TopologicalSpace (Tensor X I) := inferInstance

set_option maxHeartbeats 20000 in
example : PseudoMetricSpace (Tensor X I) := inferInstance

end

end NormedTensorInstances

section RealModelOpsProjections

variable {R Rs} [RealModelOps R Rs]

set_option maxHeartbeats 1800 in
example : Add R := inferInstance

set_option maxHeartbeats 1800 in
example : Zero R := inferInstance

set_option maxHeartbeats 200 in
example : One R := inferInstance

set_option maxHeartbeats 1800 in
example : SMul R R := inferInstance

end RealModelOpsProjections


section RealModelProjections

variable {R Rs} [RealModelOps R Rs] [LawfulRealModel R]

set_option maxHeartbeats 1800 in
example : Add R := inferInstance

set_option maxHeartbeats 1800 in
example : Zero R := inferInstance

set_option maxHeartbeats 200 in
example : One R := inferInstance

set_option maxHeartbeats 1800 in
example : SMul R R := inferInstance

set_option maxHeartbeats 10000 in
noncomputable
example : NormedSpace R (Tensor R (Fin 10)) := inferInstance

set_option maxHeartbeats 3000 in
noncomputable
example : NormedAddGroup (Tensor R (Fin 10)) := inferInstance

end RealModelProjections



end NumLean.TypeclassPerformance
