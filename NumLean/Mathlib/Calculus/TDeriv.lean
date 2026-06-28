module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import NumLean.Mathlib.FiberedAddTorsor

@[expose] public section

namespace NumLean

open Filter
open scoped Topology

namespace FiberedAddTorsor

section Defs

variable {𝕜 E F X Y : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [FiberedAddTorsor E X] [FiberedAddTorsor F Y]

/-- A function between fibered additive torsors has tangent derivative `f'` at `x` within `s` if it
is eventually fiber-preserving near `x` within `s`, and its displacement-coordinate expression has
Frechet derivative `f'` at the origin. -/
def HasTDerivWithinAt (f : X → Y) (f' : E →L[𝕜] F) (s : Set X) (x : X) : Prop :=
  (∀ᶠ y in 𝓝[s] x, fiber (f y) (f x)) ∧
    HasFDerivWithinAt
      (fun v : E => f (v +ᵥ x) -ᵥ f x)
      f'
      ((fun v : E => v +ᵥ x) ⁻¹' s)
      0

/-- Tangent derivative at a point, without a domain restriction. -/
def HasTDerivAt (f : X → Y) (f' : E →L[𝕜] F) (x : X) : Prop :=
  HasTDerivWithinAt f f' Set.univ x

/-- A function between fibered additive torsors is tangent differentiable within a set at a point if
it admits a tangent derivative there. -/
def TDifferentiableWithinAt (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace X] [TopologicalSpace Y]
    [FiberedAddTorsor E X] [FiberedAddTorsor F Y]
    (f : X → Y) (s : Set X) (x : X) : Prop :=
  ∃ f' : E →L[𝕜] F, HasTDerivWithinAt f f' s x

/-- A function between fibered additive torsors is tangent differentiable at a point if it admits a
tangent derivative there. -/
def TDifferentiableAt (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace X] [TopologicalSpace Y]
    [FiberedAddTorsor E X] [FiberedAddTorsor F Y]
    (f : X → Y) (x : X) : Prop :=
  ∃ f' : E →L[𝕜] F, HasTDerivAt f f' x

/-- The tangent derivative as a continuous linear map. Like `fderiv`, this returns zero if the
derivative does not exist. -/
noncomputable def tderiv (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiberedAddTorsor E X] [FiberedAddTorsor F Y]
    (f : X → Y) (x : X) : E →L[𝕜] F :=
  fderiv 𝕜 (fun v : E => f (v +ᵥ x) -ᵥ f x) 0

end Defs

section Basic

variable {𝕜 E F X Y : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [FiberedAddTorsor E X] [FiberedAddTorsor F Y]
variable {f : X → Y} {f' : E →L[𝕜] F} {s : Set X} {x : X}

omit [TopologicalSpace Y] in
theorem HasTDerivWithinAt.eventually_fiber (hf : HasTDerivWithinAt f f' s x) :
    ∀ᶠ y in 𝓝[s] x, fiber (f y) (f x) :=
  hf.1

omit [TopologicalSpace Y] in
theorem HasTDerivWithinAt.hasFDerivWithinAt (hf : HasTDerivWithinAt f f' s x) :
    HasFDerivWithinAt
      (fun v : E => f (v +ᵥ x) -ᵥ f x)
      f'
      ((fun v : E => v +ᵥ x) ⁻¹' s)
      0 :=
  hf.2

omit [TopologicalSpace Y] in
theorem hasTDerivWithinAt_univ :
    HasTDerivWithinAt f f' Set.univ x ↔ HasTDerivAt f f' x :=
  Iff.rfl

omit [TopologicalSpace Y] in
theorem HasTDerivAt.hasTDerivWithinAt (hf : HasTDerivAt f f' x) :
    HasTDerivWithinAt f f' Set.univ x :=
  hf

omit [TopologicalSpace Y] in
theorem HasTDerivWithinAt.mono {t : Set X}
    (hf : HasTDerivWithinAt f f' t x) (hst : s ⊆ t) :
    HasTDerivWithinAt f f' s x := by
  constructor
  · exact hf.eventually_fiber.filter_mono (nhdsWithin_mono x hst)
  · exact hf.hasFDerivWithinAt.mono (Set.preimage_mono hst)

omit [TopologicalSpace Y] in
theorem HasTDerivAt.eventually_fiber (hf : HasTDerivAt f f' x) :
    ∀ᶠ y in 𝓝 x, fiber (f y) (f x) := by
  simpa [HasTDerivAt, HasTDerivWithinAt] using hf.1

omit [TopologicalSpace Y] in
theorem HasTDerivAt.hasFDerivAt_displacement (hf : HasTDerivAt f f' x) :
    HasFDerivAt
      (fun v : E => f (v +ᵥ x) -ᵥ f x)
      f'
      0 := by
  exact hasFDerivWithinAt_univ.1 (by simpa [HasTDerivAt, HasTDerivWithinAt] using hf.2)

omit [TopologicalSpace Y] in
theorem HasTDerivAt.tderiv (hf : HasTDerivAt f f' x) :
    tderiv 𝕜 f x = f' := by
  simpa [tderiv] using hf.hasFDerivAt_displacement.fderiv

omit [TopologicalSpace Y] in
theorem HasTDerivAt.continuousAt_displacement (hf : HasTDerivAt f f' x) :
    ContinuousAt (fun v : E => f (v +ᵥ x) -ᵥ f x) 0 :=
  hf.hasFDerivAt_displacement.continuousAt

theorem HasTDerivWithinAt.tDifferentiableWithinAt (hf : HasTDerivWithinAt f f' s x) :
    TDifferentiableWithinAt 𝕜 f s x :=
  ⟨f', hf⟩

theorem HasTDerivAt.tDifferentiableAt (hf : HasTDerivAt f f' x) :
    TDifferentiableAt 𝕜 f x :=
  ⟨f', hf⟩

theorem tDifferentiableAt_iff_tDifferentiableWithinAt_univ :
    TDifferentiableAt 𝕜 f x ↔ TDifferentiableWithinAt 𝕜 f Set.univ x :=
  Iff.rfl

omit [TopologicalSpace Y] in
theorem HasTDerivAt.unique {g' : E →L[𝕜] F}
    (hf : HasTDerivAt f f' x) (hg : HasTDerivAt f g' x) : f' = g' :=
  hf.hasFDerivAt_displacement.unique hg.hasFDerivAt_displacement

omit [TopologicalSpace Y] in
theorem HasTDerivAt.hasTDerivAt_tderiv (hf : HasTDerivAt f f' x) :
    HasTDerivAt f (FiberedAddTorsor.tderiv 𝕜 f x) x := by
  rw [hf.tderiv]
  exact hf

theorem TDifferentiableAt.hasTDerivAt_tderiv (hf : TDifferentiableAt 𝕜 f x) :
    HasTDerivAt f (FiberedAddTorsor.tderiv 𝕜 f x) x := by
  rcases hf with ⟨f', hf'⟩
  exact hf'.hasTDerivAt_tderiv

theorem TDifferentiableWithinAt.mono {t : Set X}
    (hf : TDifferentiableWithinAt 𝕜 f t x) (hst : s ⊆ t) :
    TDifferentiableWithinAt 𝕜 f s x := by
  rcases hf with ⟨f', hf'⟩
  exact ⟨f', hf'.mono hst⟩

theorem HasTDerivAt.continuousAt_vadd
    (hf : HasTDerivAt f f' x)
    (hvaddX : ContinuousAt (fun v : E => v +ᵥ x) (0 : E))
    (hvaddY : ContinuousAt (fun w : F => w +ᵥ f x) (0 : F)) :
    ContinuousAt (fun v : E => f (v +ᵥ x)) 0 := by
  let disp : E → F := fun v => f (v +ᵥ x) -ᵥ f x
  have hdisp0 : disp 0 = 0 := by
    dsimp [disp]
    simpa using (vadd_vsub (0 : F) (f x))
  have hvaddY' : ContinuousAt (fun w : F => w +ᵥ f x) (disp 0) := by
    rwa [hdisp0]
  have hcomp : ContinuousAt (fun v : E => disp v +ᵥ f x) 0 :=
    by simpa [Function.comp, disp] using hvaddY'.comp hf.continuousAt_displacement
  have hmap : Tendsto (fun v : E => v +ᵥ x) (𝓝 (0 : E)) (𝓝 x) := by
    change Tendsto (fun v : E => v +ᵥ x) (𝓝 (0 : E)) (𝓝 ((fun v : E => v +ᵥ x) 0)) at hvaddX
    simpa [zero_vadd] using hvaddX
  have hfiber0 : ∀ᶠ v in 𝓝 (0 : E), fiber (f (v +ᵥ x)) (f x) :=
    hmap.eventually hf.eventually_fiber
  have heq : (fun v : E => disp v +ᵥ f x) =ᶠ[𝓝 (0 : E)] fun v => f (v +ᵥ x) := by
    filter_upwards [hfiber0] with v hv
    dsimp [disp]
    exact vsub_vadd_of_fiber hv
  exact hcomp.congr heq

theorem HasTDerivAt.continuousAt_of_tendsto
    (hf : HasTDerivAt f f' x)
    (hdom : ∀ᶠ y in 𝓝 x, fiber y x)
    (hvsubX : Tendsto (fun y : X => y -ᵥ x) (𝓝 x) (𝓝 (0 : E)))
    (hvaddX : ContinuousAt (fun v : E => v +ᵥ x) (0 : E))
    (hvaddY : ContinuousAt (fun w : F => w +ᵥ f x) (0 : F)) :
    ContinuousAt f x := by
  have hchart := hf.continuousAt_vadd hvaddX hvaddY
  have hchartT : Tendsto (fun v : E => f (v +ᵥ x)) (𝓝 (0 : E)) (𝓝 (f x)) := by
    change Tendsto (fun v : E => f (v +ᵥ x)) (𝓝 (0 : E))
      (𝓝 ((fun v : E => f (v +ᵥ x)) 0)) at hchart
    simpa [zero_vadd] using hchart
  have hcomp : Tendsto (fun y : X => f ((y -ᵥ x) +ᵥ x)) (𝓝 x) (𝓝 (f x)) :=
    hchartT.comp hvsubX
  have heq : (fun y : X => f ((y -ᵥ x) +ᵥ x)) =ᶠ[𝓝 x] f := by
    filter_upwards [hdom] with y hy
    rw [vsub_vadd_of_fiber hy]
  exact hcomp.congr' heq

end Basic

section Rules

variable {𝕜 E F G X Y Z : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalFiberedAddTorsor E X] [TopologicalFiberedAddTorsor F Y]

theorem hasTDerivAt_const (y : Y) (x : X) :
    HasTDerivAt (fun _ : X => y) (0 : E →L[𝕜] F) x := by
  constructor
  · filter_upwards with z
    exact fiber_refl y
  · have hfun : (fun _ : E => y -ᵥ y) = fun _ : E => (0 : F) := by
      funext v
      simpa using (vadd_vsub (0 : F) y)
    rw [hfun]
    exact hasFDerivWithinAt_univ.2 (hasFDerivAt_const (𝕜 := 𝕜) (0 : F) (0 : E))

theorem tDifferentiableAt_const (y : Y) (x : X) :
    TDifferentiableAt (E := E) (F := F) 𝕜 (fun _ : X => y) x :=
  (hasTDerivAt_const y x).tDifferentiableAt

theorem hasTDerivAt_id (x : X) :
    HasTDerivAt (fun x : X => x)
      (ContinuousLinearMap.id 𝕜 E) x := by
  constructor
  · simpa [nhdsWithin_univ] using eventually_fiber_nhds (G := E) x
  · have hfun : (fun v : E => (v +ᵥ x) -ᵥ x) = fun v : E => v := by
      funext v
      exact vadd_vsub v x
    rw [hfun]
    exact hasFDerivWithinAt_univ.2 (hasFDerivAt_id 0)

theorem tdifferentiableAt_id (x : X) :
    TDifferentiableAt (E := E) (F := E) 𝕜 (fun x : X => x) x :=
  (hasTDerivAt_id (𝕜 := 𝕜) x).tDifferentiableAt

theorem hasTDerivAt_iff_comp_vadd {c : X → F} {c' : E →L[𝕜] F} {x : X} :
    HasTDerivAt (𝕜 := 𝕜) (E := E) (F := F) c c' x ↔
      HasFDerivAt (fun v : E => c (v +ᵥ x)) c' 0 := by
  constructor
  · intro h
    have hd : HasFDerivAt (fun v : E => c (v +ᵥ x) - c x) c' 0 := by
      exact hasFDerivWithinAt_univ.1 (by simpa [HasTDerivAt, HasTDerivWithinAt] using h.2)
    have hd' : HasFDerivAt (fun v : E => c (v +ᵥ x) + -(c x)) c' 0 := by
      simpa [sub_eq_add_neg] using hd
    exact (hasFDerivAt_add_const_iff (c := -(c x))).1 hd'
  · intro h
    constructor
    · filter_upwards with y
      trivial
    · have hd : HasFDerivAt (fun v : E => c (v +ᵥ x) - c x) c' 0 := by
        have hd' : HasFDerivAt (fun v : E => c (v +ᵥ x) + -(c x)) c' 0 :=
          (hasFDerivAt_add_const_iff (c := -(c x))).2 h
        simpa [sub_eq_add_neg] using hd'
      exact hasFDerivWithinAt_univ.2 hd

theorem hasTDerivAt_iff_hasFDerivAt {f : E → F} {f' : E →L[𝕜] F} {x : E} :
    HasTDerivAt (𝕜 := 𝕜) (E := E) (F := F) f f' x ↔ HasFDerivAt f f' x := by
  rw [hasTDerivAt_iff_comp_vadd]
  simpa [vadd_eq_add] using (hasFDerivAt_comp_add_right (f := f) (f' := f') (x := 0) x)

theorem HasTDerivAt.add {c d : X → F} {c' d' : E →L[𝕜] F} {x : X}
    (hc : HasTDerivAt (𝕜 := 𝕜) c c' x) (hd : HasTDerivAt (𝕜 := 𝕜) d d' x) :
    HasTDerivAt (𝕜 := 𝕜) (fun x => c x + d x) (c' + d') x := by
  rw [hasTDerivAt_iff_comp_vadd] at hc hd ⊢
  exact hc.add hd

theorem TDifferentiableAt.add {c d : X → F} {x : X}
    (hc : TDifferentiableAt (E := E) 𝕜 c x) (hd : TDifferentiableAt (E := E) 𝕜 d x) :
    TDifferentiableAt (E := E) 𝕜 (fun x => c x + d x) x := by
  rcases hc with ⟨c', hc'⟩
  rcases hd with ⟨d', hd'⟩
  exact ⟨c' + d', hc'.add hd'⟩

theorem HasTDerivAt.sub {c d : X → F} {c' d' : E →L[𝕜] F} {x : X}
    (hc : HasTDerivAt (𝕜 := 𝕜) c c' x) (hd : HasTDerivAt d d' x) :
    HasTDerivAt (𝕜 := 𝕜) (fun x => c x - d x) (c' - d') x := by
  rw [hasTDerivAt_iff_comp_vadd] at hc hd ⊢
  exact hc.sub hd

theorem TDifferentiableAt.sub {c d : X → F} {x : X}
    (hc : TDifferentiableAt 𝕜 c x) (hd : TDifferentiableAt 𝕜 d x) :
    TDifferentiableAt (E := E) 𝕜 (fun x => c x - d x) x := by
  rcases hc with ⟨c', hc'⟩
  rcases hd with ⟨d', hd'⟩
  exact ⟨c' - d', hc'.sub hd'⟩

theorem HasTDerivAt.neg {c : X → F} {c' : E →L[𝕜] F} {x : X}
    (hc : HasTDerivAt (𝕜 := 𝕜) c c' x) :
    HasTDerivAt (𝕜 := 𝕜) (fun x => -c x) (-c') x := by
  rw [hasTDerivAt_iff_comp_vadd] at hc ⊢
  exact hc.neg

theorem TDifferentiableAt.neg {c : X → F} {x : X}
    (hc : TDifferentiableAt (E := E) 𝕜 c x) :
    TDifferentiableAt (E := E) 𝕜 (fun x => -c x) x := by
  rcases hc with ⟨c', hc'⟩
  exact ⟨-c', hc'.neg⟩

theorem HasTDerivAt.const_smul {f : X → F} {f' : E →L[𝕜] F} {x : X}
    (hf : HasTDerivAt f f' x) (c : 𝕜) :
    HasTDerivAt (fun x => c • f x) (c • f') x := by
  rw [hasTDerivAt_iff_comp_vadd] at hf ⊢
  exact hf.const_smul c

theorem TDifferentiableAt.const_smul {f : X → F} {x : X}
    (hf : TDifferentiableAt 𝕜 f x) (c : 𝕜) :
    TDifferentiableAt 𝕜 (fun x => c • f x) x := by
  rcases hf with ⟨f', hf'⟩
  exact ⟨c • f', hf'.const_smul c⟩

theorem HasTDerivAt.smul_const {c : X → 𝕜} {c' : E →L[𝕜] 𝕜} {x : X}
    (hc : HasTDerivAt c c' x) (f : F) :
    HasTDerivAt (fun x => c x • f) (c'.smulRight f) x := by
  rw [hasTDerivAt_iff_comp_vadd] at hc ⊢
  exact hc.smul_const f

theorem TDifferentiableAt.smul_const {c : X → 𝕜} {x : X}
    (hc : TDifferentiableAt 𝕜 c x) (f : F) :
    TDifferentiableAt 𝕜 (fun x => c x • f) x := by
  rcases hc with ⟨c', hc'⟩
  exact ⟨c'.smulRight f, hc'.smul_const f⟩

theorem HasTDerivAt.smul {c : X → 𝕜} {f : X → F} {c' : E →L[𝕜] 𝕜} {f' : E →L[𝕜] F}
    {x : X} (hc : HasTDerivAt c c' x) (hf : HasTDerivAt f f' x) :
    HasTDerivAt (fun x => c x • f x) (c x • f' + c'.smulRight (f x)) x := by
  rw [hasTDerivAt_iff_comp_vadd] at hc hf ⊢
  simpa [zero_vadd] using hc.smul hf

theorem TDifferentiableAt.smul {c : X → 𝕜} {f : X → F} {x : X}
    (hc : TDifferentiableAt 𝕜 c x) (hf : TDifferentiableAt 𝕜 f x) :
    TDifferentiableAt 𝕜 (fun x => c x • f x) x := by
  rcases hc with ⟨c', hc'⟩
  rcases hf with ⟨f', hf'⟩
  exact ⟨c x • f' + c'.smulRight (f x), hc'.smul hf'⟩

theorem HasTDerivAt.sum {ι : Type*} {u : Finset ι} {A : ι → X → F}
    {A' : ι → E →L[𝕜] F} {x : X}
    (h : ∀ i ∈ u, HasTDerivAt (A i) (A' i) x) :
    HasTDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x := by
  rw [hasTDerivAt_iff_comp_vadd]
  simpa [zero_vadd] using
    (HasFDerivAt.fun_sum fun i hi => hasTDerivAt_iff_comp_vadd.1 (h i hi))

theorem HasTDerivAt.mul {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {c d : X → A} {c' d' : E →L[𝕜] A} {x : X}
    (hc : HasTDerivAt c c' x) (hd : HasTDerivAt d d' x) :
    HasTDerivAt (fun x => c x * d x) (c x • d' + d x • c') x := by
  rw [hasTDerivAt_iff_comp_vadd (F := A)] at hc hd ⊢
  simpa [zero_vadd] using hc.mul hd

theorem TDifferentiableAt.mul {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {c d : X → A} {x : X}
    (hc : TDifferentiableAt 𝕜 c x) (hd : TDifferentiableAt 𝕜 d x) :
    TDifferentiableAt 𝕜 (fun x => c x * d x) x := by
  rcases hc with ⟨c', hc'⟩
  rcases hd with ⟨d', hd'⟩
  exact ⟨c x • d' + d x • c', hc'.mul hd'⟩

theorem HasTDerivAt.comp_of_continuousAt
    {W : Type*} [TopologicalSpace W] [FiberedAddTorsor G W]
    {f : X → Y} {g : Y → W} {f' : E →L[𝕜] F} {g' : F →L[𝕜] G} {x : X}
    (hg : HasTDerivAt (𝕜 := 𝕜) g g' (f x))
    (hf : HasTDerivAt (𝕜 := 𝕜) f f' x)
    (hf_cont : ContinuousAt f x)
    (hvaddX : ContinuousAt (fun v : E => v +ᵥ x) (0 : E)) :
    HasTDerivAt (𝕜 := 𝕜) (fun x => g (f x)) (g'.comp f') x := by
  constructor
  · simpa [nhdsWithin_univ] using hf_cont.eventually hg.eventually_fiber
  · let Fdisp : E → F := fun v => f (v +ᵥ x) -ᵥ f x
    let Gdisp : F → G := fun w => g (w +ᵥ f x) -ᵥ g (f x)
    have hFdisp_zero : Fdisp 0 = 0 := by
      dsimp [Fdisp]
      simpa using (vadd_vsub (0 : F) (f x))
    have hg' : HasFDerivAt Gdisp g' (Fdisp 0) := by
      rw [hFdisp_zero]
      exact hg.hasFDerivAt_displacement
    have hcomp : HasFDerivAt (Gdisp ∘ Fdisp) (g'.comp f') 0 :=
      hg'.comp 0 hf.hasFDerivAt_displacement
    have hmap : Tendsto (fun v : E => v +ᵥ x) (𝓝 (0 : E)) (𝓝 x) := by
      change Tendsto (fun v : E => v +ᵥ x) (𝓝 (0 : E)) (𝓝 ((fun v : E => v +ᵥ x) 0)) at hvaddX
      simpa [zero_vadd] using hvaddX
    have hfiber0 : ∀ᶠ v in 𝓝 (0 : E), fiber (f (v +ᵥ x)) (f x) :=
      hmap.eventually hf.eventually_fiber
    have heq : (fun v : E => g (f (v +ᵥ x)) -ᵥ g (f x)) =ᶠ[𝓝 0] Gdisp ∘ Fdisp := by
      filter_upwards [hfiber0] with v hv
      dsimp [Fdisp, Gdisp, Function.comp]
      rw [vsub_vadd_of_fiber hv]
    exact hasFDerivWithinAt_univ.2 (hcomp.congr_of_eventuallyEq heq)

theorem HasTDerivAt.prodMk
    {W : Type*} [TopologicalSpace W] [TopologicalFiberedAddTorsor G W]
    {f : X → Y} {g : X → W} {f' : E →L[𝕜] F} {g' : E →L[𝕜] G} {x : X}
    (hf : HasTDerivAt (𝕜 := 𝕜) f f' x)
    (hg : HasTDerivAt (𝕜 := 𝕜) g g' x) :
    HasTDerivAt (fun x => (f x, g x)) (f'.prod g') x := by
  constructor
  · have h : ∀ᶠ y in 𝓝 x, fiber (f y, g y) (f x, g x) := by
      filter_upwards [hf.eventually_fiber, hg.eventually_fiber] with y hy hz
      exact ⟨hy, hz⟩
    simpa [nhdsWithin_univ] using h
  · have hfun :
      (fun v : E => (f (v +ᵥ x), g (v +ᵥ x)) -ᵥ (f x, g x)) =
        fun v : E => (f (v +ᵥ x) -ᵥ f x, g (v +ᵥ x) -ᵥ g x) := by
      funext v
      rfl
    rw [hfun]
    exact hasFDerivWithinAt_univ.2 (hf.hasFDerivAt_displacement.prodMk hg.hasFDerivAt_displacement)

theorem hasTDerivAt_fst
    (x : X × Y) :
    HasTDerivAt (Prod.fst : X × Y → X) (ContinuousLinearMap.fst 𝕜 E F) x := by
  constructor
  · simpa [nhdsWithin_univ] using
      (continuousAt_fst.eventually (eventually_fiber_nhds (G := E) x.1))
  · have hfun : (fun v : E × F => ((v +ᵥ x).1 -ᵥ x.1)) = fun v : E × F => v.1 := by
      funext v
      exact vadd_vsub v.1 x.1
    rw [hfun]
    exact hasFDerivWithinAt_univ.2 hasFDerivAt_fst

theorem hasTDerivAt_snd
    (x : X × Y) :
    HasTDerivAt (Prod.snd : X × Y → Y) (ContinuousLinearMap.snd 𝕜 E F) x := by
  constructor
  · simpa [nhdsWithin_univ] using
      (continuousAt_snd.eventually (eventually_fiber_nhds (G := F) x.2))
  · have hfun : (fun v : E × F => ((v +ᵥ x).2 -ᵥ x.2)) = fun v : E × F => v.2 := by
      funext v
      exact vadd_vsub v.2 x.2
    rw [hfun]
    exact hasFDerivWithinAt_univ.2 hasFDerivAt_snd

end Rules

section TopologicalRules

variable {𝕜 E F G X Y Z : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [TopologicalFiberedAddTorsor E X] [TopologicalFiberedAddTorsor F Y]
variable {f : X → Y} {f' : E →L[𝕜] F} {x : X}

theorem HasTDerivAt.continuousAt (hf : HasTDerivAt f f' x) :
    ContinuousAt f x :=
  hf.continuousAt_of_tendsto
    (eventually_fiber_nhds (G := E) x)
    (tendsto_vsub_nhds_zero (G := E) x)
    (continuousAt_vadd_const (G := E) x)
    (continuousAt_vadd_const (G := F) (f x))

theorem HasTDerivAt.comp
    [TopologicalFiberedAddTorsor G Z]
    {g : Y → Z} {g' : F →L[𝕜] G}
    (hg : HasTDerivAt (𝕜 := 𝕜) g g' (f x))
    (hf : HasTDerivAt (𝕜 := 𝕜) f f' x) :
    HasTDerivAt (𝕜 := 𝕜) (fun x => g (f x)) (g'.comp f') x :=
  hg.comp_of_continuousAt hf hf.continuousAt (continuousAt_vadd_const (G := E) x)

end TopologicalRules

section RealRules

variable {E F X : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [TopologicalSpace X] [TopologicalFiberedAddTorsor E X]
variable {f : X → F} {f' : E →L[ℝ] F} {x : X}

theorem HasTDerivAt.norm {g' : F →L[ℝ] ℝ}
    (hf : HasTDerivAt f f' x) (hnorm : HasFDerivAt (fun y : F => ‖y‖) g' (f x)) :
    HasTDerivAt (fun x => ‖f x‖) (g'.comp f') x := by
  have hnorm' : HasTDerivAt (fun y : F => ‖y‖) g' (f x) :=
    (hasTDerivAt_iff_hasFDerivAt (E := F) (F := ℝ)).2 hnorm
  simpa using hnorm'.comp hf

end RealRules

section RealInnerProductRules

variable {E F X : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [TopologicalSpace X] [TopologicalFiberedAddTorsor E X]
variable {f g : X → F} {f' g' : E →L[ℝ] F} {x : X}

theorem HasTDerivAt.inner (hf : HasTDerivAt f f' x) (hg : HasTDerivAt g g' x) :
    HasTDerivAt (fun x => inner (𝕜 := ℝ) (f x) (g x))
      ((fderivInnerCLM ℝ (f x, g x)).comp <| f'.prod g') x := by
  rw [hasTDerivAt_iff_comp_vadd] at hf hg ⊢
  simpa [zero_vadd] using hf.inner ℝ hg

theorem HasTDerivAt.norm_sq (hf : HasTDerivAt f f' x) :
    HasTDerivAt (fun x => ‖f x‖ ^ 2) (2 • (innerSL ℝ (f x)).comp f') x := by
  rw [hasTDerivAt_iff_comp_vadd] at hf ⊢
  simpa [zero_vadd] using hf.norm_sq

end RealInnerProductRules

end FiberedAddTorsor

end NumLean
