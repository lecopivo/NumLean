module

public import Mathlib.Topology.Algebra.Group.Basic
public import NumLean.Mathlib.FiberedAddTorsor.Prod

@[expose] public section

namespace NumLean

open Filter
open scoped Topology

namespace FiberedAddTorsor

/-- Compatibility between the topologies on a fibered additive torsor and its model group. -/
class TopologicalFiberedAddTorsor (G : outParam Type*) (P : Type*)
    [AddGroup G] [TopologicalSpace G] [TopologicalSpace P]
    extends FiberedAddTorsor G P where
  continuous_vadd : Continuous fun gp : G × P => gp.1 +ᵥ gp.2
  continuous_vsub : Continuous fun pp : P × P => pp.1 -ᵥ pp.2
  eventually_fiber_nhds : ∀ p : P, ∀ᶠ q in 𝓝 p, fiber q p

section Basic

variable {G P : Type*} [AddGroup G] [TopologicalSpace G] [TopologicalSpace P]
variable [TopologicalFiberedAddTorsor G P]

theorem continuous_vadd : Continuous fun gp : G × P => gp.1 +ᵥ gp.2 :=
  TopologicalFiberedAddTorsor.continuous_vadd

theorem continuous_vsub : Continuous fun pp : P × P => pp.1 -ᵥ pp.2 :=
  TopologicalFiberedAddTorsor.continuous_vsub

theorem eventually_fiber_nhds (p : P) : ∀ᶠ q in 𝓝 p, fiber q p :=
  TopologicalFiberedAddTorsor.eventually_fiber_nhds p

theorem continuousAt_vadd (g : G) (p : P) :
    ContinuousAt (fun gp : G × P => gp.1 +ᵥ gp.2) (g, p) :=
  continuous_vadd.continuousAt

theorem continuousAt_vsub (p q : P) :
    ContinuousAt (fun pp : P × P => pp.1 -ᵥ pp.2) (p, q) :=
  continuous_vsub.continuousAt

theorem continuousAt_vadd_const (p : P) :
    ContinuousAt (fun g : G => g +ᵥ p) (0 : G) := by
  have hinner : ContinuousAt (fun g : G => ((g, p) : G × P)) (0 : G) :=
    (continuousAt_id : ContinuousAt (fun g : G => g) 0).prodMk continuousAt_const
  have hvadd : ContinuousAt (fun gp : G × P => gp.1 +ᵥ gp.2) ((0 : G), p) :=
    (TopologicalFiberedAddTorsor.continuous_vadd (G := G) (P := P)).continuousAt
  simpa [Function.comp_def] using
    ContinuousAt.comp
      (g := fun gp : G × P => gp.1 +ᵥ gp.2)
      (f := fun g : G => ((g, p) : G × P)) hvadd hinner

theorem tendsto_vsub_nhds_zero (p : P) :
    Tendsto (fun q : P => q -ᵥ p) (𝓝 p) (𝓝 (0 : G)) := by
  have hinner : ContinuousAt (fun q : P => ((q, p) : P × P)) p :=
    (continuousAt_id : ContinuousAt (fun q : P => q) p).prodMk continuousAt_const
  have hvsub : ContinuousAt (fun q : P => q -ᵥ p) p := by
    have hvsub' : ContinuousAt (fun pp : P × P => pp.1 -ᵥ pp.2) (p, p) :=
      (TopologicalFiberedAddTorsor.continuous_vsub (G := G) (P := P)).continuousAt
    simpa [Function.comp_def] using
      ContinuousAt.comp
        (g := fun pp : P × P => pp.1 -ᵥ pp.2)
        (f := fun q : P => ((q, p) : P × P)) hvsub' hinner
  have hzero : p -ᵥ p = (0 : G) := by
    simpa using (vadd_vsub (0 : G) p)
  change Tendsto (fun q : P => q -ᵥ p) (𝓝 p) (𝓝 ((fun q : P => q -ᵥ p) p)) at hvsub
  simpa [hzero] using hvsub

end Basic

section Instances

instance {G} [AddGroup G] [TopologicalSpace G] [ContinuousAdd G] [ContinuousSub G] :
    TopologicalFiberedAddTorsor G G where
  continuous_vadd := by simpa [vadd_eq_add] using continuous_add
  continuous_vsub := by simpa [vsub_eq_sub] using continuous_sub
  eventually_fiber_nhds := by
    intro p
    filter_upwards with q
    trivial

instance {G H P Q} [AddGroup G] [AddGroup H]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace P] [TopologicalSpace Q]
    [TopologicalFiberedAddTorsor G P] [TopologicalFiberedAddTorsor H Q] :
    TopologicalFiberedAddTorsor (G × H) (P × Q) where
  continuous_vadd := by
    change Continuous fun gp : (G × H) × (P × Q) =>
      (gp.1.1 +ᵥ gp.2.1, gp.1.2 +ᵥ gp.2.2)
    exact
      ((continuous_vadd (G := G) (P := P)).comp
          ((continuous_fst.fst).prodMk continuous_snd.fst)).prodMk
        ((continuous_vadd (G := H) (P := Q)).comp
          ((continuous_fst.snd).prodMk continuous_snd.snd))
  continuous_vsub := by
    change Continuous fun pp : (P × Q) × (P × Q) =>
      (pp.1.1 -ᵥ pp.2.1, pp.1.2 -ᵥ pp.2.2)
    exact
      ((continuous_vsub (G := G) (P := P)).comp
          ((continuous_fst.fst).prodMk continuous_snd.fst)).prodMk
        ((continuous_vsub (G := H) (P := Q)).comp
          ((continuous_fst.snd).prodMk continuous_snd.snd))
  eventually_fiber_nhds := by
    intro p
    filter_upwards [
      (continuousAt_fst.eventually (eventually_fiber_nhds (G := G) p.1)),
      (continuousAt_snd.eventually (eventually_fiber_nhds (G := H) p.2))]
      with q hq₁ hq₂
    exact ⟨hq₁, hq₂⟩

end Instances

end FiberedAddTorsor

end NumLean
