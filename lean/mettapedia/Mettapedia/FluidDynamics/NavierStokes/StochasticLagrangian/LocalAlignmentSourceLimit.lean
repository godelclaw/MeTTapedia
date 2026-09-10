import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalLimitingAlignmentSource

/-!
# Dominated passage to the limiting source on a local time interval

Spatial convergence is followed by time convergence under one continuous
absolute majorant. The limiting mean is proved interval-integrable; its
continuity at eigenvalue collisions is neither assumed nor needed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentSourceLimit

open scoped Topology
open Filter MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open LocalAlignmentContinuity LocalDepletedAlignmentSource LocalLimitingAlignmentSource
open SpectralAnisotropyLimit

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem intervalIntegrable_and_tendsto_integral_source {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (delta : ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ ∫ x : T3,
      limitingForcingEnvelope chi modes outputs (s.coefficients τ) delta x) volume 0 t ∧
    Tendsto (fun n ↦ ∫ τ in (0 : ℝ)..t, ∫ x : T3,
      depletedForcingEnvelope chi modes outputs (s.coefficients τ) delta (approximationParameter n) x)
      atTop (𝓝 (∫ τ in (0 : ℝ)..t, ∫ x : T3,
        limitingForcingEnvelope chi modes outputs (s.coefficients τ) delta x)) := by
  let F := fun n τ ↦ ∫ x : T3,
    depletedForcingEnvelope chi modes outputs (s.coefficients τ) delta (approximationParameter n) x
  let f := fun τ ↦ ∫ x : T3, limitingForcingEnvelope chi modes outputs (s.coefficients τ) delta x
  let bound := fun τ ↦ ∫ x : T3, absoluteSourceBound chi modes outputs (s.coefficients τ) delta x
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hu1 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) : Summable (fourierMoment 1 (s.coefficients τ)) :=
    summable_fourierMoment_of_le _ (by omega : 1 ≤ 2)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ)))
  have hBx (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) :
      Integrable (absoluteSourceBound chi modes outputs (s.coefficients τ) delta) :=
    (continuous_absoluteSourceBound chi modes outputs _ (hu1 τ hτ) delta).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB : IntervalIntegrable bound volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_spatialIntegral _
      (continuous_absoluteSourceBound_spaceTime s g hg hSum hu chi C hchi modes outputs delta)).mono hsub)
  have hF (n : ℕ) : IntervalIntegrable (F n) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_spatialIntegral _
      (continuous_depletedForcingEnvelope_spaceTime s g hg hSum hu chi C hchi modes outputs delta
        (approximationParameter n) (approximationParameter_pos n))).mono hsub)
  have hlim (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) : Tendsto (fun n ↦ F n τ) atTop (𝓝 (f τ)) :=
    tendsto_integral_depletedForcingEnvelope chi modes outputs _ (hu1 τ hτ) delta
  have hbound (n : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) : ‖F n τ‖ ≤ bound τ :=
    norm_integral_le_of_norm_le (hBx τ hτ)
      (Eventually.of_forall (norm_depletedForcingEnvelope_le chi modes outputs _ delta (approximationParameter n)))
  have hfbound (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) : ‖f τ‖ ≤ bound τ :=
    norm_integral_le_of_norm_le (hBx τ hτ)
      (Eventually.of_forall (norm_limitingForcingEnvelope_le chi modes outputs _ delta))
  have hmem : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) t := by
    rw [Set.uIoc_of_le ht.1]
    exact Set.Ioc_subset_Icc_self
  have hm : AEStronglyMeasurable f (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦ (hF n).def'.1) (by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
      exact hlim τ (hmem hτ))
  refine ⟨hB.mono_fun' hm ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
    exact hfbound τ (hmem hτ)
  · exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
      (Eventually.of_forall (fun n ↦ (hF n).def'.1))
      (Eventually.of_forall (fun n ↦ Eventually.of_forall (fun τ hτ ↦ hbound n τ (hmem hτ)))) hB
      (Eventually.of_forall (fun τ hτ ↦ hlim τ (hmem hτ)))

end Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentSourceLimit
