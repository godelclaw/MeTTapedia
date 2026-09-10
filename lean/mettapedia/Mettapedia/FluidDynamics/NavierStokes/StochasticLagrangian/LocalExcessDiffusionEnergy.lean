import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalLimitingDiffusionEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralDiffusionExcess
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Local alignment energy with only excess diffusion on the right

Half the coherent spectral residual pays the local diffusion cost wherever
the squared top gap dominates the strain-gradient density. Only the positive
excess is retained elsewhere. The excess is measurable and integrable on
each constructed local solution window, including top-eigenvalue collisions.
No uniform control of its integral across filters or maximal times is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalExcessDiffusionEnergy

open scoped ComplexConjugate
open Filter MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierStrainGradient InfiniteConvectionEnergy
open PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks PancakeHigherLocalVelocity
open LocalAlignmentForcing LocalMeanAlignmentBalance LocalLimitingAlignmentSource
open LocalAlignmentContinuity LocalDiffusionWeightLimit LocalLowDiffusionBudget
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics LocalSpatialSpectralBounds
open LocalStrainGradientDensity PancakeMeasurableMaterialRate
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def excessCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) : ℝ :=
  SpectralDiffusionExcess.excess (spatialStrain modes (filteredVelocity chi u) x)
    (fullVorticity u x) ((16 * nu / delta) * strainGradientSquare chi modes u x)

theorem excessCost_nonneg (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) : 0 ≤ excessCost chi modes u delta nu x :=
  SpectralDiffusionExcess.excess_nonneg _ _ _

theorem excessCost_le_limitingDiffusionCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu) (x : T3) :
    excessCost chi modes u delta nu x ≤ limitingDiffusionCost chi modes u delta nu x :=
  SpectralDiffusionExcess.excess_le_cost _ _ _
    (mul_nonneg (by positivity) (strainGradientSquare_nonneg chi modes u x))

theorem limitingDiffusionCost_le_half_residual_add_excessCost (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (delta nu : ℝ) (x : T3) :
    limitingDiffusionCost chi modes u delta nu x ≤
      ‖residual chi modes u x‖ ^ 2 / 2 + excessCost chi modes u delta nu x :=
  SpectralDiffusionExcess.cost_le_half_residual_add_excess _ _ _

theorem excessCost_eq_zero_of_gap_dominates (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (hd : 0 < delta) (x : T3)
    (h : 32 * nu * strainGradientSquare chi modes u x ≤
      delta * topGap (spatialStrain modes (filteredVelocity chi u) x) ^ 2) :
    excessCost chi modes u delta nu x = 0 := by
  apply SpectralDiffusionExcess.excess_eq_zero_of_le
  have h' : 32 * nu * strainGradientSquare chi modes u x / delta ≤
      topGap (spatialStrain modes (filteredVelocity chi u) x) ^ 2 :=
    (div_le_iff₀ hd).mpr (by nlinarith only [h])
  convert h' using 1; ring

theorem excessCost_eq_zero_of_aligned (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta nu c : ℝ) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x))
    (hw : fullVorticity u x = c • PancakeSpectralFiniteDifference.topVector
      (spatialStrain modes (filteredVelocity chi u) x)) :
    excessCost chi modes u delta nu x = 0 := by
  unfold excessCost SpectralDiffusionExcess.excess
  rw [hw, SpectralDiffusionWeightLimit.limitingWeight_aligned _ c hg, mul_zero]

theorem excessCost_eq_full_cost_of_topGap_zero (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu) (x : T3)
    (hg : topGap (spatialStrain modes (filteredVelocity chi u) x) = 0) :
    excessCost chi modes u delta nu x =
      (16 * nu / delta) * strainGradientSquare chi modes u x * ‖fullVorticity u x‖ ^ 2 :=
  SpectralDiffusionExcess.excess_eq_cost_of_topGap_zero _ _ _
    (mul_nonneg (by positivity) (strainGradientSquare_nonneg chi modes u x)) hg

theorem measurable_excessCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta nu : ℝ) :
    Measurable (excessCost chi modes u delta nu) :=
  SpectralDiffusionExcess.measurable_excess _ _ _
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_fullVorticity u hu) ((continuous_strainGradientSquare chi modes u).const_mul _)

theorem integrable_excessCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu) :
    Integrable (excessCost chi modes u delta nu) := by
  apply (integrable_limitingDiffusionCost chi modes u hu delta nu).mono'
    (measurable_excessCost chi modes u hu delta nu).aestronglyMeasurable
  exact Eventually.of_forall (fun x ↦ by
    rw [Real.norm_of_nonneg (excessCost_nonneg chi modes u delta nu x)]
    exact excessCost_le_limitingDiffusionCost chi modes u delta nu hd hnu x)

theorem integral_excessCost_le_limitingDiffusionCost (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu) :
    (∫ x : T3, excessCost chi modes u delta nu x) ≤
      ∫ x : T3, limitingDiffusionCost chi modes u delta nu x :=
  integral_mono (integrable_excessCost chi modes u hu delta nu hd hnu)
    (integrable_limitingDiffusionCost chi modes u hu delta nu)
    (excessCost_le_limitingDiffusionCost chi modes u delta nu hd hnu)

theorem measurable_excessCost_spaceTime {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (g : Wavevector → ℝ) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (delta : ℝ) :
    Measurable (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      excessCost chi modes (s.coefficients z.1) delta nu z.2) := by
  have hc (q : Wavevector) (i : Fin 3) :
      Continuous (fun τ : Set.Icc (0 : ℝ) T ↦ s.coefficients τ q i) :=
    (s.continuous q i).comp continuous_subtype_val
  exact SpectralDiffusionExcess.measurable_excess _ _ _
    (continuous_parametric_strain modes chi (fun τ : Set.Icc (0 : ℝ) T ↦
      s.coefficients τ) (fun q _ i ↦ hc q i))
    (continuous_fullVorticity_spaceTime s g hSum hu)
    ((continuous_parametric_strainGradientSquare chi modes
      (fun τ : Set.Icc (0 : ℝ) T ↦ s.coefficients τ) (fun q _ i ↦ hc q i)).const_mul _)

theorem intervalIntegrable_excessCost {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 ≤ nu)
    (g : Wavevector → ℝ) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (delta : ℝ) (hd : 0 < delta)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ ∫ x : T3,
      excessCost chi modes (s.coefficients τ) delta nu x) volume 0 t := by
  have hm := (measurable_excessCost_spaceTime s g hSum hu chi modes delta).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure T3))
  have hmr : AEStronglyMeasurable (fun τ ↦ ∫ x : T3,
      excessCost chi modes (s.coefficients τ) delta nu x) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ((aemeasurable_restrict_iff_comap_subtype measurableSet_Icc).mpr hm.measurable.aemeasurable).aestronglyMeasurable
  have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := by
    rw [Set.uIoc_of_le ht.1]
    exact fun _ hτ ↦ ⟨hτ.1.le, hτ.2.trans ht.2⟩
  apply (intervalIntegrable_and_tendsto_integral_cost s hnu g hSum hu chi modes delta hd t ht).1.mono_fun'
    (hmr.mono_measure (Measure.restrict_mono hsub le_rfl))
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
  rw [Real.norm_of_nonneg (integral_nonneg (excessCost_nonneg chi modes _ delta nu))]
  exact integral_excessCost_le_limitingDiffusionCost chi modes _
    (summable_fourierMoment_of_le _ (by omega : 1 ≤ 2)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ)))) delta nu hd hnu

theorem integral_limitingDiffusionCost_le_half_residual_add_excessCost
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu) :
    (∫ x : T3, limitingDiffusionCost chi modes u delta nu x) ≤
      (1 / 2 : ℝ) * (∫ x : T3, ‖residual chi modes u x‖ ^ 2) +
      ∫ x : T3, excessCost chi modes u delta nu x := by
  have hr : Integrable (fun x : T3 ↦ ‖residual chi modes u x‖ ^ 2) :=
    ((continuous_residual chi modes u hu).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := integrable_excessCost chi modes u hu delta nu hd hnu
  have h := integral_mono (integrable_limitingDiffusionCost chi modes u hu delta nu)
    ((hr.const_mul (1 / 2 : ℝ)).add he) (fun x ↦ by
      simpa only [Pi.add_apply, div_eq_mul_inv, one_div, one_mul, mul_comm] using
        limitingDiffusionCost_le_half_residual_add_excessCost chi modes u delta nu x)
  change (∫ x : T3, limitingDiffusionCost chi modes u delta nu x) ≤
    ∫ x : T3, (1 / 2 : ℝ) * ‖residual chi modes u x‖ ^ 2 + excessCost chi modes u delta nu x at h
  rw [integral_add (hr.const_mul (1 / 2 : ℝ)) he, integral_const_mul] at h
  exact h

theorem integral_cost_le_half_residual_add_excess {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 ≤ nu)
    (g : Wavevector → ℝ) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (delta : ℝ) (hd : 0 < delta)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, ∫ x : T3, limitingDiffusionCost chi modes (s.coefficients τ) delta nu x) ≤
      (1 / 2 : ℝ) * (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) +
      ∫ τ in (0 : ℝ)..t, ∫ x : T3, excessCost chi modes (s.coefficients τ) delta nu x := by
  have hr := intervalIntegrable_residual_sq s g hSum hu chi modes t ht
  have he := intervalIntegrable_excessCost s hnu g hSum hu chi modes delta hd t ht
  have hc := (intervalIntegrable_and_tendsto_integral_cost s hnu g hSum hu chi modes delta hd t ht).1
  have h := intervalIntegral.integral_mono_on ht.1 hc ((hr.const_mul (1 / 2 : ℝ)).add he)
    (fun τ hτ ↦ integral_limitingDiffusionCost_le_half_residual_add_excessCost chi modes _
      (summable_fourierMoment_of_le _ (by omega : 1 ≤ 2)
        (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ ⟨hτ.1, hτ.2.trans ht.2⟩))) delta nu hd hnu)
  simpa only [intervalIntegral.integral_add (hr.const_mul (1 / 2 : ℝ)) he,
    intervalIntegral.integral_const_mul] using h

theorem meanEnergy_add_half_integral_residual_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu) (hT : 0 < T) (hB : 0 ≤ B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (delta : ℝ) (hd : 0 < delta) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanEnergy chi modes (s.coefficients t) delta +
      (1 / 2 : ℝ) * (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes u₀ delta +
        (∫ τ in (0 : ℝ)..t, ∫ x : T3, excessCost chi modes (s.coefficients τ) delta nu x) +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, limitingForcingEnvelope chi modes outputs (s.coefficients τ) delta x := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hE := LocalLimitingDiffusionEnergy.meanEnergy_add_integral_residual_le_initial
    s hnu hT hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd t ht
  have hC := integral_cost_le_half_residual_add_excess s hnu.le g hSum hu2 chi modes delta hd t ht
  linarith only [hE, hC]

/-- One actual solution simultaneously satisfies the excess-only diffusion
budget for every admissible finite filter. No spectral gap is assumed. -/
theorem exists_physical_localExcessDiffusionEnergy (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hdiv : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
      ∀ (chi : Wavevector → ℂ) (C : ℝ), (∀ q, ‖chi q‖ ≤ C) →
      ∀ modes outputs : Finset Wavevector, (∀ q, q ∉ modes → chi q = 0) →
      (∀ q, chi (-q) = conj (chi q)) → modes ⊆ outputs →
      (∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs) →
      (∀ k, -k ∈ modes ↔ k ∈ modes) → (∀ k ∈ modes, frequencyVec k ≠ 0) →
      ∀ delta > (0 : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) T,
      meanEnergy chi modes (s.coefficients t) delta +
        (1 / 2 : ℝ) * (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes (torusFourierVelocity f) delta +
        (∫ τ in (0 : ℝ)..t, ∫ x : T3, excessCost chi modes (s.coefficients τ) delta nu x) +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, limitingForcingEnvelope chi modes outputs (s.coefficients τ) delta x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd t ht
  exact meanEnergy_add_half_integral_residual_le_initial s hnu hT hB g hg hSum hu chi C hchi modes outputs
    hcut hchir hsub hout hs hk delta hd t ht

end Mettapedia.FluidDynamics.NavierStokes.LocalExcessDiffusionEnergy
