import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentSourceLimit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalDepletedDiffusionEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalDiffusionWeightLimit

/-!
# Actual alignment budget with unsmoothed depleted diffusion and source

Both auxiliary smoothing parameters are removed by spatial and temporal
dominated convergence. The fixed positive energy regularizer remains.
The diffusion weight is zero on separated aligned eigenlines and falls
back to full vorticity at top collisions. No all-scale closure is claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalLimitingDiffusionEnergy

open scoped Topology ComplexConjugate
open Filter MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierStrainGradient InfiniteConvectionEnergy
open PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks PancakeHigherLocalVelocity
open LocalAlignmentForcing LocalMeanAlignmentBalance LocalLimitingAlignmentSource
open SpectralAnisotropyLimit LocalAlignmentSourceLimit
open LocalAlignmentContinuity LocalDepletedAlignmentSource LocalDepletedDiffusionBudget
open LocalDiffusionWeightLimit

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem meanEnergy_add_integral_residual_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
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
      (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes u₀ delta +
        (∫ τ in (0 : ℝ)..t, ∫ x : T3, limitingDiffusionCost chi modes (s.coefficients τ) delta nu x) +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, limitingForcingEnvelope chi modes outputs (s.coefficients τ) delta x := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hlimD := (intervalIntegrable_and_tendsto_integral_cost s hnu.le g hSum hu2 chi modes delta hd t ht).2
  have hlimR := (intervalIntegrable_and_tendsto_integral_source s g hg hSum hu2 chi C hchi
    modes outputs delta t ht).2
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds ((tendsto_const_nhds.add hlimD).add hlimR)
  intro n
  have hsubI : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hD : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      diffusionCost chi modes (s.coefficients τ) delta (approximationParameter n) nu x) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_spatialIntegral _
      (continuous_diffusionCost_spaceTime s g hSum hu2 chi modes delta
        (approximationParameter n) (approximationParameter_pos n))).mono hsubI)
  have hR : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      depletedForcingEnvelope chi modes outputs (s.coefficients τ) delta (approximationParameter n) x) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_spatialIntegral _
      (continuous_depletedForcingEnvelope_spaceTime s g hg hSum hu2 chi C hchi modes outputs delta
        (approximationParameter n) (approximationParameter_pos n))).mono hsubI)
  have hsplit : (∫ τ in (0 : ℝ)..t, ∫ x : T3,
      LocalDepletedDiffusionEnergy.budgetSource chi modes outputs (s.coefficients τ) delta
        (approximationParameter n) (approximationParameter n) nu x) =
      (∫ τ in (0 : ℝ)..t, ∫ x : T3,
        diffusionCost chi modes (s.coefficients τ) delta (approximationParameter n) nu x) +
      (∫ τ in (0 : ℝ)..t, ∫ x : T3,
        depletedForcingEnvelope chi modes outputs (s.coefficients τ) delta (approximationParameter n) x) := by
    rw [← intervalIntegral.integral_add hD hR]
    apply intervalIntegral.integral_congr
    intro τ hτ
    have hτ' : τ ∈ Set.Icc (0 : ℝ) T := hsubI (by simpa only [Set.uIcc_of_le ht.1] using hτ)
    have hm1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτ'))
    exact integral_add
      ((continuous_diffusionCost chi modes _ hm1 delta _ nu
        (approximationParameter_pos n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((continuous_depletedForcingEnvelope chi modes outputs _ hm1 delta _
        (approximationParameter_pos n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have h := LocalDepletedDiffusionEnergy.meanEnergy_add_integral_residual_le_initial
    s hnu hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd
    (approximationParameter n) (approximationParameter_pos n)
    (approximationParameter n) (approximationParameter_pos n) hT t ht
  simpa only [hsplit, add_assoc] using h

/-- A single local solution for every admissible finite strain filter,
with both auxiliary smoothing parameters removed from the conclusion. -/
theorem exists_physical_localLimitingDiffusionEnergy (nu : ℝ) (hnu : 0 < nu)
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
        (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes (torusFourierVelocity f) delta +
        (∫ τ in (0 : ℝ)..t, ∫ x : T3, limitingDiffusionCost chi modes (s.coefficients τ) delta nu x) +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, limitingForcingEnvelope chi modes outputs (s.coefficients τ) delta x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd t ht
  exact meanEnergy_add_integral_residual_le_initial s hnu hT hB g hg hSum hu chi C hchi modes outputs
    hcut hchir hsub hout hs hk delta hd t ht

end Mettapedia.FluidDynamics.NavierStokes.LocalLimitingDiffusionEnergy
