import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalDepletedDiffusionBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalDepletedAlignmentBudget

/-!
# Actual initial-data alignment energy with depleted diffusion

The collision-safe weak diffusion bound is integrated on the actual local
solution, retaining its capped alignment weight. Spectral almost-everywhere
differentiability, transport cancellation, and the time fundamental theorem
are proved upstream, not supplied as assumptions. All three positive
regularizers are independent. No cutoff-uniform global bound is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalDepletedDiffusionEnergy

open scoped ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierStrainGradient InfiniteConvectionEnergy
open PancakeGalerkinKineticEnergy PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open PancakeHigherLocalVelocity
open LocalAlignmentForcing LocalAlignmentContinuity LocalMeanAlignmentBalance
open LocalDepletedAlignmentSource LocalDepletedDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def budgetSource (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta epsilon eta nu : ℝ) (x : T3) : ℝ :=
  diffusionCost chi modes u delta epsilon nu x + depletedForcingEnvelope chi modes outputs u delta eta x

theorem continuous_budgetSource_spaceTime {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (delta epsilon eta : ℝ) (heps : 0 < epsilon) (heta : 0 < eta) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      budgetSource chi modes outputs (s.coefficients z.1) delta epsilon eta nu z.2) :=
  (continuous_diffusionCost_spaceTime s g hSum hu chi modes delta epsilon heps).add
    (continuous_depletedForcingEnvelope_spaceTime s g hg hSum hu chi C hchi modes outputs delta eta heta)

section Solution

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
  (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
  (hchir : ∀ q, chi (-q) = conj (chi q))
  (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
  (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
  (delta : ℝ) (hd : 0 < delta) (epsilon : ℝ) (heps : 0 < epsilon) (eta : ℝ) (heta : 0 < eta)

include hnu hB hg hSum hu hchi hcut hchir hsub hout hs hk hd heps heta

theorem meanEnergy_add_integral_residual_le
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    meanEnergy chi modes (s.coefficients b) delta +
      (∫ τ in a..b, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes (s.coefficients a) delta +
        ∫ τ in a..b, ∫ x : T3, budgetSource chi modes outputs (s.coefficients τ) delta epsilon eta nu x := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hsubI : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T :=
    fun _ hτ ↦ Set.Ioo_subset_Icc_self (hI hτ)
  have hR : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      budgetSource chi modes outputs (s.coefficients τ) delta epsilon eta nu x) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((continuousOn_spatialIntegral _
      (continuous_budgetSource_spaceTime s g hg hSum hu2 chi C hchi modes outputs delta epsilon eta heps heta)).mono hsubI)
  have hz : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      ‖residual chi modes (s.coefficients τ) x‖ ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((continuousOn_spatialIntegral _
      ((continuous_residual_spaceTime s g hSum hu2 chi modes).norm.pow 2)).mono hsubI)
  obtain ⟨hf, hbalance⟩ := LocalAlignmentEnergyBudget.intervalIntegral_materialRate_eq_energy
    s hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta a b hab hI
  have hdom : ∀ᵐ τ ∂volume.restrict (Set.Ioo a b),
      (∫ x : T3, materialRate chi modes outputs (s.coefficients τ) delta nu x) +
        (∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
        ∫ x : T3, budgetSource chi modes outputs (s.coefficients τ) delta epsilon eta nu x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      LocalAlignmentEnergyBudget.ae_integrable_materialRate s hB g hg hSum hu chi C hchi modes outputs
        hcut hchir hsub hout hs hk delta a b hab hI] with τ hτ hF
    have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
      (hu τ (hsubI (Set.Ioo_subset_Icc_self hτ)))
    have hm1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hm
    have hD : Integrable (diffusionCost chi modes (s.coefficients τ) delta epsilon nu) :=
      (continuous_diffusionCost chi modes _ hm1 delta epsilon nu heps).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have hN : Integrable (depletedForcingEnvelope chi modes outputs (s.coefficients τ) delta eta) :=
      (continuous_depletedForcingEnvelope chi modes outputs _ hm1 delta eta heta).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    simpa only [budgetSource, integral_add hD hN] using
      LocalDepletedDiffusionBudget.integral_materialRate_add_residual_le chi modes outputs _ hm
        delta epsilon eta nu hd heps heta hnu.le hF
  rw [restrict_Ioo_eq_restrict_Icc] at hdom
  have h := intervalIntegral.integral_mono_ae_restrict hab (hf.add hz) hR hdom
  rw [intervalIntegral.integral_add hf hz, hbalance] at h
  linarith

theorem meanEnergy_add_integral_residual_le_initial (hT : 0 < T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanEnergy chi modes (s.coefficients t) delta +
      (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes u₀ delta +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, budgetSource chi modes outputs (s.coefficients τ) delta epsilon eta nu x := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hA : ContinuousOn (fun τ ↦ meanEnergy chi modes (s.coefficients τ) delta) (Set.Icc 0 T) :=
    continuousOn_spatialIntegral _ (continuous_alignmentEnergy_spaceTime s g hSum hu2 chi modes delta)
  have hZ : ContinuousOn (fun τ ↦ ∫ x : T3,
      ‖residual chi modes (s.coefficients τ) x‖ ^ 2) (Set.Icc 0 T) :=
    continuousOn_spatialIntegral _ ((continuous_residual_spaceTime s g hSum hu2 chi modes).norm.pow 2)
  have hR : ContinuousOn (fun τ ↦ ∫ x : T3,
      budgetSource chi modes outputs (s.coefficients τ) delta epsilon eta nu x) (Set.Icc 0 T) :=
    continuousOn_spatialIntegral _
      (continuous_budgetSource_spaceTime s g hg hSum hu2 chi C hchi modes outputs delta epsilon eta heps heta)
  have h := intervalIntegral.endpoint_estimate_of_interior (C := 0) hT hA hZ hR
    (fun a b ha hab hb ↦ by
      simpa only [add_zero] using meanEnergy_add_integral_residual_le
        s hnu hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd epsilon heps eta heta a b hab.le
        (fun _ hτ ↦ ⟨ha.trans_le hτ.1, hτ.2.trans_lt hb⟩)) t ht
  simpa only [s.initial, add_zero] using h

end Solution

/-- One physical local solution supplies the estimate for all admissible
finite filters, positive regularizers, and times in its closed window. -/
theorem exists_physical_localDepletedDiffusionEnergy (nu : ℝ) (hnu : 0 < nu)
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
      ∀ delta > (0 : ℝ), ∀ epsilon > (0 : ℝ), ∀ eta > (0 : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) T,
      meanEnergy chi modes (s.coefficients t) delta +
        (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes (torusFourierVelocity f) delta +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, budgetSource chi modes outputs (s.coefficients τ) delta epsilon eta nu x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd epsilon heps eta heta t ht
  exact meanEnergy_add_integral_residual_le_initial s hnu hB g hg hSum hu chi C hchi modes outputs
    hcut hchir hsub hout hs hk delta hd epsilon heps eta heta hT t ht

end Mettapedia.FluidDynamics.NavierStokes.LocalDepletedDiffusionEnergy
