import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalDepletedAlignmentSource

/-!
# Initial-data alignment budget with the depleted nonlinear source

The continuous scalar anisotropy envelope is integrated on the actual
local solution. Spectral differentiability and the material-rate identity
are already proved almost everywhere; neither is assumed here. The new
source is no larger than the coarse signed source, but its scale-uniform
time control and global continuation remain separate obligations.
Source smoothing and the energy regularizer are independent parameters.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalDepletedAlignmentBudget

open scoped ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierStrainGradient InfiniteConvectionEnergy
open PancakeGalerkinKineticEnergy PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open PancakeHigherLocalVelocity
open LocalAlignmentForcing LocalAlignmentContinuity LocalMeanAlignmentBalance
open LocalDepletedAlignmentSource

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

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
  (delta : ℝ) (hd : 0 < delta)
  (epsilon : ℝ) (heps : 0 < epsilon)

include hnu hB hg hSum hu hchi hcut hchir hsub hout hs hk hd heps

theorem meanEnergy_add_integral_residual_le
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    meanEnergy chi modes (s.coefficients b) delta +
      (∫ τ in a..b, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes (s.coefficients a) delta +
        4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta +
        ∫ τ in a..b, ∫ x : T3, depletedForcingEnvelope chi modes outputs (s.coefficients τ) delta epsilon x := by
  have ha := (hI (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)).1.le
  have hb := (hI (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩)).2.le
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hsubI : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T :=
    fun _ hτ ↦ Set.Ioo_subset_Icc_self (hI hτ)
  have hR : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      depletedForcingEnvelope chi modes outputs (s.coefficients τ) delta epsilon x) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((continuousOn_spatialIntegral _
      (continuous_depletedForcingEnvelope_spaceTime s g hg hSum hu2 chi C hchi modes outputs delta epsilon heps)).mono hsubI)
  have hz : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      ‖residual chi modes (s.coefficients τ) x‖ ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((continuousOn_spatialIntegral _
      ((continuous_residual_spaceTime s g hSum hu2 chi modes).norm.pow 2)).mono hsubI)
  obtain ⟨hf, hbalance⟩ := LocalAlignmentEnergyBudget.intervalIntegral_materialRate_eq_energy
    s hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta a b hab hI
  have hdom : ∀ᵐ τ ∂volume.restrict (Set.Ioo a b),
      (∫ x : T3, materialRate chi modes outputs (s.coefficients τ) delta nu x) +
        (∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) -
        (∫ x : T3, depletedForcingEnvelope chi modes outputs (s.coefficients τ) delta epsilon x) ≤
      ((16 * nu / delta) * strainGradientCutoffWeight modes chi) *
        (kineticEnergy (s.coefficients τ) * kineticEnergy (fourierCurl (s.coefficients τ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      LocalAlignmentEnergyBudget.ae_integrable_materialRate s hB g hg hSum hu chi C hchi modes outputs
        hcut hchir hsub hout hs hk delta a b hab hI] with τ hτ hF
    have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
      (hu τ (hsubI (Set.Ioo_subset_Icc_self hτ)))
    have h := integral_materialRate_add_residual_le chi modes outputs _ hm delta nu epsilon hd heps hnu.le hF
    nlinarith
  have h := LocalEnergySubinterval.integral_le_of_energy_enstrophy_majorant
    s hnu g hg hSum hu2 a b ha hab hb _
    ((16 * nu / delta) * strainGradientCutoffWeight modes chi)
    (mul_nonneg (by positivity) (strainGradientCutoffWeight_nonneg modes chi))
    ((hf.add hz).sub hR) hdom
  rw [intervalIntegral.integral_sub (hf.add hz) hR,
    intervalIntegral.integral_add hf hz, hbalance] at h
  have he : (16 * nu / delta * strainGradientCutoffWeight modes chi) * kineticEnergy u₀ ^ 2 /
      (4 * nu) = 4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta := by
    field_simp
    ring
  rw [he] at h
  linarith

theorem meanEnergy_add_integral_residual_le_initial (hT : 0 < T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanEnergy chi modes (s.coefficients t) delta +
      (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes u₀ delta +
        4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, depletedForcingEnvelope chi modes outputs (s.coefficients τ) delta epsilon x := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hA : ContinuousOn (fun τ ↦ meanEnergy chi modes (s.coefficients τ) delta) (Set.Icc 0 T) :=
    continuousOn_spatialIntegral _ (continuous_alignmentEnergy_spaceTime s g hSum hu2 chi modes delta)
  have hZ : ContinuousOn (fun τ ↦ ∫ x : T3,
      ‖residual chi modes (s.coefficients τ) x‖ ^ 2) (Set.Icc 0 T) :=
    continuousOn_spatialIntegral _ ((continuous_residual_spaceTime s g hSum hu2 chi modes).norm.pow 2)
  have hR : ContinuousOn (fun τ ↦ ∫ x : T3,
      depletedForcingEnvelope chi modes outputs (s.coefficients τ) delta epsilon x) (Set.Icc 0 T) :=
    continuousOn_spatialIntegral _
      (continuous_depletedForcingEnvelope_spaceTime s g hg hSum hu2 chi C hchi modes outputs delta epsilon heps)
  have h := intervalIntegral.endpoint_estimate_of_interior hT hA hZ hR
    (fun a b ha hab hb ↦ meanEnergy_add_integral_residual_le
      s hnu hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd epsilon heps a b hab.le
      (fun _ hτ ↦ ⟨ha.trans_le hτ.1, hτ.2.trans_lt hb⟩)) t ht
  simpa only [s.initial] using h

end Solution

/-- Physical periodic data construct a single local solution satisfying
the depleted-source estimate for every admissible finite filter. -/
theorem exists_physical_localDepletedAlignmentBudget (nu : ℝ) (hnu : 0 < nu)
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
      ∀ delta > (0 : ℝ), ∀ epsilon > (0 : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) T,
      meanEnergy chi modes (s.coefficients t) delta +
        (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes (torusFourierVelocity f) delta +
        4 * strainGradientCutoffWeight modes chi * kineticEnergy (torusFourierVelocity f) ^ 2 / delta +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, depletedForcingEnvelope chi modes outputs (s.coefficients τ) delta epsilon x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd epsilon heps t ht
  exact meanEnergy_add_integral_residual_le_initial s hnu hB g hg hSum hu chi C hchi modes outputs
    hcut hchir hsub hout hs hk delta hd epsilon heps hT t ht

end Mettapedia.FluidDynamics.NavierStokes.LocalDepletedAlignmentBudget
