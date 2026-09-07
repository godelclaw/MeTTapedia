import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeReducedForcingContinuity

/-!
# Integrated alignment budget with signed transport-weight variation

The frozen material derivative is constructed from the supplied retained
velocity solution. Its integrated estimate squares only the reduced
forcing, and keeps the actual weight variation signed. No spectral gap,
extra forcing integrability budget, or arbitrary-data existence is assumed
or concluded by this finite-cutoff result.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeReducedEulerianBudget

open MeasureTheory
open scoped ComplexConjugate
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open PancakeMaterialSpatialEstimate PancakeAEMaterialRate PancakeMeasurableMaterialRate
open PancakeFrozenMaterialDerivative PancakeMaterialDiffusionBudget PancakeReducedMaterialBudget
open PancakePhysicalWeightedTransport PancakeReducedForcingContinuity PancakeEulerianAlignmentBudget
open PancakePhysicalMeanBalance PancakeFourierStrainGradient PancakeViscousMisalignmentAbsorption
open PancakeFrequencyProjectorCommutator

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem ae_frozenMaterialRate_reduced_paid
    (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (delta nu : ℝ) (hdelt : 0 < delta) (hnu : 0 ≤ nu)
    (hlow : low ⊆ modes) (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hchi : ∀ q, q ∉ low → chi q = 0) (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t q, u t (-q) = PancakeBlockReality.coefficientConjugate (u t q))
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ t, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ t, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun s ↦ u s q i) (velocityRHS modes (u t) nu q i) t) :
    ∀ᵐ t : ℝ, (∫ x : T3, frozenMaterialRate chi modes u delta t x) +
      (1 / 2 : ℝ) * meanResidualSquare chi modes (u t) ≤
      (16 * nu / delta) * strainGradientCutoffWeight low chi * fullEnergy modes (u t) *
        fullEnergy modes (fourierCurl (u t)) + meanReducedEnvelope chi modes outputs (u t) delta -
        meanWeightVariation chi modes (u t) delta := by
  have hc := contDiff_coefficients_of_velocityRHS modes u nu hk hu hd
  have hchim : ∀ q, q ∉ modes → chi q = 0 := fun q hq ↦ hchi q (fun hqL ↦ hq (hlow hqL))
  filter_upwards [ae_ae_materialSpectralDifferentiable chi modes u hc] with t hL
  have heq : ∀ᵐ x : T3, frozenMaterialRate chi modes u delta t x =
      physicalMaterialRate chi modes outputs (u t) delta nu x := by
    filter_upwards [hL] with x hx
    exact (hasDerivAt_frozenMaterialEnergy chi modes outputs u delta nu t x hsub hout hchim hchir
      hs (hr t) hk (hu t) (hd t) hx).deriv
  exact integral_materialRate_reduced_paid chi low modes outputs (u t) delta nu
    (frozenMaterialRate chi modes u delta t) hdelt hnu hlow hsub hchi hchir hs (hr t) (hu t)
    (integrable_frozenMaterialRate_of_agreement chi modes outputs u delta nu t
      (fun q hq i ↦ (hc q hq i).continuous) heq) (heq.mono (fun _ hx ↦ hx.le))

/-- Initial kinetic energy pays diffusion; the actual signed weight
variation replaces the squared mismatch-transport cost. The reduced
nonlinear/projection forcing and all cutoff dependence remain explicit. -/
theorem meanAlignmentEnergy_reduced_budget_initial_paid
    (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (delta nu T : ℝ) (hdelt : 0 < delta) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hlow : low ⊆ modes) (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hchi : ∀ q, q ∉ low → chi q = 0) (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t q, u t (-q) = PancakeBlockReality.coefficientConjugate (u t q))
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ t, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ t, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun s ↦ u s q i) (velocityRHS modes (u t) nu q i) t) :
    meanAlignmentEnergy chi modes (u T) delta +
      (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..T, meanResidualSquare chi modes (u t)) ≤
        meanAlignmentEnergy chi modes (u 0) delta +
          8 * strainGradientCutoffWeight low chi * fullEnergy modes (u 0) ^ 2 / delta +
          (∫ t in (0 : ℝ)..T, meanReducedEnvelope chi modes outputs (u t) delta) -
          (∫ t in (0 : ℝ)..T, meanWeightVariation chi modes (u t) delta) := by
  have hc1 := contDiff_coefficients_of_velocityRHS modes u nu hk hu hd
  have hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i) := fun q hq i ↦ (hc1 q hq i).continuous
  obtain ⟨hIm, hbalance⟩ := intervalIntegral_frozenMaterialRate_eq_energy chi modes u delta 0 T hc1 hu
  have hIz := (continuous_meanResidualSquare chi modes u hc).intervalIntegrable (μ := volume) 0 T
  have hIG := (continuous_meanReducedEnvelope chi modes outputs u delta hc hk hu).intervalIntegrable (μ := volume) 0 T
  have hIW := (continuous_meanWeightVariation chi modes u delta hc hk hu hs hr hchir).intervalIntegrable (μ := volume) 0 T
  have hIU := (continuous_kineticEnstrophyProduct modes u hc).intervalIntegrable (μ := volume) 0 T
  have hpaid := ae_frozenMaterialRate_reduced_paid chi low modes outputs u delta nu hdelt hnu.le
    hlow hsub hout hchi hchir hs hr hk hu hd
  have hpaid' : ∀ᵐ t : ℝ,
      (∫ x : T3, frozenMaterialRate chi modes u delta t x) + (1 / 2 : ℝ) * meanResidualSquare chi modes (u t) ≤
        ((16 * nu / delta) * strainGradientCutoffWeight low chi) *
          (fullEnergy modes (u t) * fullEnergy modes (fourierCurl (u t))) +
        meanReducedEnvelope chi modes outputs (u t) delta - meanWeightVariation chi modes (u t) delta := by
    simpa only [mul_assoc] using hpaid
  have hi := intervalIntegral.integral_mono_ae hT (hIm.add (hIz.const_mul (1 / 2)))
    (((hIU.const_mul ((16 * nu / delta) * strainGradientCutoffWeight low chi)).add hIG).sub hIW) hpaid'
  rw [intervalIntegral.integral_add hIm (hIz.const_mul (1 / 2)),
    intervalIntegral.integral_sub ((hIU.const_mul ((16 * nu / delta) * strainGradientCutoffWeight low chi)).add hIG) hIW,
    intervalIntegral.integral_add (hIU.const_mul ((16 * nu / delta) * strainGradientCutoffWeight low chi)) hIG,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hbalance] at hi
  have hUO := kineticEnstrophyProduct_integral_le_initial modes u nu T hnu hT hs hr hu hd
  have hcpos : 0 ≤ (16 * nu / delta) * strainGradientCutoffWeight low chi :=
    mul_nonneg (by positivity) (strainGradientCutoffWeight_nonneg low chi)
  have hp := mul_le_mul_of_nonneg_left hUO hcpos
  have he : ((16 * nu / delta) * strainGradientCutoffWeight low chi) *
      (fullEnergy modes (u 0) ^ 2 / (2 * nu)) =
      8 * strainGradientCutoffWeight low chi * fullEnergy modes (u 0) ^ 2 / delta := by
    field_simp
    ring
  rw [he] at hp
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeReducedEulerianBudget
