import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeightVariationGradient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeReducedEulerianBudget

/-!
# Finite-cutoff payment for the actual strain-weight variation

The physical velocity and strain gradient are bounded from their Fourier
coefficients. Parseval removes the receiver cardinality from the spatial
integral. The transporting multiplier's squared mass remains explicit;
for the low/full mismatch it is not uniform in the retained cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeWeightVariationCutoff

open MeasureTheory
open scoped ComplexConjugate
open PeriodicFourierTriad PancakeWeightVariationGradient PancakePhysicalWeightedTransport
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakePhysicalSpectralDefect
open PancakeMeasurableMaterialRate PancakeFrequencyProjectorCommutator PancakeViscousMisalignmentAbsorption
open PancakeLowDiffusionBudget PancakeFourierStrainGradient PancakePressureAnisotropyBudget
open PancakeReducedForcingContinuity PancakeEulerianAlignmentBudget PancakeGalerkinKineticEnergy
open PancakePeriodicVorticityEquation
open PancakePeriodicCoherentSplit PancakeTransverseEnergyFreezing PancakePeriodicComplexStretch
open PancakePhysicalMeanBalance PancakeReducedEulerianBudget

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def velocityMultiplierMass (modes : Finset Wavevector) (beta : Wavevector → ℂ) : ℝ :=
  ∑ q ∈ modes, ‖beta q‖ ^ 2

def weightVariationCutoffConstant (low modes : Finset Wavevector)
    (chi beta : Wavevector → ℂ) : ℝ :=
  2 * Real.sqrt (velocityMultiplierMass modes beta) * Real.sqrt (strainGradientCutoffWeight low chi)

theorem weightVariationCutoffConstant_nonneg (low modes : Finset Wavevector)
    (chi beta : Wavevector → ℂ) : 0 ≤ weightVariationCutoffConstant low modes chi beta := by
  unfold weightVariationCutoffConstant
  positivity

theorem norm_coefficientReconstruction_le_sum (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    ‖coefficientVec (finiteFourierReconstruction modes u x)‖ ≤ ∑ q ∈ modes, ‖coefficientVec (u q)‖ := by
  simp only [finiteFourierReconstruction, coefficientVec, WithLp.toLp_sum, WithLp.toLp_smul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [norm_smul]
  have h := (UnitAddTorus.mFourier q).norm_coe_le_norm x
  rw [UnitAddTorus.mFourier_norm] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (u q))]

theorem norm_spatialVelocity_le_energy (beta : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    ‖spatialVelocity beta modes u x‖ ≤
      Real.sqrt (velocityMultiplierMass modes beta) * Real.sqrt (fullEnergy modes u) := by
  have hreal := norm_realPart_sq_le (finiteFourierReconstruction modes (filteredVelocity beta u) x)
  have hn : ‖spatialVelocity beta modes u x‖ ≤
      ‖coefficientVec (finiteFourierReconstruction modes (filteredVelocity beta u) x)‖ := by
    change ‖complexRealPartEuclidean (finiteFourierReconstruction modes (filteredVelocity beta u) x)‖ ≤ _
    nlinarith [norm_nonneg (complexRealPartEuclidean (finiteFourierReconstruction modes (filteredVelocity beta u) x)),
      norm_nonneg (coefficientVec (finiteFourierReconstruction modes (filteredVelocity beta u) x))]
  apply hn.trans ((norm_coefficientReconstruction_le_sum modes (filteredVelocity beta u) x).trans ?_)
  simp only [norm_coefficientVec_filtered]
  have hc := Real.sum_mul_le_sqrt_mul_sqrt modes (fun q ↦ ‖beta q‖) (fun q ↦ ‖coefficientVec (u q)‖)
  simpa only [norm_coefficientVec_sq, velocityMultiplierMass, fullEnergy] using hc

theorem ae_abs_weightVariation_le_energy (chi beta : Wavevector → ℂ) (low modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (hlow : low ⊆ modes)
    (hchi : ∀ q, q ∉ low → chi q = 0) :
    ∀ᵐ x : T3, |physicalWeightVariation chi beta modes u delta x| ≤
      weightVariationCutoffConstant low modes chi beta * fullEnergy modes u *
        ‖coefficientVec (finiteFourierReconstruction modes (fourierCurl u) x)‖ ^ 2 := by
  filter_upwards [ae_abs_physicalWeightVariation_le_gradient_norm chi beta modes u delta] with x hx
  have hg := sum_norm_strainGradient_sq_le low modes chi u x hlow
  have he : (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) =
      ∑ j : Fin 3, ‖strainGradient low (filteredVelocity chi u) x j‖ ^ 2 := by
    simp only [strainGradient_filtered_subset low modes chi u x _ hlow hchi]
  rw [he] at hx
  have hgs := Real.sqrt_le_sqrt hg
  rw [Real.sqrt_mul (strainGradientCutoffWeight_nonneg low chi)] at hgs
  have hw := norm_realPart_sq_le (finiteFourierReconstruction modes (fourierCurl u) x)
  have hv := norm_spatialVelocity_le_energy beta modes u x
  apply hx.trans
  calc
    _ ≤ 2 * (Real.sqrt (velocityMultiplierMass modes beta) * Real.sqrt (fullEnergy modes u)) *
      (Real.sqrt (strainGradientCutoffWeight low chi) * Real.sqrt (fullEnergy modes u)) *
        ‖coefficientVec (finiteFourierReconstruction modes (fourierCurl u) x)‖ ^ 2 := by
          apply mul_le_mul ?_ hw (sq_nonneg _) (by positivity)
          gcongr
    _ = _ := by
      unfold weightVariationCutoffConstant
      calc
        _ = 2 * Real.sqrt (velocityMultiplierMass modes beta) *
          Real.sqrt (strainGradientCutoffWeight low chi) * (Real.sqrt (fullEnergy modes u)) ^ 2 *
            ‖coefficientVec (finiteFourierReconstruction modes (fourierCurl u) x)‖ ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt (fullEnergy_nonneg modes u)]

theorem integral_abs_weightVariation_le_energy
    (chi beta : Wavevector → ℂ) (low modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (hlow : low ⊆ modes)
    (hchi : ∀ q, q ∉ low → chi q = 0) :
    (∫ x : T3, |physicalWeightVariation chi beta modes u delta x|) ≤
      weightVariationCutoffConstant low modes chi beta * fullEnergy modes u * fullEnergy modes (fourierCurl u) := by
  have hi : Integrable (fun x : T3 ↦ (weightVariationCutoffConstant low modes chi beta * fullEnergy modes u) *
      ‖coefficientVec (finiteFourierReconstruction modes (fourierCurl u) x)‖ ^ 2) :=
    (continuous_const.mul ((continuous_coefficientReconstruction modes (fourierCurl u)).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x : T3 ↦ abs_nonneg
    (physicalWeightVariation chi beta modes u delta x))) hi
    (ae_abs_weightVariation_le_energy chi beta low modes u delta hlow hchi)
  rw [integral_const_mul, integral_norm_coefficientReconstruction_sq] at h
  exact h

theorem abs_meanWeightVariation_le_energy (chi : Wavevector → ℂ) (low modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (hlow : low ⊆ modes)
    (hchi : ∀ q, q ∉ low → chi q = 0) :
    |meanWeightVariation chi modes u delta| ≤
      weightVariationCutoffConstant low modes chi (fun q ↦ chi q - 1) *
        fullEnergy modes u * fullEnergy modes (fourierCurl u) := by
  apply abs_integral_le_integral_abs.trans
  exact integral_abs_weightVariation_le_energy chi _ low modes u delta hlow hchi

theorem integral_abs_meanWeightVariation_initial_paid
    (chi : Wavevector → ℂ) (low modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (delta nu T : ℝ) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hlow : low ⊆ modes) (hchi : ∀ q, q ∉ low → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t q, u t (-q) = PancakeBlockReality.coefficientConjugate (u t q))
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ t, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ t, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun s ↦ u s q i) (velocityRHS modes (u t) nu q i) t) :
    (∫ t in (0 : ℝ)..T, |meanWeightVariation chi modes (u t) delta|) ≤
      weightVariationCutoffConstant low modes chi (fun q ↦ chi q - 1) * fullEnergy modes (u 0) ^ 2 / (2 * nu) := by
  have hc1 := PancakeMaterialSpatialEstimate.contDiff_coefficients_of_velocityRHS modes u nu hk hu hd
  have hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i) := fun q hq i ↦ (hc1 q hq i).continuous
  have hIW := (continuous_meanWeightVariation chi modes u delta hc hk hu hs hr hchir).abs.intervalIntegrable
    (μ := volume) 0 T
  have hIU := (continuous_kineticEnstrophyProduct modes u hc).intervalIntegrable (μ := volume) 0 T
  let C := weightVariationCutoffConstant low modes chi (fun q ↦ chi q - 1)
  have hp : ∀ t : ℝ, |meanWeightVariation chi modes (u t) delta| ≤
      C * (fullEnergy modes (u t) * fullEnergy modes (fourierCurl (u t))) := by
    intro t
    simpa only [C, mul_assoc] using abs_meanWeightVariation_le_energy chi low modes (u t) delta hlow hchi
  have hi := intervalIntegral.integral_mono_on hT hIW (hIU.const_mul C) (fun t _ ↦ hp t)
  rw [intervalIntegral.integral_const_mul] at hi
  apply hi.trans
  have hpay := mul_le_mul_of_nonneg_left
    (kineticEnstrophyProduct_integral_le_initial modes u nu T hnu hT hs hr hu hd)
    (weightVariationCutoffConstant_nonneg low modes chi (fun q ↦ chi q - 1))
  simpa only [C, mul_div_assoc] using hpay

theorem velocityMultiplierMass_mismatch_split (chi : Wavevector → ℂ) (low modes : Finset Wavevector)
    (hlow : low ⊆ modes) (hchi : ∀ q, q ∉ low → chi q = 0) :
    velocityMultiplierMass modes (fun q ↦ chi q - 1) =
      (modes \ low).card + ∑ q ∈ low, ‖chi q - 1‖ ^ 2 := by
  classical
  have he : (∑ q ∈ modes \ low, ‖chi q - 1‖ ^ 2) = ((modes \ low).card : ℝ) := by
    calc
      _ = ∑ _q ∈ modes \ low, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro q hq
        simp [hchi q (Finset.mem_sdiff.mp hq).2]
      _ = _ := by simp
  rw [velocityMultiplierMass, ← Finset.sum_sdiff hlow, he]

theorem meanAlignmentEnergy_transport_paid
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
          (8 * strainGradientCutoffWeight low chi / delta +
            weightVariationCutoffConstant low modes chi (fun q ↦ chi q - 1) / (2 * nu)) *
              fullEnergy modes (u 0) ^ 2 +
          (∫ t in (0 : ℝ)..T, meanReducedEnvelope chi modes outputs (u t) delta) := by
  have hb := meanAlignmentEnergy_reduced_budget_initial_paid chi low modes outputs u delta nu T
    hdelt hnu hT hlow hsub hout hchi hchir hs hr hk hu hd
  have hp := integral_abs_meanWeightVariation_initial_paid chi low modes u delta nu T
    hnu hT hlow hchi hchir hs hr hk hu hd
  have ha := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun t ↦ meanWeightVariation chi modes (u t) delta) hT
  have hn := neg_le_abs (∫ t in (0 : ℝ)..T, meanWeightVariation chi modes (u t) delta)
  have he : (8 * strainGradientCutoffWeight low chi / delta +
      weightVariationCutoffConstant low modes chi (fun q ↦ chi q - 1) / (2 * nu)) * fullEnergy modes (u 0) ^ 2 =
      8 * strainGradientCutoffWeight low chi * fullEnergy modes (u 0) ^ 2 / delta +
        weightVariationCutoffConstant low modes chi (fun q ↦ chi q - 1) * fullEnergy modes (u 0) ^ 2 / (2 * nu) := by ring
  rw [he]
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeWeightVariationCutoff
