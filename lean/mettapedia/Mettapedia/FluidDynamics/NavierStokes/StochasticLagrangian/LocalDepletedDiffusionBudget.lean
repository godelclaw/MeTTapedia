import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.DepletedLaplacianDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalDepletedAlignmentSource
/-!
# Actual weak diffusion with the capped alignment weight

All spatial consistency hypotheses are discharged for the actual filtered
strain and full, untruncated vorticity. No spectral gap or selected-frame
measurability is required. The resulting continuous local cost retains
alignment information instead of spending a coarse initial-energy bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalDepletedDiffusionBudget

open scoped Topology Matrix.Norms.Elementwise RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFourierStrainGradient PancakeFilteredStrainDynamics
open PancakeFourierPressureStrain
open PancakeSpatialStrainEvolution PancakePhysicalDiffusionLimit PancakePhysicalLaplacian
open PancakeFourierTranslationCurve PancakeLaplacianDiffusion PancakeRegularizedMaterialRate
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeDyadicDirectionEvolution PancakeHigherDerivativeMoments
open PancakeInfiniteSpatialLaplacian InfiniteKineticCancellation InfiniteConvectionEnergy
open LocalVorticityDiffusion LocalLowDiffusionBudget LocalLowFrequencyBudget LocalKineticEnergy
open PancakeLocalInfiniteVelocity

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open LocalJointDiffusionBudget LocalDepletedAlignmentSource LocalAlignmentForcing LocalAlignmentContinuity
open SpectralDiffusionWeight
open PancakeMeasurableMaterialRate

def diffusionCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta epsilon nu : ℝ) (x : T3) : ℝ :=
  (16 * nu / delta) * (3 * strainGradientAmplitude modes chi u ^ 2) *
    weight (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x) epsilon

theorem continuous_diffusionCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (delta epsilon nu : ℝ) (heps : 0 < epsilon) :
    Continuous (diffusionCost chi modes u delta epsilon nu) :=
  (continuous_weight _ _ epsilon heps
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_fullVorticity u hu)).const_mul _

theorem diffusionCost_nonneg (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta epsilon nu : ℝ)
    (hd : 0 < delta) (heps : 0 < epsilon) (hnu : 0 ≤ nu) (x : T3) :
    0 ≤ diffusionCost chi modes u delta epsilon nu x :=
  mul_nonneg (by positivity) (weight_nonneg _ _ epsilon heps)

theorem diffusionCost_le_coarse (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta epsilon nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu) (x : T3) :
    diffusionCost chi modes u delta epsilon nu x ≤
      (16 * nu / delta) * (3 * strainGradientAmplitude modes chi u ^ 2) * ‖fullVorticity u x‖ ^ 2 :=
  mul_le_mul_of_nonneg_left (weight_le_norm_sq _ _ epsilon) (by positivity)

theorem continuous_diffusionCost_spaceTime {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (g : Wavevector → ℝ) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (delta epsilon : ℝ) (heps : 0 < epsilon) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      diffusionCost chi modes (s.coefficients z.1) delta epsilon nu z.2) := by
  have hc (q : Wavevector) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
    (s.continuous q i).comp continuous_subtype_val
  have hS := continuous_parametric_strain modes chi
    (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t) (fun q _ i ↦ hc q i)
  have hw := continuous_fullVorticity_spaceTime s g hSum hu
  have hW := continuous_weight _ _ epsilon heps hS hw
  have hA : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ strainGradientAmplitude modes chi (s.coefficients t)) := by
    unfold strainGradientAmplitude
    exact continuous_finsetSum modes (fun q _ ↦ continuous_const.mul
      (((PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℂ)).comp
        (continuous_pi (fun i ↦ hc q i))).norm))
  exact (continuous_const.mul (continuous_const.mul ((hA.comp continuous_fst).pow 2))).mul hW

/-- The weak spatial diffusion estimate has no receiver truncation. -/
theorem integral_laplacian_diffusion_paid
    (modes : Finset Wavevector) (chi : Wavevector → ℂ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (F R : T3 → ℝ) (delta epsilon nu : ℝ) (hd : 0 < delta) (heps : 0 < epsilon) (hnu : 0 ≤ nu)
    (hF : Integrable F) (hR : Integrable R)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (spatialStrain modes (filteredVelocity chi u) x)
      delta (fullVorticity u x) (strainLaplacian modes (filteredVelocity chi u) x)
      (fullVorticityLaplacian u x) + R x) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) * (3 * strainGradientAmplitude modes chi u ^ 2) *
      (∫ x : T3, weight (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x) epsilon) + ∫ x : T3, R x := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu
  have hw2 := summable_secondMoment_curl u hu
  have hw1 := summable_firstMoment_of_second _ hw2
  have hwI : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using hw1
  have hw0 := summable_norm_coefficients id _ hwI
  have hwd := summable_norm_derivativeCoefficients id _ hwI
  have hwdd := summable_norm_secondDerivative _ hw2
  have hS : Continuous (spatialStrain modes (filteredVelocity chi u)) := by
    apply Continuous.subtype_mk
    have hc := PancakeMappedFourierDiffusion.continuous_mappedField realMatrixOperatorCLM modes
      (strainCoeff (filteredVelocity chi u))
    rw [mappedField_strain] at hc
    exact hc
  have hL : 0 ≤ strainGradientAmplitude modes chi u := by
    unfold strainGradientAmplitude
    exact Finset.sum_nonneg (fun q _ ↦ mul_nonneg (strainGradientWeight_nonneg chi q) (norm_nonneg _))
  have hp : ∀ᵐ x : T3, F x ≤ nu * linearRate (spatialStrain modes (filteredVelocity chi u) x)
      delta (fullVorticity u x) (∑ j : Fin 3, strainSecond modes (filteredVelocity chi u) j x)
      (∑ j : Fin 3, fullCurlSecond u j x) + R x := by
    simpa only [sum_fullCurlSecond u hu, strainLaplacian] using hpoint
  have hh := DepletedLaplacianDiffusion.integral_joint_rate_le_of_uniform_approx (Finset.univ : Finset (Fin 3))
    (spatialStrain modes (filteredVelocity chi u)) (fullVorticity u)
    (strainSecond modes (filteredVelocity chi u)) (fullCurlSecond u) F R delta epsilon nu
    (fun _ ↦ strainGradientAmplitude modes chi u) coordinateShift
    (fun j ↦ PancakeMappedFourierDiffusion.uniformError modes (strainCoeff (filteredVelocity chi u)) j 9)
    (fun j ↦ InfiniteFourierDiffusion.uniformError (fourierCurl u) j ‖complexRealPartEuclideanCLM‖)
    hd heps hnu (fun _ _ ↦ hL) hS (continuous_fullVorticity u hu1) hF hR hp
    (fun h _ j _ x ↦ by
      have he := PancakeMappedFourierDiffusion.norm_mappedSecond_sub_central_le realMatrixOperatorCLM modes
        (strainCoeff (filteredVelocity chi u)) j 9 h x (by norm_num) norm_realMatrixOperator_le
      simpa only [mappedField_strain, strainSecond] using he)
    (fun h _ j _ x ↦ by
      have he := InfiniteFourierDiffusion.norm_mappedSecond_sub_central_le complexRealPartEuclideanCLM
        (fourierCurl u) hw0 j h x
      simpa only [mappedField_curl u hu1, fullCurlSecond] using he)
    (fun h _ j _ x ↦ norm_strain_shift_le_amplitude modes chi u j h x)
    (fun h _ j _ x ↦ by
      simpa only [coordinateShift_neg, abs_neg] using norm_strain_shift_le_amplitude modes chi u j (-h) x)
    (fun _ _ ↦ PancakeMappedFourierDiffusion.uniformError_tendsto _ _ _ _)
    (fun j _ ↦ InfiniteFourierDiffusion.uniformError_tendsto _ hw0 j (hwd j) (hwdd j j) _)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hh

theorem integral_materialRate_add_residual_le
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (delta epsilon eta nu : ℝ)
    (hd : 0 < delta) (heps : 0 < epsilon) (heta : 0 < eta) (hnu : 0 ≤ nu)
    (hF : Integrable (materialRate chi modes outputs u delta nu)) :
    (∫ x : T3, materialRate chi modes outputs u delta nu x) +
      (∫ x : T3, ‖residual chi modes u x‖ ^ 2) ≤
      (∫ x : T3, diffusionCost chi modes u delta epsilon nu x) +
        ∫ x : T3, depletedForcingEnvelope chi modes outputs u delta eta x := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hz : Integrable (fun x : T3 ↦ ‖residual chi modes u x‖ ^ 2) :=
    ((continuous_residual chi modes u hu1).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (depletedForcingEnvelope chi modes outputs u delta eta) :=
    (continuous_depletedForcingEnvelope chi modes outputs u hu1 delta eta heta).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_laplacian_diffusion_paid modes chi u hu
    (fun x ↦ materialRate chi modes outputs u delta nu x + ‖residual chi modes u x‖ ^ 2)
    (depletedForcingEnvelope chi modes outputs u delta eta) delta epsilon nu hd heps hnu (hF.add hz) hR
    (Filter.Eventually.of_forall (materialRate_depleted_le chi modes outputs u delta nu eta heta))
  rw [integral_add hF hz] at h
  simpa only [diffusionCost, integral_const_mul] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalDepletedDiffusionBudget
