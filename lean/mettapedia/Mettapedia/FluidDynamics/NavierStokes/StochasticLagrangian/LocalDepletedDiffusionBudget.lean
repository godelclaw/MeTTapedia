import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.DepletedLaplacianDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalDepletedAlignmentSource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalizedLaplacianDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalStrainGradientDensity

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
open PancakeMeasurableMaterialRate LocalStrainGradientDensity LocalSpatialSpectralBounds
open LocalSpatialSpectralRelation PancakeHaarTransportRate

def diffusionCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta epsilon nu : ℝ) (x : T3) : ℝ :=
  (16 * nu / delta) * strainGradientSquare chi modes u x *
    weight (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x) epsilon

theorem continuous_diffusionCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (delta epsilon nu : ℝ) (heps : 0 < epsilon) :
    Continuous (diffusionCost chi modes u delta epsilon nu) :=
  ((continuous_strainGradientSquare chi modes u).const_mul _).mul
    (continuous_weight _ _ epsilon heps
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_fullVorticity u hu))

theorem diffusionCost_nonneg (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta epsilon nu : ℝ)
    (hd : 0 < delta) (heps : 0 < epsilon) (hnu : 0 ≤ nu) (x : T3) :
    0 ≤ diffusionCost chi modes u delta epsilon nu x :=
  mul_nonneg (mul_nonneg (by positivity) (strainGradientSquare_nonneg chi modes u x))
    (weight_nonneg _ _ epsilon heps)

theorem diffusionCost_le_coarse (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta epsilon nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu) (x : T3) :
    diffusionCost chi modes u delta epsilon nu x ≤
      (16 * nu / delta) * (3 * strainGradientAmplitude modes chi u ^ 2) * ‖fullVorticity u x‖ ^ 2 := by
  apply (mul_le_mul_of_nonneg_left (weight_le_norm_sq _ _ epsilon)
    (mul_nonneg (by positivity) (strainGradientSquare_nonneg chi modes u x))).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (strainGradientSquare_le_amplitude chi modes u x) (by positivity)) (sq_nonneg _)

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
  have hH := continuous_parametric_strainGradientSquare chi modes
    (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t) (fun q _ i ↦ hc q i)
  exact (hH.const_mul _).mul hW


/-- The actual local strain-gradient density remains inside the weak spatial integral. -/
theorem integral_laplacian_diffusion_local_paid
    (modes : Finset Wavevector) (chi : Wavevector → ℂ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (F R : T3 → ℝ) (delta epsilon nu : ℝ) (hd : 0 < delta) (heps : 0 < epsilon) (hnu : 0 ≤ nu)
    (hF : Integrable F) (hR : Integrable R)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (spatialStrain modes (filteredVelocity chi u) x)
      delta (fullVorticity u x) (strainLaplacian modes (filteredVelocity chi u) x)
      (fullVorticityLaplacian u x) + R x) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) *
      (∫ x : T3, strainGradientSquare chi modes u x * weight (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x) epsilon) + ∫ x : T3, R x := by
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
  have hG (j : Fin 3) (x : T3) : HasDerivAt
      (fun h ↦ (spatialStrain modes (filteredVelocity chi u) (x + coordinateShift j h)).1)
      (strainGradient modes (filteredVelocity chi u) x j) 0 := by
    simpa only [strainCurve, coordinateShift_zero, add_zero] using hasDerivAt_strainCurve chi modes u j x 0
  have hGneg (j : Fin 3) (x : T3) : HasDerivAt
      (fun h ↦ (spatialStrain modes (filteredVelocity chi u) (x + -(coordinateShift j h))).1)
      (-strainGradient modes (filteredVelocity chi u) x j) 0 := by
    simpa only [Function.comp_def, Pi.neg_apply, id_eq, coordinateShift_neg, neg_zero, neg_one_smul] using
      (hG j x).scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp only [neg_zero])
  have hh := LocalizedLaplacianDiffusion.integral_joint_rate_le_of_first_second_approx (Finset.univ : Finset (Fin 3))
    (spatialStrain modes (filteredVelocity chi u)) (fullVorticity u)
    (fun j x ↦ strainGradient modes (filteredVelocity chi u) x j)
    (strainSecond modes (filteredVelocity chi u)) (fullCurlSecond u) F R delta epsilon nu
    (fun _ ↦ strainGradientAmplitude modes chi u) coordinateShift
    (fun j ↦ PancakeMappedFourierDiffusion.uniformError modes (strainCoeff (filteredVelocity chi u)) j 9)
    (fun j ↦ InfiniteFourierDiffusion.uniformError (fourierCurl u) j ‖complexRealPartEuclideanCLM‖)
    hd heps hnu (fun _ _ ↦ hL) hS (continuous_fullVorticity u hu1) hF hR hp
    (fun j _ ↦ coordinateShift_zero j) (fun j _ ↦ hG j) (fun j _ ↦ hGneg j)
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
  have hi (j : Fin 3) : Integrable (fun x ↦
      ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2 *
        weight (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x) epsilon) :=
    (((continuous_strainGradient chi modes u j).norm.pow 2).mul
      (continuous_weight _ _ epsilon heps hS (continuous_fullVorticity u hu1))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [← integral_finsetSum _ (fun j _ ↦ hi j)] at hh
  simpa only [strainGradientSquare, Finset.sum_mul] using hh

/-- The earlier coarse estimate is a corollary of the local-density estimate. -/
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
  have hW := continuous_weight
    (spatialStrain modes (filteredVelocity chi u)) (fullVorticity u) epsilon heps
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_fullVorticity u hu1)
  have hiW : Integrable (fun x ↦ weight (spatialStrain modes (filteredVelocity chi u) x)
      (fullVorticity u x) epsilon) :=
    hW.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiH : Integrable (fun x ↦ strainGradientSquare chi modes u x *
      weight (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x) epsilon) :=
    ((continuous_strainGradientSquare chi modes u).mul hW).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb := integral_mono hiH (hiW.const_mul (3 * strainGradientAmplitude modes chi u ^ 2))
    (fun x ↦ mul_le_mul_of_nonneg_right (strainGradientSquare_le_amplitude chi modes u x)
      (weight_nonneg _ _ epsilon heps))
  rw [integral_const_mul] at hb
  have h := integral_laplacian_diffusion_local_paid modes chi u hu F R delta epsilon nu hd heps hnu hF hR hpoint
  exact h.trans (by
    simpa only [mul_assoc, add_comm] using add_le_add_right
      (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 16 * nu / delta)) (∫ x : T3, R x))

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
  have h := integral_laplacian_diffusion_local_paid modes chi u hu
    (fun x ↦ materialRate chi modes outputs u delta nu x + ‖residual chi modes u x‖ ^ 2)
    (depletedForcingEnvelope chi modes outputs u delta eta) delta epsilon nu hd heps hnu (hF.add hz) hR
    (Filter.Eventually.of_forall (materialRate_depleted_le chi modes outputs u delta nu eta heta))
  rw [integral_add hF hz] at h
  simpa only [diffusionCost, mul_assoc, integral_const_mul] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalDepletedDiffusionBudget
