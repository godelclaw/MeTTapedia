import Mettapedia.Analysis.WeightedCurlCancellation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticitySeparation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityNegation

/-!
# Weighted cancellation for the actual full vorticity

The fields and all jets are reconstructed from the same infinite Fourier
velocity. No finite-support, imposed-strain, or assumed-cancellation
hypothesis is used. Four absolute moments justify the classical derivatives.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedCurlCancellation

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis WeightedCurlCancellation
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeGalerkinKineticEnergy PancakeHigherDerivativeMoments PancakeInfiniteSpatialCurl
open PancakeInfiniteSpatialLaplacian PancakePeriodicComplexStretch PancakePeriodicVorticityEquation
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeLocalProjectedEquation
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakeLocalGradientEquation PancakeLocalStrainEquation PancakeFilteredStrainDynamics
open PancakeFourierMaterialPaths
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget LocalAlignmentForcing
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance actualCurlCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance actualCurlCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance actualCurlCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem summable_fourierMoment_curl (m : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (m + 1) u)) : Summable (fourierMoment m (fourierCurl u)) :=
  (hu.mul_left (2 * Real.pi)).of_nonneg_of_le (fourierMoment_nonneg _ _)
    (LocalVorticityDiffusion.fourierMoment_curl_le m u)

theorem fullVorticity_curl_eq_curlJet (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) :
    fullVorticity (fourierCurl u) x = curlJet (fun j ↦ fullCurlGradient u j x) := by
  have hw : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment_curl 1 u hu
  ext i
  fin_cases i <;> simp [fullVorticity, spatialCurl, coordinateDerivative_fullFourierField _ _ hw,
    fullCurlGradient, curlJet, complexRealPartEuclideanCLM_apply, complexRealPartEuclidean]

theorem sum_fullCurlGradient_diagonal_eq_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (x : T3) :
    (∑ j : Fin 3, fullCurlGradient u j x j) = 0 := by
  have hw := summable_fourierMoment_curl 2 u hu
  have hw1 : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second _ hw
  have h := congrArg Complex.re
    (spatialDivergence_fullFourierField (fourierCurl u) hw (fun k ↦ fourierCurl_transverse k u) x)
  simpa only [spatialDivergence, coordinateDerivative_fullFourierField _ _ hw1,
    Complex.re_sum, Complex.zero_re, fullCurlGradient,
    complexRealPartEuclideanCLM_apply, complexRealPartEuclidean, PiLp.toLp_apply] using h

theorem inner_fullStrain_curl_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) (a : R3) :
    ⟪a, fullStrainOperator (fourierCurl u) x a⟫ =
      ∑ j : Fin 3, a j * ⟪a, fullCurlGradient u j x⟫ := by
  have hw : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment_curl 1 u hu
  simp [fullStrainOperator, realMatrixOperator_apply, PancakeLocalStrainEquation.spatialStrain,
    symmetrize, spatialVelocityGradient, coordinateDerivative_fullFourierField _ _ hw,
    fullCurlGradient, complexRealPartEuclideanCLM_apply, complexRealPartEuclidean,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, Complex.mul_re]
  ring

/-- The unweighted cancellation and its exact polynomial-weight defect
hold for full spatial curls, with no assumed dynamical budget. -/
theorem integral_weighted_strain_doubleCurl_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (n : ℕ) :
    (∫ x : T3, (‖fullVorticity u x‖ ^ 2) ^ n *
      ⟪fullVorticity u x, fullStrainOperator (fourierCurl (fourierCurl u)) x (fullVorticity u x)⟫) =
      -(∫ x : T3, (∑ j : Fin 3, fullVorticity u x j *
        weightRate n (fullVorticity u x) (fullCurlGradient u j x)) *
          ⟪fullVorticity u x, fullVorticity (fourierCurl u) x⟫) := by
  have hu3 := summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 4) hu
  have hw3 := summable_fourierMoment_curl 3 u hu
  have hw2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hw3
  have hshift (j : Fin 3) : UnitTorusWeakDerivative.coordinateShift j =
      PancakeFourierTranslationCurve.coordinateShift j := by
    funext t i
    simp [UnitTorusWeakDerivative.coordinateShift, UnitTorusWeakDerivative.torusPoint,
      UnitTorusWeakDerivative.coordinateLine, PancakeFourierTranslationCurve.coordinateShift,
      PancakeFourierMaterialPaths.torusPoint, PancakeFourierStrainGradient.coordinateLine]
  simp_rw [inner_fullStrain_curl_eq (fourierCurl u) hw2]
  apply integral_weighted_curl_gradient_eq (fullVorticity u) (fullVorticity (fourierCurl u))
    (fullCurlGradient u) (fullCurlGradient (fourierCurl u))
    (continuous_fullVorticity u (summable_firstMoment_of_second _ hu2))
    (continuous_fullVorticity _ (summable_firstMoment_of_second _ hw2))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)
    (LocalSquaredGapGradient.continuous_fullCurlGradient (fourierCurl u))
    (LocalAlignmentTransport.locallyLipschitz_fullVorticity u hu2)
    (LocalAlignmentTransport.locallyLipschitz_fullVorticity _ hw2)
  · intro j x
    simpa only [hshift, PancakeHaarTransportRate.coordinateShift_zero, add_zero] using
      hasDerivAt_fullVorticity_shift u hu3 j x 0
  · intro j x
    simpa only [hshift, PancakeHaarTransportRate.coordinateShift_zero, add_zero] using
      hasDerivAt_fullVorticity_shift (fourierCurl u) hw3 j x 0
  · exact fullVorticity_curl_eq_curlJet u hu2
  · exact sum_fullCurlGradient_diagonal_eq_zero u hu3
  · exact sum_fullCurlGradient_diagonal_eq_zero (fourierCurl u) hw3

theorem integral_strain_doubleCurl_eq_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) :
    (∫ x : T3,
      ⟪fullVorticity u x, fullStrainOperator (fourierCurl (fourierCurl u)) x (fullVorticity u x)⟫) = 0 := by
  simpa [weightRate] using integral_weighted_strain_doubleCurl_eq u hu 0

/-- Incompressibility identifies the double curl with the negative ordinary
velocity Laplacian; the coefficient normalization includes the torus phase. -/
theorem fourierCurl_fourierCurl_eq_neg_laplacian (u : FourierVelocity)
    (hd : ∀ k, modeDot k (u k) = 0) :
    fourierCurl (fourierCurl u) = -laplacianCoeff u := by
  funext k
  simp only [fourierCurl, coefficientCross_smul_right, cross_cross_wavevector, hd,
    zero_smul, zero_sub, smul_neg, smul_smul, Pi.neg_apply, laplacianCoeff]
  rw [pow_two, mul_assoc]

theorem fullFourierField_negativeLaplacian_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) :
    fullFourierField id (-laplacianCoeff u) x = -spatialLaplacian (fullFourierField id u) x := by
  rw [LocalVorticityNegation.fullFourierField_neg, spatialLaplacian_fullFourierField u hu]
  rfl

theorem integral_strain_negativeLaplacian_eq_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ k, modeDot k (u k) = 0) :
    (∫ x : T3, ⟪fullVorticity u x,
      fullStrainOperator (-laplacianCoeff u) x (fullVorticity u x)⟫) = 0 := by
  rw [← fourierCurl_fourierCurl_eq_neg_laplacian u hd]
  exact integral_strain_doubleCurl_eq_zero u hu

/-- The sixth-power weight leaves the exact signed longitudinal-helicity
defect. The unweighted zero identity cannot be reused with this weight. -/
theorem integral_sixth_weighted_strain_negativeLaplacian_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ k, modeDot k (u k) = 0) :
    (∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x,
      fullStrainOperator (-laplacianCoeff u) x (fullVorticity u x)⟫) =
      -6 * (∫ x : T3, ‖fullVorticity u x‖ ^ 4 *
        (∑ j : Fin 3, fullVorticity u x j * ⟪fullVorticity u x, fullCurlGradient u j x⟫) *
          ⟪fullVorticity u x, fullVorticity (fourierCurl u) x⟫) := by
  have h := integral_weighted_strain_doubleCurl_eq u hu 3
  rw [fourierCurl_fourierCurl_eq_neg_laplacian u hd] at h
  have hr (x : T3) :
      (∑ j : Fin 3, fullVorticity u x j * weightRate 3 (fullVorticity u x) (fullCurlGradient u j x)) *
          ⟪fullVorticity u x, fullVorticity (fourierCurl u) x⟫ =
      6 * (‖fullVorticity u x‖ ^ 4 *
        (∑ j : Fin 3, fullVorticity u x j * ⟪fullVorticity u x, fullCurlGradient u j x⟫) *
          ⟪fullVorticity u x, fullVorticity (fourierCurl u) x⟫) := by
    norm_num [weightRate, ← pow_mul, Fin.sum_univ_three]
    ring
  simp only [← pow_mul, hr, integral_const_mul] at h
  convert h using 1
  ring

/-- Amplitude variation along vortex lines paired with curl helicity. -/
def longitudinalHelicityIntegral (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ 4 *
    (∑ j : Fin 3, fullVorticity u x j * ⟪fullVorticity u x, fullCurlGradient u j x⟫) *
      ⟪fullVorticity u x, fullVorticity (fourierCurl u) x⟫

/-- The actual strain's deviation from the chosen Laplacian scale. -/
def weightedStrainSpectralDefect (κ : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x,
    (fullStrainOperator (-laplacianCoeff u) x - κ • fullStrainOperator u x) (fullVorticity u x)⟫

/-- An exact alternative expression for the existing eighth-moment source.
It retains both signed debts and asserts no spectral concentration. -/
theorem stretching_spectral_identity (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ k, modeDot k (u k) = 0) (κ : ℝ) :
    κ * LocalVorticityEighthMoment.stretching u =
      -6 * longitudinalHelicityIntegral u - weightedStrainSpectralDefect κ u := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 4) hu
  have hw := continuous_fullVorticity u hu1
  have hdbl : Summable (fourierMoment 1 (fourierCurl (fourierCurl u))) :=
    summable_fourierMoment_curl 1 _ (summable_fourierMoment_curl 2 u
      (summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu))
  rw [fourierCurl_fourierCurl_eq_neg_laplacian u hd] at hdbl
  have hL : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 *
      ⟪fullVorticity u x, fullStrainOperator (-laplacianCoeff u) x (fullVorticity u x)⟫) :=
    ((hw.norm.pow 6).mul (hw.inner ((continuous_fullStrainOperator _ hdbl).clm_apply hw))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hS : Integrable (fun x : T3 ↦ κ * (‖fullVorticity u x‖ ^ 6 *
      ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫)) :=
    ((hw.norm.pow 6).mul (hw.inner ((continuous_fullStrainOperator u hu1).clm_apply hw))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) |>.const_mul κ
  have hdef : weightedStrainSpectralDefect κ u =
      -6 * longitudinalHelicityIntegral u - κ * LocalVorticityEighthMoment.stretching u := by
    unfold weightedStrainSpectralDefect
    simp only [sub_apply, smul_apply, inner_sub_right,
      real_inner_smul_right, mul_sub, show ∀ x y : ℝ, x * (κ * y) = κ * (x * y) from by intros; ring]
    rw [integral_sub hL hS, integral_const_mul,
      integral_sixth_weighted_strain_negativeLaplacian_eq u hu hd]
    rfl
  linarith only [hdef]

theorem longitudinalHelicityIntegral_eq_zero_of_no_longitudinal_variation (u : FourierVelocity)
    (h : ∀ x : T3, ∑ j : Fin 3,
      fullVorticity u x j * ⟪fullVorticity u x, fullCurlGradient u j x⟫ = 0) :
    longitudinalHelicityIntegral u = 0 := by
  simp only [longitudinalHelicityIntegral, h, mul_zero, zero_mul, integral_zero]

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedCurlCancellation
