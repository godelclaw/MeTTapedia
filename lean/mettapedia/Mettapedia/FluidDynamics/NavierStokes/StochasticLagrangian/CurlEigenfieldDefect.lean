import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalCenteredHelicityBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullStrainFourierSeries
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFilteredVorticity

/-!
# A common field defect for centered helicity and spectral strain

The defect `curl u - rho*u` is constructed from the actual Fourier velocity.
Its curl is the centered vorticity curl, and applying `curl + rho` gives the
Laplacian spectral defect at `rho^2`. These identities assert neither spectral
concentration nor a dynamical bound on the defect.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.CurlEigenfieldDefect

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeDyadicDirectionEvolution
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open PancakeIndexedFourierMoments PancakeFourierPressureStrain PancakeFourierMaterialPaths
open PancakeCoefficientLimitEquation PancakeLocalInfiniteVelocity PancakeGalerkinVorticityBridge
open LocalLowDiffusionBudget LocalAlignmentForcing LocalWeightedCurlCancellation
open LocalCenteredHelicityBudget FullStrainFourierSeries

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance defectCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance defectCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance defectCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fourierMoment_sub_le (m : ℕ) (u v : FourierVelocity) (q : Wavevector) :
    fourierMoment m (u - v) q ≤ fourierMoment m u q + fourierMoment m v q := by
  change (1 + ‖frequencyVec q‖) ^ m * ‖coefficientVec (u q) - coefficientVec (v q)‖ ≤ _
  exact (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans_eq (mul_add _ _ _)

theorem fourierMoment_smul (m : ℕ) (c : ℂ) (u : FourierVelocity) (q : Wavevector) :
    fourierMoment m (c • u) q = ‖c‖ * fourierMoment m u q := by
  change (1 + ‖frequencyVec q‖) ^ m * ‖c • coefficientVec (u q)‖ = _
  rw [norm_smul]
  unfold fourierMoment
  ring

theorem summable_fourierMoment_sub (m : ℕ) (u v : FourierVelocity)
    (hu : Summable (fourierMoment m u)) (hv : Summable (fourierMoment m v)) :
    Summable (fourierMoment m (u - v)) :=
  (hu.add hv).of_nonneg_of_le (fourierMoment_nonneg _ _) (fourierMoment_sub_le m u v)

theorem summable_fourierMoment_smul (m : ℕ) (c : ℂ) (u : FourierVelocity)
    (hu : Summable (fourierMoment m u)) : Summable (fourierMoment m (c • u)) := by
  change Summable (fun q ↦ fourierMoment m (c • u) q)
  simpa only [fourierMoment_smul] using hu.mul_left ‖c‖

theorem fourierCurl_sub (u v : FourierVelocity) :
    fourierCurl (u - v) = fourierCurl u - fourierCurl v := by
  simp only [sub_eq_add_neg, LocalFilteredVorticity.fourierCurl_add,
    LocalVorticityNegation.fourierCurl_neg]

theorem fourierCurl_smul (c : ℂ) (u : FourierVelocity) :
    fourierCurl (c • u) = c • fourierCurl u := by
  funext q
  simp only [fourierCurl, Pi.smul_apply, coefficientCross_smul_right]
  exact smul_comm _ _ _

/-- The real center is constant in space. -/
def coefficients (ρ : ℝ) (u : FourierVelocity) : FourierVelocity :=
  fourierCurl u - (ρ : ℂ) • u

theorem summable_fourierMoment (m : ℕ) (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (m + 1) u)) :
    Summable (fourierMoment m (coefficients ρ u)) :=
  summable_fourierMoment_sub m _ _ (summable_fourierMoment_curl m u hu)
    (summable_fourierMoment_smul m _ u
      (PancakeHigherDerivativeMoments.summable_fourierMoment_of_le u (by omega) hu))

theorem curl_coefficients (ρ : ℝ) (u : FourierVelocity) :
    fourierCurl (coefficients ρ u) = fourierCurl (fourierCurl u) - (ρ : ℂ) • fourierCurl u := by
  rw [coefficients, fourierCurl_sub, fourierCurl_smul]

theorem laplacian_spectral_factorization (ρ : ℝ) (u : FourierVelocity)
    (hd : ∀ q, modeDot q (u q) = 0) :
    -laplacianCoeff u - ((ρ ^ 2 : ℝ) : ℂ) • u =
      fourierCurl (coefficients ρ u) + (ρ : ℂ) • coefficients ρ u := by
  rw [curl_coefficients, fourierCurl_fourierCurl_eq_neg_laplacian u hd]
  ext q i
  simp only [coefficients, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.neg_apply, Complex.ofReal_pow]
  ring

theorem fullVorticity_sub (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) (x : T3) :
    fullVorticity (u - v) x = fullVorticity u x - fullVorticity v x := by
  have hs (w : FourierVelocity) (hw : Summable (fourierMoment 1 w)) :
      Summable (fun q ↦ ‖fourierCurl w q‖) := by
    exact summable_norm_curlCoefficients id w (by simpa only [indexedFirstMoment_id] using hw)
  simp only [fullVorticity, spatialCurl_velocity _ (summable_fourierMoment_sub 1 u v hu hv),
    spatialCurl_velocity u hu, spatialCurl_velocity v hv, fourierCurl_sub]
  change complexRealPartEuclideanCLM
    (fullFourierField id (fun q ↦ fourierCurl u q - fourierCurl v q) x) = _
  rw [PancakeLocalPressureEquation.fullFourierField_sub _ _ (hs u hu) (hs v hv)]
  exact map_sub _ _ _

theorem fullVorticity_real_smul (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    fullVorticity ((ρ : ℂ) • u) x = ρ • fullVorticity u x := by
  simp only [fullVorticity, spatialCurl_velocity _ (summable_fourierMoment_smul 1 _ u hu),
    spatialCurl_velocity u hu, fourierCurl_smul]
  change complexRealPartEuclideanCLM
    (fullFourierField id (fun q ↦ (ρ : ℂ) • fourierCurl u q) x) = _
  rw [fullFourierField_smul]
  change complexRealPartEuclideanCLM (ρ • fullFourierField id (fourierCurl u) x) = _
  exact complexRealPartEuclideanCLM.map_smul ρ _

theorem fullVorticity_coefficients (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) :
    fullVorticity (coefficients ρ u) x =
      fullVorticity (fourierCurl u) x - ρ • fullVorticity u x := by
  have hu1 := PancakeHigherDerivativeMoments.summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu
  rw [coefficients, fullVorticity_sub _ _ (summable_fourierMoment_curl 1 u hu)
    (summable_fourierMoment_smul 1 _ u hu1), fullVorticity_real_smul ρ u hu1]

theorem strainCoeff_sub (u v : FourierVelocity) (q : Wavevector) :
    strainCoeff (u - v) q = strainCoeff u q - strainCoeff v q := by
  simp only [sub_eq_add_neg, PancakeFourierPressureStrain.strainCoeff_add, strainCoeff_neg]

theorem strainCoeff_smul (c : ℂ) (u : FourierVelocity) (q : Wavevector) :
    strainCoeff (c • u) q = c • strainCoeff u q := by
  ext i j
  simp only [strainCoeff, gradientCoeff, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply,
    Matrix.add_apply, Matrix.transpose_apply]
  ring

theorem fullStrainOperator_sub (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) (x : T3) :
    fullStrainOperator (u - v) x = fullStrainOperator u x - fullStrainOperator v x := by
  have he := (hasSum_strain_matrix u hu x).sub (hasSum_strain_matrix v hv x)
  have hm := (hasSum_strain_matrix (u - v) (summable_fourierMoment_sub 1 u v hu hv) x).unique
    (he.congr_fun (fun q ↦ by rw [strainCoeff_sub, smul_sub]))
  change realMatrixOperatorCLM _ = realMatrixOperatorCLM _ - realMatrixOperatorCLM _
  rw [hm, map_sub]

theorem fullStrainOperator_real_smul (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    fullStrainOperator ((ρ : ℂ) • u) x = ρ • fullStrainOperator u x := by
  have he := (hasSum_strain_matrix u hu x).const_smul (ρ : ℂ)
  have hm := (hasSum_strain_matrix ((ρ : ℂ) • u)
    (summable_fourierMoment_smul 1 _ u hu) x).unique
      (he.congr_fun (fun q ↦ by rw [strainCoeff_smul]; exact smul_comm _ _ _))
  change realMatrixOperatorCLM _ = ρ • realMatrixOperatorCLM _
  rw [hm]
  exact realMatrixOperatorCLM.map_smul ρ _

/-- Both actual spatial remainders are generated by the same field defect. -/
theorem strain_spectral_factorization (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    fullStrainOperator (-laplacianCoeff u) x - ρ ^ 2 • fullStrainOperator u x =
      fullStrainOperator (fourierCurl (coefficients ρ u)) x +
        ρ • fullStrainOperator (coefficients ρ u) x := by
  have hu2 := PancakeHigherDerivativeMoments.summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hu1 := PancakeHigherDerivativeMoments.summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hw1 := summable_fourierMoment_curl 1 u hu2
  have hww1 := summable_fourierMoment_curl 1 _ (summable_fourierMoment_curl 2 u hu)
  rw [← fourierCurl_fourierCurl_eq_neg_laplacian u hd, curl_coefficients,
    fullStrainOperator_sub _ _ hww1 (summable_fourierMoment_smul 1 _ _ hw1),
    fullStrainOperator_real_smul ρ _ hw1, coefficients,
    fullStrainOperator_sub _ _ hw1 (summable_fourierMoment_smul 1 _ _ hu1),
    fullStrainOperator_real_smul ρ _ hu1]
  module

theorem centeredHelicityMoment_eq_curl_defect (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    centeredHelicityMoment ρ u = ∫ x : T3, ‖fullVorticity u x‖ ^ 6 *
      ⟪fullVorticity u x, fullVorticity (coefficients ρ u) x⟫ ^ 2 := by
  rw [centeredHelicityMoment_eq ρ u hu]
  simp only [fullVorticity_coefficients ρ u hu]

theorem weightedStrainSpectralDefect_eq (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0) :
    weightedStrainSpectralDefect (ρ ^ 2) u =
      ∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x,
        (fullStrainOperator (fourierCurl (coefficients ρ u)) x +
          ρ • fullStrainOperator (coefficients ρ u) x) (fullVorticity u x)⟫ := by
  simp only [weightedStrainSpectralDefect, strain_spectral_factorization ρ u hu hd]

end Mettapedia.FluidDynamics.NavierStokes.CurlEigenfieldDefect
