import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMappedFourierDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLowDiffusionBudget

/-!
# Paid spatial diffusion for the constructed finite Fourier fields

The strain and vorticity are the actual real Fourier reconstructions. Their
central-difference consistency and strain first-increment estimates are
proved from the coefficients, not supplied as assumptions. The conclusion
bounds an integrable full-rate envelope for one coordinate diffusion.
It is not an all-scale estimate or the full material/advection balance.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalDiffusionLimit

open scoped Topology Matrix.Norms.Elementwise
open MeasureTheory PeriodicFourierTriad PancakePeriodicVorticityEquation
open PancakePeriodicCoherentSplit PancakeFourierPressureStrain PancakeFourierMaterialPaths
open PancakeFourierStrainGradient PancakeMappedFourierDiffusion PancakeFourierTranslationCurve
open PancakeWeakDiffusionLimit PancakePhysicalSpectralDefect PancakeDyadicDirectionEvolution
open PancakeRegularizedMaterialRate PancakeFilteredStrainDynamics
open PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakePressureAnisotropyBudget PancakeLowDiffusionBudget PancakeViscousMisalignmentAbsorption

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fourierField_matrix_eq (modes : Finset Wavevector) (a : FourierMatrix) (x : T3) :
    fourierField modes a x = matrixReconstruction modes a x := by
  simp [fourierField, modeField, matrixReconstruction]

theorem fourierField_vector_eq (modes : Finset Wavevector) (a : FourierVelocity) (x : T3) :
    fourierField modes a x = finiteFourierReconstruction modes a x := by
  simp [fourierField, modeField, finiteFourierReconstruction]

theorem mappedField_strain (modes : Finset Wavevector) (u : FourierVelocity) :
    mappedField realMatrixOperatorCLM modes (strainCoeff u) = fun x ↦ (spatialStrain modes u x).1 := by
  funext x
  simp only [mappedField, fourierField_matrix_eq, spatialStrain]
  rfl

theorem mappedField_vorticity (modes : Finset Wavevector) (u : FourierVelocity) :
    mappedField complexRealPartEuclideanCLM modes (fourierCurl u) = spatialVorticity modes u := by
  funext x
  simp only [mappedField, fourierField_vector_eq, complexRealPartEuclideanCLM_apply, spatialVorticity]

def strainSecond (modes : Finset Wavevector) (u : FourierVelocity) (j : Fin 3) : T3 → R3 →L[ℝ] R3 :=
  mappedSecond realMatrixOperatorCLM modes (strainCoeff u) j

def vorticitySecond (modes : Finset Wavevector) (u : FourierVelocity) (j : Fin 3) : T3 → R3 :=
  mappedSecond complexRealPartEuclideanCLM modes (fourierCurl u) j

def vorticityGradient (modes : Finset Wavevector) (u : FourierVelocity) (j : Fin 3) : T3 → R3 :=
  mappedField complexRealPartEuclideanCLM modes (derivativeCoeff j (fourierCurl u))

theorem mappedField_strainGradient (modes : Finset Wavevector) (u : FourierVelocity) (j : Fin 3) :
    mappedField realMatrixOperatorCLM modes (derivativeCoeff j (strainCoeff u)) =
      fun x ↦ strainGradient modes u x j := by
  funext x
  simp only [mappedField, fourierField_matrix_eq, strainGradient]
  rfl

/-- The coefficient-defined strainSecond is the derivative of the actual
coordinate strain gradient, not a free diffusion direction. -/
theorem hasDerivAt_strainGradient_shift (modes : Finset Wavevector) (u : FourierVelocity)
    (j : Fin 3) (h : ℝ) (x : T3) :
    HasDerivAt (fun t ↦ strainGradient modes u (x + coordinateShift j t) j)
      (strainSecond modes u j (x + coordinateShift j h)) h := by
  have hd := hasDerivAt_mappedField_shift realMatrixOperatorCLM modes
    (derivativeCoeff j (strainCoeff u)) j h x
  simpa only [mappedField_strainGradient, strainSecond, mappedSecond] using hd

theorem hasDerivAt_spatialVorticity_shift (modes : Finset Wavevector) (u : FourierVelocity)
    (j : Fin 3) (h : ℝ) (x : T3) :
    HasDerivAt (fun t ↦ spatialVorticity modes u (x + coordinateShift j t))
      (vorticityGradient modes u j (x + coordinateShift j h)) h := by
  have hd := hasDerivAt_mappedField_shift complexRealPartEuclideanCLM modes (fourierCurl u) j h x
  simpa only [mappedField_vorticity, vorticityGradient] using hd

theorem hasDerivAt_vorticityGradient_shift (modes : Finset Wavevector) (u : FourierVelocity)
    (j : Fin 3) (h : ℝ) (x : T3) :
    HasDerivAt (fun t ↦ vorticityGradient modes u j (x + coordinateShift j t))
      (vorticitySecond modes u j (x + coordinateShift j h)) h := by
  exact hasDerivAt_mappedField_shift complexRealPartEuclideanCLM modes
    (derivativeCoeff j (fourierCurl u)) j h x

theorem strainDerivativeSum_le_amplitude (outputs : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (j : Fin 3) :
    9 * (∑ q ∈ outputs, ‖derivativeCoeff j (strainCoeff (filteredVelocity chi u)) q‖) ≤
      strainGradientAmplitude outputs chi u := by
  calc
    _ ≤ 9 * (∑ q ∈ outputs, ‖unitTorusDerivativePhase‖ ^ 2 * ‖frequencyVec q‖ ^ 2 *
        ‖PancakeFrequencyProjectorCommutator.coefficientVec (filteredVelocity chi u q)‖) := by
      gcongr with q hq
      exact norm_strainDerivativeCoeff_le j _ q
    _ = _ := by
      simp only [norm_coefficientVec_filtered, strainGradientAmplitude, strainGradientWeight,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

theorem norm_strain_shift_le_amplitude (outputs : Finset Wavevector) (chi : Wavevector → ℂ)
    (u : FourierVelocity) (j : Fin 3) (h : ℝ) (x : T3) :
    ‖(spatialStrain outputs (filteredVelocity chi u) (x + coordinateShift j h)).1 -
      (spatialStrain outputs (filteredVelocity chi u) x).1‖ ≤
      strainGradientAmplitude outputs chi u * |h| := by
  have hm := norm_mappedField_increment_le realMatrixOperatorCLM outputs
    (strainCoeff (filteredVelocity chi u)) j 9 h x (by norm_num) norm_realMatrixOperator_le
  rw [mappedField_strain] at hm
  exact hm.trans (mul_le_mul_of_nonneg_right
    (strainDerivativeSum_le_amplitude outputs chi u j) (abs_nonneg h))

/-- Actual physical fields discharge all finite-difference approximation
hypotheses. Only the full-rate envelope and its integrability remain input. -/
theorem integral_coordinate_diffusion_paid
    (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ) (u : FourierVelocity)
    (j : Fin 3) (F B : T3 → ℝ) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu)
    (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (spatialStrain outputs (filteredVelocity chi u) x)
      delta (spatialVorticity modes u x) (strainSecond outputs (filteredVelocity chi u) j x)
      (vorticitySecond modes u j x) + B x) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) * strainGradientAmplitude outputs chi u ^ 2 *
      (∫ x : T3, ‖spatialVorticity modes u x‖ ^ 2) + ∫ x : T3, B x := by
  have hS : Continuous (spatialStrain outputs (filteredVelocity chi u)) := by
    apply Continuous.subtype_mk
    have hc := continuous_mappedField realMatrixOperatorCLM outputs (strainCoeff (filteredVelocity chi u))
    rw [mappedField_strain] at hc
    exact hc
  have hw : Continuous (spatialVorticity modes u) := by
    rw [← mappedField_vorticity]
    exact continuous_mappedField _ _ _
  have hL : 0 ≤ strainGradientAmplitude outputs chi u := by
    unfold strainGradientAmplitude
    exact Finset.sum_nonneg (fun q _ ↦ mul_nonneg (strainGradientWeight_nonneg chi q) (norm_nonneg _))
  apply integral_rate_le_of_uniform_central_approx
    (spatialStrain outputs (filteredVelocity chi u)) (spatialVorticity modes u)
    (strainSecond outputs (filteredVelocity chi u) j) (vorticitySecond modes u j) F B delta nu
    (strainGradientAmplitude outputs chi u) (coordinateShift j)
    (uniformError outputs (strainCoeff (filteredVelocity chi u)) j 9)
    (uniformError modes (fourierCurl u) j ‖complexRealPartEuclideanCLM‖)
    hd hnu hL hS hw hF hB hpoint
  · intro h _ x
    have he := norm_mappedSecond_sub_central_le realMatrixOperatorCLM outputs
      (strainCoeff (filteredVelocity chi u)) j 9 h x (by norm_num) norm_realMatrixOperator_le
    simpa only [mappedField_strain, strainSecond] using he
  · intro h _ x
    have he := norm_mappedSecond_sub_central_le complexRealPartEuclideanCLM modes
      (fourierCurl u) j ‖complexRealPartEuclideanCLM‖ h x (norm_nonneg _)
      complexRealPartEuclideanCLM.le_opNorm
    simpa only [mappedField_vorticity, vorticitySecond] using he
  · intro h _ x
    exact norm_strain_shift_le_amplitude outputs chi u j h x
  · intro h _ x
    simpa only [coordinateShift_neg, abs_neg] using
      norm_strain_shift_le_amplitude outputs chi u j (-h) x
  · exact uniformError_tendsto _ _ _ _
  · exact uniformError_tendsto _ _ _ _

theorem integral_spatialVorticity_sq_le (modes : Finset Wavevector) (u : FourierVelocity) :
    (∫ x : T3, ‖spatialVorticity modes u x‖ ^ 2) ≤ fullEnergy modes (fourierCurl u) := by
  have hi : Integrable (fun x : T3 ↦ ‖coefficientVec
      (finiteFourierReconstruction modes (fourierCurl u) x)‖ ^ 2) :=
    (continuous_coefficientReconstruction modes (fourierCurl u)).norm.pow 2
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x : T3 ↦
    sq_nonneg ‖spatialVorticity modes u x‖)) hi
      (Filter.Eventually.of_forall (fun x : T3 ↦
        norm_realPart_sq_le (finiteFourierReconstruction modes (fourierCurl u) x)))
  rwa [integral_norm_coefficientReconstruction_sq] at hm

/-- The physical spatial inequality with the fixed-low coefficient-energy
price. There is no factor counting the retained high-frequency modes. -/
theorem integral_coordinate_diffusion_energy_paid
    (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ) (u : FourierVelocity)
    (j : Fin 3) (F B : T3 → ℝ) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu)
    (hsub : outputs ⊆ modes) (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (spatialStrain outputs (filteredVelocity chi u) x)
      delta (spatialVorticity modes u x) (strainSecond outputs (filteredVelocity chi u) j x)
      (vorticitySecond modes u j x) + B x) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) * (∑ q ∈ outputs, strainGradientWeight chi q ^ 2) *
      fullEnergy modes u * fullEnergy modes (fourierCurl u) + ∫ x : T3, B x := by
  apply (integral_coordinate_diffusion_paid outputs modes chi u j F B delta nu hd hnu hF hB hpoint).trans
  have hp := mul_le_mul (strainGradientAmplitude_sq_le outputs modes chi u hsub)
    (integral_spatialVorticity_sq_le modes u)
    (integral_nonneg (fun _ ↦ sq_nonneg _))
    (mul_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) (fullEnergy_nonneg modes u))
  have hc := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 16 * nu / delta)
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalDiffusionLimit
