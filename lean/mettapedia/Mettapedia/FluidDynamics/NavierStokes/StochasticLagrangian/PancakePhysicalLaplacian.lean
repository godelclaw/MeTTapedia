import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalDiffusionLimit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLaplacianDiffusion

/-!
# The actual Fourier Laplacian and joint paid diffusion

The three coordinate second derivatives are combined as a single operator.
Its Fourier multiplier is identified with the physical viscous coefficient.
Only the full-rate envelope, not each selected-frame response, is integrated.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalLaplacian

open scoped Topology Matrix.Norms.Elementwise
open MeasureTheory PeriodicFourierTriad PancakePeriodicVorticityEquation PancakePeriodicCoherentSplit
open PancakeFourierMaterialPaths PancakeFourierStrainGradient PancakeMappedFourierDiffusion
open PancakeFourierTranslationCurve PancakeWeakDiffusionLimit PancakePhysicalDiffusionLimit
open PancakePhysicalSpectralDefect PancakeDyadicDirectionEvolution PancakeRegularizedMaterialRate
open PancakeFilteredStrainDynamics PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeLaplacianDiffusion PancakeViscousMisalignmentAbsorption PancakeFourierPressureStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def strainLaplacian (modes : Finset Wavevector) (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  ∑ j : Fin 3, strainSecond modes u j x

def vorticityLaplacian (modes : Finset Wavevector) (u : FourierVelocity) (x : T3) : R3 :=
  ∑ j : Fin 3, vorticitySecond modes u j x

section Coefficients

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

def laplacianCoeff (a : Wavevector → E) (q : Wavevector) : E :=
  (unitTorusDerivativePhase ^ 2 * modeSquare q) • a q

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem sum_secondCoeff (a : Wavevector → E) (q : Wavevector) :
    (∑ j : Fin 3, derivativeCoeff j (derivativeCoeff j a) q) = laplacianCoeff a q := by
  simp only [derivativeCoeff, smul_smul, ← Finset.sum_smul, laplacianCoeff]
  congr 1
  simp only [modeSquare, Fin.sum_univ_three]
  ring

omit [IsScalarTower ℝ ℂ E] in
theorem sum_mappedSecond (Q : E →L[ℝ] V) (modes : Finset Wavevector)
    (a : Wavevector → E) (x : T3) :
    (∑ j : Fin 3, mappedSecond Q modes a j x) = mappedField Q modes (laplacianCoeff a) x := by
  simp only [mappedSecond, mappedField, fourierField, ContinuousMap.sum_apply, modeField,
    ContinuousMap.coe_mk, ← map_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [← Finset.smul_sum, sum_secondCoeff]

omit [IsScalarTower ℝ ℂ E] in
theorem mappedField_real_smul (Q : E →L[ℝ] V) (modes : Finset Wavevector)
    (a : Wavevector → E) (c : ℝ) (x : T3) :
    mappedField Q modes (fun q ↦ c • a q) x = c • mappedField Q modes a x := by
  simp only [mappedField, fourierField, ContinuousMap.sum_apply, modeField, ContinuousMap.coe_mk,
    smul_comm (UnitAddTorus.mFourier _ _) c, ← Finset.smul_sum, map_smul]

end Coefficients

theorem strainLaplacian_eq (modes : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    strainLaplacian modes u x =
      realMatrixOperator (matrixReconstruction modes (laplacianCoeff (strainCoeff u)) x) := by
  have h := sum_mappedSecond realMatrixOperatorCLM modes (strainCoeff u) x
  simp only [mappedField, fourierField_matrix_eq] at h
  exact h

theorem vorticityLaplacian_eq (modes : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    vorticityLaplacian modes u x = complexRealPartEuclideanCLM
      (finiteFourierReconstruction modes (laplacianCoeff (fourierCurl u)) x) := by
  unfold vorticityLaplacian vorticitySecond
  rw [sum_mappedSecond]
  simp only [mappedField, fourierField_vector_eq]

theorem viscousStrainCoeff_eq (nu : ℝ) (u : FourierVelocity) (q : Wavevector) :
    viscousStrainCoeff nu u q = nu • laplacianCoeff (strainCoeff u) q := by
  rw [viscousStrainCoeff, viscousGradientCoeff, map_smul, symmetrize_gradient]
  simp only [laplacianCoeff, ← Complex.coe_smul, smul_smul]
  congr 1
  ring

theorem viscousVorticityCoeff_eq (nu : ℝ) (a : FourierVelocity) (q : Wavevector) :
    unitTorusViscousVorticityCoeff nu a q = nu • laplacianCoeff a q := by
  simp only [unitTorusViscousVorticityCoeff, laplacianCoeff, ← Complex.coe_smul, smul_smul]
  congr 1
  ring

theorem reconstructed_viscousStrain (modes : Finset Wavevector) (nu : ℝ)
    (u : FourierVelocity) (x : T3) :
    realMatrixOperator (matrixReconstruction modes (viscousStrainCoeff nu u) x) =
      nu • strainLaplacian modes u x := by
  have hm := mappedField_real_smul realMatrixOperatorCLM modes (laplacianCoeff (strainCoeff u)) nu x
  simp only [mappedField, fourierField_matrix_eq] at hm
  change realMatrixOperator (matrixReconstruction modes (fun q ↦ nu • laplacianCoeff (strainCoeff u) q) x) =
    nu • realMatrixOperator (matrixReconstruction modes (laplacianCoeff (strainCoeff u)) x) at hm
  rw [strainLaplacian_eq]
  simpa only [← viscousStrainCoeff_eq] using hm

theorem reconstructed_viscousVorticity (modes : Finset Wavevector) (nu : ℝ)
    (u : FourierVelocity) (x : T3) :
    complexRealPartEuclideanCLM
      (finiteFourierReconstruction modes (unitTorusViscousVorticityCoeff nu (fourierCurl u)) x) =
      nu • vorticityLaplacian modes u x := by
  have hm := mappedField_real_smul complexRealPartEuclideanCLM modes (laplacianCoeff (fourierCurl u)) nu x
  simp only [mappedField, fourierField_vector_eq] at hm
  rw [vorticityLaplacian_eq]
  simpa only [← viscousVorticityCoeff_eq] using hm

/-- The full three-dimensional diffusion estimate. The coordinate
responses are never assumed separately measurable or integrable. -/
theorem integral_laplacian_diffusion_paid
    (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ) (u : FourierVelocity)
    (F B : T3 → ℝ) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu)
    (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (spatialStrain outputs (filteredVelocity chi u) x)
      delta (spatialVorticity modes u x) (strainLaplacian outputs (filteredVelocity chi u) x)
      (vorticityLaplacian modes u x) + B x) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) * (3 * strainGradientAmplitude outputs chi u ^ 2) *
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
  have hh := integral_joint_rate_le_of_uniform_approx (Finset.univ : Finset (Fin 3))
    (spatialStrain outputs (filteredVelocity chi u)) (spatialVorticity modes u)
    (strainSecond outputs (filteredVelocity chi u)) (vorticitySecond modes u) F B delta nu
    (fun _ ↦ strainGradientAmplitude outputs chi u) coordinateShift
    (fun j ↦ uniformError outputs (strainCoeff (filteredVelocity chi u)) j 9)
    (fun j ↦ uniformError modes (fourierCurl u) j ‖complexRealPartEuclideanCLM‖)
    hd hnu (fun _ _ ↦ hL) hS hw hF hB hpoint
    (fun h _ j _ x ↦ by
      have he := norm_mappedSecond_sub_central_le realMatrixOperatorCLM outputs
        (strainCoeff (filteredVelocity chi u)) j 9 h x (by norm_num) norm_realMatrixOperator_le
      simpa only [mappedField_strain, strainSecond] using he)
    (fun h _ j _ x ↦ by
      have he := norm_mappedSecond_sub_central_le complexRealPartEuclideanCLM modes
        (fourierCurl u) j ‖complexRealPartEuclideanCLM‖ h x (norm_nonneg _)
        complexRealPartEuclideanCLM.le_opNorm
      simpa only [mappedField_vorticity, vorticitySecond] using he)
    (fun h _ j _ x ↦ norm_strain_shift_le_amplitude outputs chi u j h x)
    (fun h _ j _ x ↦ by
      simpa only [coordinateShift_neg, abs_neg] using norm_strain_shift_le_amplitude outputs chi u j (-h) x)
    (fun _ _ ↦ uniformError_tendsto _ _ _ _) (fun _ _ ↦ uniformError_tendsto _ _ _ _)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hh

theorem integral_laplacian_diffusion_energy_paid
    (outputs modes : Finset Wavevector) (chi : Wavevector → ℂ) (u : FourierVelocity)
    (F B : T3 → ℝ) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu)
    (hsub : outputs ⊆ modes) (hF : Integrable F) (hB : Integrable B)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (spatialStrain outputs (filteredVelocity chi u) x)
      delta (spatialVorticity modes u x) (strainLaplacian outputs (filteredVelocity chi u) x)
      (vorticityLaplacian modes u x) + B x) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) * strainGradientCutoffWeight outputs chi *
      fullEnergy modes u * fullEnergy modes (fourierCurl u) + ∫ x : T3, B x := by
  apply (integral_laplacian_diffusion_paid outputs modes chi u F B delta nu hd hnu hF hB hpoint).trans
  have ha : 3 * strainGradientAmplitude outputs chi u ^ 2 ≤
      strainGradientCutoffWeight outputs chi * fullEnergy modes u := by
    have h := strainGradientAmplitude_sq_le outputs modes chi u hsub
    unfold strainGradientCutoffWeight
    nlinarith
  have hp := mul_le_mul ha (integral_spatialVorticity_sq_le modes u)
    (integral_nonneg (fun _ ↦ sq_nonneg _))
    (mul_nonneg (strainGradientCutoffWeight_nonneg outputs chi) (fullEnergy_nonneg modes u))
  have hc := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 16 * nu / delta)
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalLaplacian
