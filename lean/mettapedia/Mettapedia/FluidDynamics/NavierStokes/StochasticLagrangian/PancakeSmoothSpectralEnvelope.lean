import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeDiscardedNonlinearLimit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralResidualDepletion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalWeightedTransport

/-!
# Actual vorticity and gap-weight bounds under a smooth Fourier envelope

The constants depend on a supplied summable Fourier envelope, not on the
retained set. Such bounds permit a consistency limit on a smooth field;
they are not estimates in terms of initial kinetic energy alone.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSmoothSpectralEnvelope

open scoped Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeDyadicDirectionEvolution
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeExteriorReconstructionTail PancakePhysicalSpectralDefect PancakeFourierStrainGradient
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierPressureStrain
open PancakeIncomingLowSourceEnergy PancakeSpectralResidualDepletion PancakeRegularizedDiffusion
open PancakePhysicalWeightedTransport PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "T3" => UnitAddTorus (Fin 3)

theorem norm_coefficient_le_firstMoment (u : FourierVelocity) (k : Wavevector) :
    ‖coefficientVec (u k)‖ ≤ fourierMoment 1 u k := by
  simp only [fourierMoment, pow_one]
  nlinarith [mul_nonneg (norm_nonneg (frequencyVec k)) (norm_nonneg (coefficientVec (u k)))]

theorem norm_spatialVorticity_le_envelope (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : ∀ k, fourierMoment 2 u k ≤ g k) (x : T3) :
    ‖spatialVorticity modes u x‖ ≤ (2 * Real.pi) * ∑' k, g k := by
  apply (norm_real_reconstruction_le_sum modes (fourierCurl u) x).trans
  calc
    _ ≤ ∑ k ∈ modes, (2 * Real.pi) * g k := by
      apply Finset.sum_le_sum
      intro k _
      exact ((norm_coefficient_le_firstMoment (fourierCurl u) k).trans (firstMoment_curl_le_second u k)).trans
        (mul_le_mul_of_nonneg_left (hu k) (by positivity))
    _ = (2 * Real.pi) * ∑ k ∈ modes, g k := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hSum.sum_le_tsum modes (fun k _ ↦ hg k)) (by positivity)

theorem norm_strainCoeff_filtered_le_envelope (g : Wavevector → ℝ) (u : FourierVelocity)
    (chi : Wavevector → ℂ) (B : ℝ) (hB : 0 ≤ B) (hchi : ∀ k, ‖chi k‖ ≤ B)
    (hu : ∀ k, fourierMoment 2 u k ≤ g k) (k : Wavevector) :
    ‖strainCoeff (filteredVelocity chi u) k‖ ≤ (2 * Real.pi) * B * g k := by
  have hm : ‖frequencyVec k‖ * ‖coefficientVec (u k)‖ ≤ fourierMoment 2 u k := by
    apply (show ‖frequencyVec k‖ * ‖coefficientVec (u k)‖ ≤ fourierMoment 1 u k from ?_).trans (firstMoment_le_second u k)
    simp only [fourierMoment, pow_one]
    nlinarith [norm_nonneg (coefficientVec (u k))]
  calc
    _ ≤ ‖PancakePeriodicVorticityEquation.unitTorusDerivativePhase‖ * ‖frequencyVec k‖ *
        ‖coefficientVec (filteredVelocity chi u k)‖ := norm_strainCoeff_le _ _
    _ = (2 * Real.pi) * ‖frequencyVec k‖ * (‖chi k‖ * ‖coefficientVec (u k)‖) := by
      rw [norm_derivativePhase, norm_coefficientVec_filtered]
    _ ≤ (2 * Real.pi) * ‖frequencyVec k‖ * (B * ‖coefficientVec (u k)‖) := by gcongr; exact hchi k
    _ = (2 * Real.pi) * B * (‖frequencyVec k‖ * ‖coefficientVec (u k)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hm.trans (hu k)) (by positivity)

theorem norm_spatialStrain_le_envelope (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (modes : Finset Wavevector) (u : FourierVelocity) (chi : Wavevector → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hchi : ∀ k, ‖chi k‖ ≤ B)
    (hu : ∀ k, fourierMoment 2 u k ≤ g k) (x : T3) :
    ‖(spatialStrain modes (filteredVelocity chi u) x).1‖ ≤ 9 * (2 * Real.pi) * B * ∑' k, g k := by
  apply (norm_realMatrixOperator_le _).trans
  calc
    _ ≤ 9 * ∑ k ∈ modes, ‖strainCoeff (filteredVelocity chi u) k‖ :=
      mul_le_mul_of_nonneg_left (norm_matrixReconstruction_le _ _ _) (by positivity)
    _ ≤ 9 * ∑ k ∈ modes, (2 * Real.pi) * B * g k :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ ↦ norm_strainCoeff_filtered_le_envelope g u chi B hB hchi hu k)) (by positivity)
    _ = 9 * (2 * Real.pi) * B * ∑ k ∈ modes, g k := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hSum.sum_le_tsum modes (fun k _ ↦ hg k)) (by positivity)

theorem norm_regularizedGap_zero_le (S : SymmetricStrain) : ‖regularizedGap S 0‖ ≤ 2 * ‖S.1‖ := by
  have he := abs_orderedEigenvalue_le_opNorm S 0
  change |topEigenvalue S| ≤ ‖S.1‖ at he
  calc
    _ ≤ ‖(topEigenvalue S + 0) • (1 : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (EuclideanSpace ℝ (Fin 3)))‖ + ‖S.1‖ := norm_sub_le _ _
    _ = |topEigenvalue S| + ‖S.1‖ := by simp only [add_zero, norm_smul, norm_one, Real.norm_eq_abs, mul_one]
    _ ≤ _ := by linarith

theorem norm_physicalGapWeight_le_envelope (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (modes : Finset Wavevector) (u : FourierVelocity) (chi : Wavevector → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hchi : ∀ k, ‖chi k‖ ≤ B)
    (hu : ∀ k, fourierMoment 2 u k ≤ g k) (x : T3) :
    ‖physicalGapWeight chi modes u 0 x‖ ≤ 18 * (2 * Real.pi) * B * ∑' k, g k := by
  apply (norm_regularizedGap_zero_le _).trans
  calc
    _ ≤ 2 * (9 * (2 * Real.pi) * B * ∑' k, g k) :=
      mul_le_mul_of_nonneg_left (norm_spatialStrain_le_envelope g hg hSum modes u chi B hB hchi hu x) (by positivity)
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PancakeSmoothSpectralEnvelope
