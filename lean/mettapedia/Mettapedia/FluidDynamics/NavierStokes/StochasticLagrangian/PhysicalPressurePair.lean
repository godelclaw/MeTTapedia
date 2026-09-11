import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ComplexPressureConvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeZeroModeCurlBridge
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfinitePressureCoefficients

/-!
# Identifying pressure pairs with the actual pressure Hessian

The trace of the physical pressure Hessian is the negative of the complex
Biot--Savart pair convolution of the actual Fourier curl. Mean velocity is
allowed: its pressure interactions vanish by incompressibility. Both finite
and convergent infinite convection coefficients use the existing definitions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PhysicalPressurePair

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator
open PancakeGalerkinKineticEnergy PancakeZeroModeCurlBridge PancakeFourierPressureStrain
open PancakeLowPressureBudget ComplexPressurePair ComplexPressureConvolution
open FourierPressureTraceSymbol PancakeCoefficientLimitEquation PancakeInfinitePressureCoefficients
open PancakeLocalVelocityExistence PancakeInfiniteVelocityEnvelope PancakeCurlOutputTail
open PancakeSobolevFiberEnvelope

theorem tracePair_fourierCurl (u : FourierVelocity) (k p : Wavevector)
    (hk : modeDot k (u k) = 0) (hp : modeDot p (u p) = 0) :
    tracePair k p (fourierCurl u k) (fourierCurl u p) =
      unitTorusDerivativePhase ^ 2 * (modeDot p (u k) * modeDot k (u p)) := by
  by_cases hk0 : k = 0
  · subst k
    simp [tracePair, complexBiotSavartAmp, modeSquare, modeDot]
  by_cases hp0 : p = 0
  · subst p
    simp [tracePair, complexBiotSavartAmp, modeSquare, modeDot]
  have h := physical_tracePair_eq k p (fourierCurl u k) (fourierCurl u p)
  rw [physicalBiotSavart_fourierCurl k u (frequencyVec_ne_zero hk0) hk,
    physicalBiotSavart_fourierCurl p u (frequencyVec_ne_zero hp0) hp] at h
  linear_combination h

theorem pressureHessian_trace_eq_pairSum (M : Finset Wavevector) (u : FourierVelocity)
    (hu : ∀ k ∈ M, modeDot k (u k) = 0) (q : Wavevector) :
    (pressureHessianCoeff M u q).trace =
      -(∑ kp ∈ interactionPairs M q, tracePair kp.1 kp.2 (fourierCurl u kp.1) (fourierCurl u kp.2)) := by
  rw [pressureHessianCoeff_trace, pressure_numerator_output_pair M u q hu, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro kp hkp
  have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hkp).1
  have hq := (Finset.mem_filter.mp hkp).2
  rw [tracePair_fourierCurl u kp.1 kp.2 (hu _ hmem.1) (hu _ hmem.2), ← hq,
    modeDot_add_wavevector, modeDot_add_wavevector, hu _ hmem.1, hu _ hmem.2]
  ring

theorem pressureHessian_tilt_eq_pairConvolution
    (e : EuclideanSpace ℝ (Fin 3)) (M : Finset Wavevector) (u : FourierVelocity)
    (hu : ∀ k ∈ M, modeDot k (u k) = 0) (q : Wavevector) :
    (pressureHessianCoeff M u q).trace • complexTiltSymbol e q =
      -pairConvolution e M M (fourierCurl u) (fourierCurl u) q := by
  rw [pressureHessian_trace_eq_pairSum M u hu, neg_smul, Finset.sum_smul]
  congr 1
  unfold pairConvolution interactionPairs
  apply Finset.sum_congr rfl
  intro kp hkp
  rw [tiltPair, (Finset.mem_filter.mp hkp).2]

theorem sum_pressureHessian_tilt_sq_le (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1)
    (M Q : Finset Wavevector) (u : FourierVelocity)
    (hu : ∀ k ∈ M, modeDot k (u k) = 0)
    (hQ : ∀ k ∈ M, ∀ p ∈ M, k + p ∈ Q) :
    (∑ q ∈ Q, ‖(pressureHessianCoeff M u q).trace • complexTiltSymbol e q‖ ^ 2) ≤
      8 * (∑ k ∈ M, ‖ComplexTransverseMatrix.transverse e (coefficientVec (fourierCurl u k))‖) ^ 2 *
        (∑ k ∈ M, ‖coefficientVec (fourierCurl u k)‖ ^ 2) +
      8 * (∑ k ∈ M, ‖coefficientVec (fourierCurl u k)‖) ^ 2 *
        (∑ k ∈ M, ‖ComplexTransverseMatrix.transverse e (coefficientVec (fourierCurl u k))‖ ^ 2) := by
  simp only [pressureHessian_tilt_eq_pairConvolution e M u hu, norm_neg]
  have h := sum_norm_pairConvolution_sq_le e he M M Q (fourierCurl u) (fourierCurl u) hQ
  simpa only [localizationDefect_eq_of_divergenceFree e _ _ (fourierCurl_transverse _ u)] using h

theorem modeDot_infiniteConvection (u : FourierVelocity) (q : Wavevector)
    (hu : ∀ i, Summable (fun k ↦ outputFiber q u k i)) :
    modeDot q (infiniteConvection u q) =
      ∑' k, modeDot q (u k) * modeDot q (u (q - k)) := by
  simp only [modeDot, infiniteConvection, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun i _ ↦ (hu i).mul_left (q i : ℂ))]
  apply tsum_congr
  intro k
  simp only [outputFiber, modeDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem traceAmplitude_eq_tsum_pairs (chi : Wavevector → ℂ) (u : FourierVelocity)
    (hd : ∀ k, modeDot k (u k) = 0) (q : Wavevector)
    (hu : ∀ i, Summable (fun k ↦ outputFiber q u k i)) :
    traceAmplitude chi u q =
      -chi q * ∑' k, tracePair k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) := by
  have ht (k : Wavevector) : tracePair k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) =
      unitTorusDerivativePhase ^ 2 * (modeDot q (u k) * modeDot q (u (q - k))) := by
    rw [tracePair_fourierCurl u k (q - k) (hd k) (hd (q - k))]
    have hq : q = k + (q - k) := by abel
    have h1 : modeDot q (u k) = modeDot (q - k) (u k) := by
      conv_lhs => arg 1; rw [hq]
      rw [modeDot_add_wavevector, hd k, zero_add]
    have h2 : modeDot q (u (q - k)) = modeDot k (u (q - k)) := by
      conv_lhs => arg 1; rw [hq]
      rw [modeDot_add_wavevector, hd (q - k), add_zero]
    rw [h1, h2]
  have htrace : traceAmplitude chi u q =
      chi q * unitTorusDerivativePhase ^ 2 *
        (modeSquare q * infinitePressureCoeff u q) := by
    rw [modeSquare_eq_real]
    unfold traceAmplitude FourierPressureTiltEnergy.pressureAmplitude
    ring
  rw [htrace, infinitePressureCoeff_poisson, modeDot_infiniteConvection u q hu]
  simp only [ht, tsum_mul_left]
  ring

theorem traceAmplitude_eq_tsum_pairs_of_moment (chi : Wavevector → ℂ) (u : FourierVelocity)
    (hd : ∀ k, modeDot k (u k) = 0) (hu : Summable (fourierMoment 2 u)) (q : Wavevector) :
    traceAmplitude chi u q =
      -chi q * ∑' k, tracePair k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) := by
  apply traceAmplitude_eq_tsum_pairs chi u hd q
  intro i
  exact ((summable_pairEnvelope (fourierMoment 2 u) (fourierMoment_nonneg _ _) hu).prod_factor q).of_norm_bounded
    (fun k ↦ norm_outputFiber_le_momentEnvelope u (fourierMoment 2 u)
      (fourierMoment_nonneg _ _) (fun _ ↦ le_rfl) q k i)

theorem summable_norm_fourierCurl (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Summable (fun k ↦ ‖coefficientVec (fourierCurl u k)‖) := by
  apply (summable_firstMoment_curl u hu).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro k
  unfold fourierMoment
  rw [pow_one]
  nlinarith only [mul_nonneg (norm_nonneg (frequencyVec k)) (norm_nonneg (coefficientVec (fourierCurl u k)))]

/-- Actual infinite pressure-tilt coefficients, with convergence of the
curl-inverted pair series proved from the velocity's second moment. -/
theorem tiltCoefficient_eq_tsum_pairs (chi : Wavevector → ℂ) (u : FourierVelocity)
    (hd : ∀ k, modeDot k (u k) = 0) (hu : Summable (fourierMoment 2 u))
    (e : EuclideanSpace ℝ (Fin 3)) (q : Wavevector) :
    coefficientVec (FourierPressureTiltEnergy.tiltCoefficient chi u e q) =
      (-chi q) • ∑' k, tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) := by
  have hw := summable_norm_fourierCurl u hu
  have hs := summable_tracePair (fourierCurl u) (fourierCurl u) hw hw q
  have ht (k : Wavevector) : tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) =
      tracePair k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) • complexTiltSymbol e q := by
    rw [tiltPair, show k + (q - k) = q by abel]
  simp only [ht, hs.tsum_smul_const]
  rw [coefficientVec_tiltCoefficient_eq, traceAmplitude_eq_tsum_pairs_of_moment chi u hd hu q, smul_smul]

end Mettapedia.FluidDynamics.NavierStokes.PhysicalPressurePair
