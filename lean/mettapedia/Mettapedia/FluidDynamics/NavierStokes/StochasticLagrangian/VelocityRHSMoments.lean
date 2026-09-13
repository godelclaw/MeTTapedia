import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeVelocityGradientEnvelope

/-!
# Absolute moments of the full velocity equation

A common input moment of order `m + 2` dominates the `m`th absolute
moment of the actual infinite Navier--Stokes right-hand side. The
same convolution envelope works for every order; its size is not a
dynamical initial-data bound. These estimates justify differentiation
of higher spatial derivatives along the local evolution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VelocityRHSMoments

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeInfiniteVelocityEnvelope
open PancakeSobolevFiberEnvelope PancakeCoefficientLimitEquation PancakeFixedOutputVelocityBound
open PancakeLowPressureBudget PancakePhysicalSixthDecay PancakePeriodicVorticityEquation
open PancakeIncomingLowSourceEnergy

theorem one_add_norm_output_le (q k : Wavevector) :
    1 + ‖frequencyVec q‖ ≤ (1 + ‖frequencyVec k‖) * (1 + ‖frequencyVec (q - k)‖) := by
  have hq : q = k + (q - k) := by abel
  have hnorm : ‖frequencyVec q‖ ≤ ‖frequencyVec k‖ + ‖frequencyVec (q - k)‖ := by
    conv_lhs => rw [hq, frequencyVec_add]
    exact norm_add_le _ _
  nlinarith [mul_nonneg (norm_nonneg (frequencyVec k)) (norm_nonneg (frequencyVec (q - k)))]

theorem weighted_outputFiber_le (m : ℕ) (u : FourierVelocity) (g : Wavevector → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hu : ∀ k, fourierMoment (m + 2) u k ≤ g k)
    (q k : Wavevector) (i : Fin 3) :
    (1 + ‖frequencyVec q‖) ^ m * ‖outputFiber q u k i‖ ≤ g k * g (q - k) := by
  have hf : ‖outputFiber q u k i‖ ≤
      ‖frequencyVec q‖ * ‖coefficientVec (u k)‖ * ‖coefficientVec (u (q - k))‖ := by
    rw [outputFiber, norm_mul]
    exact mul_le_mul (norm_modeDot_le q (u k))
      (PiLp.norm_apply_le (coefficientVec (u (q - k))) i) (norm_nonneg _) (by positivity)
  calc
    _ ≤ (1 + ‖frequencyVec q‖) ^ (m + 1) *
        ‖coefficientVec (u k)‖ * ‖coefficientVec (u (q - k))‖ := by
      rw [pow_succ]
      calc
        _ ≤ (1 + ‖frequencyVec q‖) ^ m *
            ((1 + ‖frequencyVec q‖) * ‖coefficientVec (u k)‖ *
              ‖coefficientVec (u (q - k))‖) := by
          gcongr
          exact hf.trans (by gcongr; exact le_add_of_nonneg_left zero_le_one)
        _ = _ := by ring
    _ ≤ ((1 + ‖frequencyVec k‖) * (1 + ‖frequencyVec (q - k)‖)) ^ (m + 1) *
        ‖coefficientVec (u k)‖ * ‖coefficientVec (u (q - k))‖ := by
      gcongr
      exact one_add_norm_output_le q k
    _ = fourierMoment (m + 1) u k * fourierMoment (m + 1) u (q - k) := by
      simp only [fourierMoment, mul_pow]
      ring
    _ ≤ _ := mul_le_mul
      ((fourierMoment_mono u (by omega : m + 1 ≤ m + 2) k).trans (hu k))
      ((fourierMoment_mono u (by omega : m + 1 ≤ m + 2) (q - k)).trans (hu (q - k)))
      (fourierMoment_nonneg _ _ _) (hg k)

theorem weighted_infiniteConvection_component_le (m : ℕ) (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ k, fourierMoment (m + 2) u k ≤ g k) (q : Wavevector) (i : Fin 3) :
    (1 + ‖frequencyVec q‖) ^ m * ‖infiniteConvection u q i‖ ≤ convolutionEnvelope g q := by
  have hs := (summable_pairEnvelope g hg hSum).prod_factor q
  have hu2 (k : Wavevector) := (fourierMoment_mono u (by omega : 2 ≤ m + 2) k).trans (hu k)
  have hn := hs.of_nonneg_of_le (fun k ↦ norm_nonneg (outputFiber q u k i))
    (fun k ↦ norm_outputFiber_le_momentEnvelope u g hg hu2 q k i)
  calc
    _ ≤ (1 + ‖frequencyVec q‖) ^ m * ∑' k, ‖outputFiber q u k i‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (by positivity)
    _ = ∑' k, (1 + ‖frequencyVec q‖) ^ m * ‖outputFiber q u k i‖ := (tsum_mul_left).symm
    _ ≤ _ := (hn.mul_left _).tsum_le_tsum (weighted_outputFiber_le m u g hg hu q · i) hs

theorem fourierMoment_infiniteConvection_le (m : ℕ) (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ k, fourierMoment (m + 2) u k ≤ g k) (q : Wavevector) :
    fourierMoment m (infiniteConvection u) q ≤ 3 * convolutionEnvelope g q := by
  have hw : 0 ≤ (1 + ‖frequencyVec q‖) ^ m := by positivity
  have h := norm_coefficientVec_le_three
    ((((1 + ‖frequencyVec q‖) ^ m : ℝ) : ℂ) • infiniteConvection u q) _
    (convolutionEnvelope_nonneg g hg q) (fun i ↦ by
      simpa only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hw] using weighted_infiniteConvection_component_le m u g hg hSum hu q i)
  change ‖(((1 + ‖frequencyVec q‖) ^ m : ℝ) : ℂ) • coefficientVec (infiniteConvection u q)‖ ≤ _ at h
  simpa only [fourierMoment, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw] using h

theorem fourierMoment_infiniteVelocityRHS_le (m : ℕ) (nu : ℝ) (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ k, fourierMoment (m + 2) u k ≤ g k) (q : Wavevector) :
    fourierMoment m (infiniteVelocityRHS nu u) q ≤ velocityEnvelope nu g q := by
  change (1 + ‖frequencyVec q‖) ^ m *
    ‖coefficientVec (lerayMode q ((-unitTorusDerivativePhase) • infiniteConvection u q)) +
      coefficientVec (unitTorusViscousVorticityCoeff nu u q)‖ ≤ _
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)).trans
  rw [mul_add]
  unfold velocityEnvelope
  apply add_le_add
  · apply (mul_le_mul_of_nonneg_left (norm_lerayMode_le q _) (by positivity)).trans
    change (1 + ‖frequencyVec q‖) ^ m *
      ‖(-unitTorusDerivativePhase) • coefficientVec (infiniteConvection u q)‖ ≤ _
    rw [norm_smul, norm_neg, norm_derivativePhase]
    calc
      _ = (2 * Real.pi) * fourierMoment m (infiniteConvection u) q := by
        unfold fourierMoment
        ring
      _ ≤ (2 * Real.pi) * (3 * convolutionEnvelope g q) :=
        mul_le_mul_of_nonneg_left (fourierMoment_infiniteConvection_le m u g hg hSum hu q) (by positivity)
      _ = _ := by ring
  · rw [norm_viscousCoefficient]
    have hr : (1 + ‖frequencyVec q‖) ^ m * ‖frequencyVec q‖ ^ 2 *
        ‖coefficientVec (u q)‖ ≤ fourierMoment (m + 2) u q := by
      unfold fourierMoment
      rw [pow_add]
      gcongr
      exact le_add_of_nonneg_left zero_le_one
    calc
      _ = (|nu| * (2 * Real.pi) ^ 2) *
          ((1 + ‖frequencyVec q‖) ^ m * ‖frequencyVec q‖ ^ 2 * ‖coefficientVec (u q)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr.trans (hu q)) (by positivity)

theorem summable_fourierMoment_infiniteVelocityRHS (m : ℕ) (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (m + 2) u)) : Summable (fourierMoment m (infiniteVelocityRHS nu u)) :=
  (summable_velocityEnvelope nu (fourierMoment (m + 2) u) (fourierMoment_nonneg _ _) hu
    ).of_nonneg_of_le (fourierMoment_nonneg _ _)
      (fourierMoment_infiniteVelocityRHS_le m nu u _ (fourierMoment_nonneg _ _) hu (fun _ ↦ le_rfl))

end Mettapedia.FluidDynamics.NavierStokes.VelocityRHSMoments
