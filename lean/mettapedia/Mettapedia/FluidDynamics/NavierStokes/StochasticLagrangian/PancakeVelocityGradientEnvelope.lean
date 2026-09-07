import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherDerivativeMoments

/-!
# A common envelope for the differentiated velocity RHS

The output derivative of convection is paid by two input moments, while
the differentiated viscous term is paid by the third input moment.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeVelocityGradientEnvelope

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeIndexedFourierMoments PancakeHigherDerivativeMoments
open PancakeInfiniteVelocityEnvelope PancakeInfinitePressureHessian PancakeCoefficientLimitEquation
open PancakeFixedOutputVelocityBound PancakePeriodicVorticityEquation PancakeInfiniteFourierDerivative
open PancakeIncomingLowSourceEnergy

theorem norm_frequency_mul_velocityRHS_le (nu : ℝ) (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ k, fourierMoment 3 u k ≤ g k) (q : Wavevector) :
    ‖frequencyVec q‖ * ‖coefficientVec (infiniteVelocityRHS nu u q)‖ ≤ velocityEnvelope nu g q := by
  have hu2 (k : Wavevector) : fourierMoment 2 u k ≤ g k :=
    (fourierMoment_mono u (by omega : 2 ≤ 3) k).trans (hu k)
  change ‖frequencyVec q‖ *
    ‖coefficientVec (lerayMode q ((-unitTorusDerivativePhase) • infiniteConvection u q)) +
      coefficientVec (unitTorusViscousVorticityCoeff nu u q)‖ ≤ _
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)).trans
  rw [mul_add]
  unfold velocityEnvelope
  apply add_le_add
  · apply (mul_le_mul_of_nonneg_left (norm_lerayMode_le q _) (norm_nonneg _)).trans
    change ‖frequencyVec q‖ * ‖(-unitTorusDerivativePhase) • coefficientVec (infiniteConvection u q)‖ ≤ _
    rw [norm_smul, norm_neg, norm_derivativePhase]
    calc
      _ = (2 * Real.pi) * (‖frequencyVec q‖ * ‖coefficientVec (infiniteConvection u q)‖) := by ring
      _ ≤ (2 * Real.pi) * (3 * convolutionEnvelope g q) :=
        mul_le_mul_of_nonneg_left
          (norm_frequency_mul_infiniteConvection_le u g hg hSum hu2 q) (by positivity)
      _ = _ := by ring
  · rw [norm_viscousCoefficient]
    have hr : ‖frequencyVec q‖^3 * ‖coefficientVec (u q)‖ ≤ fourierMoment 3 u q := by
      unfold fourierMoment
      gcongr
      exact le_add_of_nonneg_left zero_le_one
    calc
      _ = (|nu| * (2 * Real.pi)^2) * (‖frequencyVec q‖^3 * ‖coefficientVec (u q)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr.trans (hu q)) (by positivity)

theorem norm_velocityRHS_derivative_le (nu : ℝ) (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ k, fourierMoment 3 u k ≤ g k) (j : Fin 3) (q : Wavevector) :
    ‖indexedDerivativeCoeff id j (infiniteVelocityRHS nu u) q‖ ≤
      (2 * Real.pi) * velocityEnvelope nu g q := by
  apply (norm_coefficient_sup_le_euclidean _).trans
  change ‖(unitTorusDerivativePhase * (q j : ℂ)) •
    coefficientVec (infiniteVelocityRHS nu u q)‖ ≤ _
  rw [norm_smul, norm_mul, norm_derivativePhase]
  calc
    _ ≤ (2 * Real.pi) * ‖frequencyVec q‖ * ‖coefficientVec (infiniteVelocityRHS nu u q)‖ := by
      gcongr
      exact norm_frequency_coordinate_le q j
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (norm_frequency_mul_velocityRHS_le nu u g hg hSum hu q)
        (by positivity)

theorem firstMoment_velocityRHS_le (nu : ℝ) (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ k, fourierMoment 3 u k ≤ g k) (q : Wavevector) :
    fourierMoment 1 (infiniteVelocityRHS nu u) q ≤ 2 * velocityEnvelope nu g q := by
  have h0 := norm_infiniteVelocityRHS_le nu u g hg hSum
    (fun k ↦ (fourierMoment_mono u (by omega : 2 ≤ 3) k).trans (hu k)) q
  have h1 := norm_frequency_mul_velocityRHS_le nu u g hg hSum hu q
  simp only [fourierMoment, pow_one]
  nlinarith

theorem summable_firstMoment_velocityRHS (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    Summable (fourierMoment 1 (infiniteVelocityRHS nu u)) :=
  ((summable_velocityEnvelope nu (fourierMoment 3 u) (fourierMoment_nonneg _ _) hu).mul_left 2).of_nonneg_of_le (fourierMoment_nonneg _ _)
      (firstMoment_velocityRHS_le nu u _ (fourierMoment_nonneg _ _) hu (fun _ ↦ le_rfl))

end Mettapedia.FluidDynamics.NavierStokes.PancakeVelocityGradientEnvelope
