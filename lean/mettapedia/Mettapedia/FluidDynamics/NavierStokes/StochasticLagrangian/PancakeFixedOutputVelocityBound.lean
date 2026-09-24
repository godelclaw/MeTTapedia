import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLowPressureBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCommonGalerkinWindow

/-!
# Fixed-output velocity estimates from kinetic energy

Incompressibility moves the convection derivative onto the output
frequency. The convolution fiber is bounded by kinetic energy without a
retained-mode count. All norms are Euclidean coefficient norms.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFixedOutputVelocityBound

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open PancakeFrequencyProjectorCommutator PancakeLowPressureBudget
open PancakeViscousMisalignmentAbsorption PancakeIncomingLowSourceEnergy
open PancakeFourierPressureStrain

theorem coefficientVec_sum {ι : Type*} (s : Finset ι) (f : ι → VelocityCoefficient) :
    coefficientVec (∑ i ∈ s, f i) = ∑ i ∈ s, coefficientVec (f i) := by
  ext j
  simp [coefficientVec]

theorem norm_lerayMode_le (q : Wavevector) (v : VelocityCoefficient) :
    ‖coefficientVec (lerayMode q v)‖ ≤ ‖coefficientVec v‖ := by
  by_cases hq : modeSquare q = 0
  · simp [lerayMode, hq]
  have ht := modeDot_lerayMode_eq_zero q v hq
  have he := congrArg Complex.re (hermitian_leray_right q (lerayMode q v) v ht)
  have hh := abs_hermitian_re_le (lerayMode q v) v
  have hi : (coefficientHermitian (lerayMode q v) (lerayMode q v)).re =
      coefficientEnergy (lerayMode q v) := by
    simp [coefficientHermitian, coefficientEnergy, Complex.normSq_apply]
  rw [← he, hi, ← norm_coefficientVec_sq,
    abs_of_nonneg (sq_nonneg _)] at hh
  nlinarith [norm_nonneg (coefficientVec (lerayMode q v)), norm_nonneg (coefficientVec v)]

theorem norm_convectionConvolution_le (M : Finset Wavevector) (u : FourierVelocity)
    (hd : ∀ k ∈ M, modeDot k (u k) = 0) (q : Wavevector) :
    ‖coefficientVec (convectionConvolution M u q)‖ ≤
      ‖frequencyVec q‖ * fullEnergy M u := by
  rw [convectionConvolution_eq_pairSum, coefficientVec_sum]
  calc
    _ ≤ ∑ p ∈ interactionPairs M q, ‖coefficientVec (orderedConvection p.1 p.2 u)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ interactionPairs M q,
        ‖frequencyVec q‖ * (‖coefficientVec (u p.1)‖ * ‖coefficientVec (u p.2)‖) := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := Finset.mem_filter.mp hp
      have hk := (Finset.mem_product.mp hm.1).1
      have he : modeDot p.2 (u p.1) = modeDot q (u p.1) := by
        rw [← hm.2, modeDot_add_wavevector, hd p.1 hk, zero_add]
      change ‖modeDot p.2 (u p.1) • coefficientVec (u p.2)‖ ≤ _
      rw [norm_smul, he]
      calc
        _ ≤ (‖frequencyVec q‖ * ‖coefficientVec (u p.1)‖) * ‖coefficientVec (u p.2)‖ :=
          mul_le_mul_of_nonneg_right (norm_modeDot_le q _) (norm_nonneg _)
        _ = _ := by ring
    _ = ‖frequencyVec q‖ * ∑ p ∈ interactionPairs M q,
        ‖coefficientVec (u p.1)‖ * ‖coefficientVec (u p.2)‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_pair_norm_product_le_energy M u q) (norm_nonneg _)

theorem norm_viscousCoefficient (nu : ℝ) (u : FourierVelocity) (q : Wavevector) :
    ‖coefficientVec (unitTorusViscousVorticityCoeff nu u q)‖ =
      |nu| * (2 * Real.pi)^2 * ‖frequencyVec q‖^2 * ‖coefficientVec (u q)‖ := by
  change ‖((nu : ℂ) * unitTorusDerivativePhase^2 * modeSquare q) • coefficientVec (u q)‖ = _
  rw [norm_smul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_pow, norm_derivativePhase, norm_modeSquare]

theorem norm_velocityRHS_le (M : Finset Wavevector) (u : FourierVelocity)
    (nu : ℝ) (hk : ∀ k ∈ M, frequencyVec k ≠ 0)
    (hd : ∀ k ∈ M, modeDot k (u k) = 0) (q : Wavevector) :
    ‖coefficientVec (velocityRHS M u nu q)‖ ≤
      (2 * Real.pi) * ‖frequencyVec q‖ * fullEnergy M u +
      |nu| * (2 * Real.pi)^2 * ‖frequencyVec q‖^2 * ‖coefficientVec (u q)‖ := by
  rw [velocityRHS, finiteTransport_fourierCurl_eq M u hk hd]
  change ‖coefficientVec (lerayMode q ((-unitTorusDerivativePhase) • convectionConvolution M u q)) +
    coefficientVec (unitTorusViscousVorticityCoeff nu u q)‖ ≤ _
  apply (norm_add_le _ _).trans
  rw [norm_viscousCoefficient]
  apply add_le_add _ le_rfl
  apply (norm_lerayMode_le q _).trans
  change ‖(-unitTorusDerivativePhase) • coefficientVec (convectionConvolution M u q)‖ ≤ _
  rw [norm_smul, norm_neg, norm_derivativePhase]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (norm_convectionConvolution_le M u hd q) (by positivity : 0 ≤ 2 * Real.pi)

end Mettapedia.FluidDynamics.NavierStokes.PancakeFixedOutputVelocityBound
