import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherSobolevWeights
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSobolevVelocityRate

/-!
# Higher-order energy rate of the actual physical velocity equation

The same Leray cancellation and exact viscous symbol hold with every fixed
polynomial weight. The higher-order convolution estimate has an explicit
order-dependent factor and no cutoff dependence.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeHigherSobolevVelocityRate

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator
open PancakeSignedTransportEnergy PancakeGalerkinKineticEnergy PancakeLowPressureBudget
open PancakeFiniteConvolutionL2 PancakeSobolevWeights PancakeSobolevVelocityRate
open PancakeHigherSobolevWeights PancakeIncomingLowSourceEnergy

def velocityEnergy (m : ℕ) (M : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  orderEnergy m M (amplitude u)
def velocityDissipation (m : ℕ) (M : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  orderDissipation m M (amplitude u)

theorem velocityEnergy_eq (m : ℕ) (M : Finset Wavevector) (u : FourierVelocity) :
    velocityEnergy m M u = ∑ k ∈ M, orderWeight m k ^ 2 * coefficientEnergy (u k) := by
  simp [velocityEnergy, orderEnergy, amplitude, mul_pow, norm_coefficientVec_sq]

theorem velocityDissipation_eq (m : ℕ) (M : Finset Wavevector) (u : FourierVelocity) :
    velocityDissipation m M u = ∑ k ∈ M,
      orderWeight m k ^ 2 * ‖frequencyVec k‖ ^ 2 * coefficientEnergy (u k) := by
  simp [velocityDissipation, orderDissipation, orderEnergy, amplitude, mul_pow,
    norm_coefficientVec_sq, mul_assoc]

def orderConvectionRate (m : ℕ) (M : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ M, orderWeight m q ^ 2 *
    (coefficientHermitian (u q) ((-unitTorusDerivativePhase) • convectionConvolution M u q)).re

def orderVelocityRate (m : ℕ) (M : Finset Wavevector) (u du : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ M, orderWeight m q ^ 2 * (coefficientHermitian (u q) (du q)).re

theorem orderVelocityRate_velocityRHS (m : ℕ) (M : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (hd : ∀ k ∈ M, modeDot k (u k) = 0) :
    orderVelocityRate m M u (velocityRHS M u nu) =
      orderConvectionRate m M u - 2 * nu * (2 * Real.pi)^2 * velocityDissipation m M u := by
  have he (q : Wavevector) (hq : q ∈ M) :
      (coefficientHermitian (u q) (velocityRHS M u nu q)).re =
      (coefficientHermitian (u q) ((-unitTorusDerivativePhase) • convectionConvolution M u q)).re -
      nu * (2 * Real.pi)^2 * ‖frequencyVec q‖^2 * coefficientEnergy (u q) := by
    rw [velocityRHS, hermitian_add_right, Complex.add_re,
      hermitian_leray_right q (u q) _ (hd q hq),
      finiteTransport_fourierCurl_eq M u hk hd, viscous_energy_pair, ← norm_frequencyVec_sq]
    ring
  rw [orderVelocityRate, orderConvectionRate, velocityDissipation_eq]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [he q hq]
  ring

theorem orderConvectionRate_le (m : ℕ) (M : Finset Wavevector) (u : FourierVelocity) :
    orderConvectionRate m M u ≤ 2 * (2 * Real.pi) * orderTriad m M (amplitude u) := by
  have he : orderConvectionRate m M u =
      2 * ∑ q ∈ M, ∑ k ∈ M, ∑ l ∈ M, if k+l = q then
        orderWeight m q ^ 2 * (coefficientHermitian (u q)
          ((-unitTorusDerivativePhase) • orderedConvection k l u)).re else 0 := by
    simp only [orderConvectionRate, convectionConvolution, Finset.smul_sum,
      hermitian_sum_right, Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    split_ifs <;> simp [coefficientHermitian]
  rw [he]
  calc
    _ ≤ 2 * ∑ q ∈ M, ∑ k ∈ M, ∑ l ∈ M, if k+l = q then
        orderWeight m q ^ 2 * ((2 * Real.pi) * amplitude u q * amplitude u k *
          (‖frequencyVec l‖ * amplitude u l)) else 0 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      split_ifs
      · exact mul_le_mul_of_nonneg_left (convection_pair_le u q k l) (sq_nonneg _)
      · exact le_rfl
    _ = _ := by
      rw [collect_output_sum]
      simp only [orderTriad, cut, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      split_ifs <;> ring

theorem orderVelocityRate_le (m : ℕ) (hm : 2 ≤ m) (M : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (hd : ∀ k ∈ M, modeDot k (u k) = 0) :
    orderVelocityRate m M u (velocityRHS M u nu) +
        2 * nu * (2 * Real.pi)^2 * velocityDissipation m M u ≤
      4 * (2 : ℝ)^m * (2 * Real.pi) * Real.sqrt latticeMass *
        velocityEnergy m M u * Real.sqrt (velocityDissipation m M u) := by
  rw [orderVelocityRate_velocityRHS m M u nu hk hd]
  have h1 := orderConvectionRate_le m M u
  have h2 := mul_le_mul_of_nonneg_left
    (orderTriad_le m hm M (amplitude u) (fun k ↦ norm_nonneg _))
    (show 0 ≤ 2 * (2 * Real.pi) by positivity)
  change 2 * (2 * Real.pi) * orderTriad m M (amplitude u) ≤
    2 * (2 * Real.pi) * (2 * (2 : ℝ)^m * Real.sqrt latticeMass *
      velocityEnergy m M u * Real.sqrt (velocityDissipation m M u)) at h2
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeHigherSobolevVelocityRate
