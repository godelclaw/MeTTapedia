import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSobolevWeights
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalVelocityEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLowPressureBudget

/-!
# Second-order energy of the physical retained velocity equation

The Fourier Leray projection does no work against the transverse velocity
coefficient. A finite convolution estimate bounds the remaining convection
without a cutoff factor. The viscous derivative cost is retained exactly.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevVelocityRate

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator
open PancakeSignedTransportEnergy PancakeGalerkinKineticEnergy PancakeLowPressureBudget
open PancakeFiniteConvolutionL2 PancakeSobolevWeights
open PancakeIncomingLowSourceEnergy

def amplitude (u : FourierVelocity) (k : Wavevector) : ℝ := ‖coefficientVec (u k)‖
def sobolevEnergy (M : Finset Wavevector) (u : FourierVelocity) : ℝ := energy M (amplitude u)
def sobolevDissipation (M : Finset Wavevector) (u : FourierVelocity) : ℝ := dissipation M (amplitude u)

theorem sobolevEnergy_eq (M : Finset Wavevector) (u : FourierVelocity) :
    sobolevEnergy M u = ∑ k ∈ M, weight k ^ 2 * coefficientEnergy (u k) := by
  simp [sobolevEnergy, energy, amplitude, mul_pow, norm_coefficientVec_sq]

theorem sobolevDissipation_eq (M : Finset Wavevector) (u : FourierVelocity) :
    sobolevDissipation M u = ∑ k ∈ M,
      weight k ^ 2 * ‖frequencyVec k‖ ^ 2 * coefficientEnergy (u k) := by
  simp [sobolevDissipation, dissipation, energy, amplitude, mul_pow, norm_coefficientVec_sq,
    mul_assoc]

def convectionRate (M : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ M, weight q ^ 2 *
    (coefficientHermitian (u q) ((-unitTorusDerivativePhase) • convectionConvolution M u q)).re

def energyRate (M : Finset Wavevector) (u du : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ M, weight q ^ 2 * (coefficientHermitian (u q) (du q)).re

theorem energyRate_velocityRHS (M : Finset Wavevector) (u : FourierVelocity) (nu : ℝ)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (hd : ∀ k ∈ M, modeDot k (u k) = 0) :
    energyRate M u (velocityRHS M u nu) =
      convectionRate M u - 2 * nu * (2 * Real.pi)^2 * sobolevDissipation M u := by
  have he (q : Wavevector) (hq : q ∈ M) :
      (coefficientHermitian (u q) (velocityRHS M u nu q)).re =
      (coefficientHermitian (u q) ((-unitTorusDerivativePhase) • convectionConvolution M u q)).re -
      nu * (2 * Real.pi)^2 * ‖frequencyVec q‖^2 * coefficientEnergy (u q) := by
    rw [velocityRHS, hermitian_add_right, Complex.add_re,
      hermitian_leray_right q (u q) _ (hd q hq),
      finiteTransport_fourierCurl_eq M u hk hd, viscous_energy_pair, ← norm_frequencyVec_sq]
    ring
  rw [energyRate, convectionRate, sobolevDissipation_eq]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [he q hq]
  ring

theorem convection_pair_le (u : FourierVelocity) (q k l : Wavevector) :
    (coefficientHermitian (u q) ((-unitTorusDerivativePhase) • orderedConvection k l u)).re ≤
      (2 * Real.pi) * amplitude u q * amplitude u k * (‖frequencyVec l‖ * amplitude u l) := by
  apply (le_abs_self _).trans
  apply (abs_hermitian_re_le _ _).trans
  change amplitude u q * ‖(-unitTorusDerivativePhase) •
    (modeDot l (u k) • coefficientVec (u l))‖ ≤ _
  rw [norm_smul, norm_neg, norm_derivativePhase, norm_smul]
  have h := norm_modeDot_le l (u k)
  change ‖modeDot l (u k)‖ ≤ ‖frequencyVec l‖ * amplitude u k at h
  calc
    _ ≤ amplitude u q * ((2 * Real.pi) *
        ((‖frequencyVec l‖ * amplitude u k) * amplitude u l)) := by
      dsimp [amplitude] at h ⊢
      gcongr
    _ = _ := by ring

theorem collect_output_sum (M : Finset Wavevector) (F : Wavevector → Wavevector → Wavevector → ℝ) :
    (∑ q ∈ M, ∑ k ∈ M, ∑ l ∈ M, if k + l = q then F q k l else 0) =
      ∑ k ∈ M, ∑ l ∈ M, if k + l ∈ M then F (k+l) k l else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp

theorem convectionRate_le (M : Finset Wavevector) (u : FourierVelocity) :
    convectionRate M u ≤
      2 * (2 * Real.pi) * weightedTriad M (amplitude u) := by
  have he : convectionRate M u =
      2 * ∑ q ∈ M, ∑ k ∈ M, ∑ l ∈ M, if k + l = q then
        weight q ^ 2 * (coefficientHermitian (u q)
          ((-unitTorusDerivativePhase) • orderedConvection k l u)).re else 0 := by
    simp only [convectionRate, convectionConvolution, Finset.smul_sum,
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
    _ ≤ 2 * ∑ q ∈ M, ∑ k ∈ M, ∑ l ∈ M, if k + l = q then
        weight q ^ 2 * ((2 * Real.pi) * amplitude u q * amplitude u k *
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
      simp only [weightedTriad, cut, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      split_ifs <;> ring

theorem energyRate_le (M : Finset Wavevector) (u : FourierVelocity) (nu : ℝ)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (hd : ∀ k ∈ M, modeDot k (u k) = 0) :
    energyRate M u (velocityRHS M u nu) + 2 * nu * (2 * Real.pi)^2 * sobolevDissipation M u ≤
      8 * (2 * Real.pi) * Real.sqrt latticeMass * sobolevEnergy M u * Real.sqrt (sobolevDissipation M u) := by
  rw [energyRate_velocityRHS M u nu hk hd]
  have h1 := convectionRate_le M u
  have h2 := mul_le_mul_of_nonneg_left
    (weightedTriad_le M (amplitude u) (fun k ↦ norm_nonneg _))
    (show 0 ≤ 2 * (2 * Real.pi) by positivity)
  change 2 * (2 * Real.pi) * weightedTriad M (amplitude u) ≤
    2 * (2 * Real.pi) * (4 * Real.sqrt latticeMass * sobolevEnergy M u *
      Real.sqrt (sobolevDissipation M u)) at h2
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevVelocityRate
