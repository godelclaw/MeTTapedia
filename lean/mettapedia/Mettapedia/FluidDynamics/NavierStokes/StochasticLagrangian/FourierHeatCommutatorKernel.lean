import Mettapedia.Analysis.ODE.ExponentialDuhamel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatFlow

/-!
# Signed Duhamel kernel of the actual heat commutator

The multiplier defect factors into a signed input-frequency contraction
and a nonnegative time kernel. No division by a rate difference is used.
The factorization is inserted into the actual infinite nonlinear force,
with the Leray pressure correction unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorKernel

open Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail
open FourierVorticityPairDynamics FourierHeatFlow PancakeSobolevFiberEnvelope
open PancakePeriodicVorticityEquation

def rateDefect (ν : ℝ) (k l : Wavevector) : ℝ :=
  pairDamping ν k l - modeDamping ν (k + l)

def timeKernel (ν : ℝ) (k l : Wavevector) (σ r : ℝ) : ℝ :=
  ExponentialDuhamel.kernel (modeDamping ν (k + l)) (pairDamping ν k l) σ r

theorem multiplier_pair (ν σ : ℝ) (k l : Wavevector) :
    multiplier ν σ k * multiplier ν σ l = Real.exp (-pairDamping ν k l * σ) := by
  unfold multiplier pairDamping
  rw [← Real.exp_add]
  congr 1
  ring

theorem rateDefect_eq_frequency_contraction (ν : ℝ) (k l : Wavevector) :
    rateDefect ν k l =
      -2 * ν * (2 * Real.pi) ^ 2 * ∑ j : Fin 3, (k j : ℝ) * (l j : ℝ) := by
  simp only [rateDefect, pairDamping, modeDamping, norm_frequencyVec_sq,
    Fin.sum_univ_three, Pi.add_apply, Int.cast_add]
  ring

theorem multiplier_sub_eq_rateDefect_integral (ν σ : ℝ) (k l : Wavevector) :
    multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l =
      rateDefect ν k l * ∫ r in (0 : ℝ)..σ, timeKernel ν k l σ r := by
  rw [multiplier_pair]
  exact ExponentialDuhamel.exp_sub_eq_rate_mul_integral _ _ _

theorem integral_timeKernel_nonneg (ν : ℝ) (k l : Wavevector) {σ : ℝ} (hσ : 0 ≤ σ) :
    0 ≤ ∫ r in (0 : ℝ)..σ, timeKernel ν k l σ r :=
  ExponentialDuhamel.integral_kernel_nonneg _ _ hσ

theorem abs_multiplier_sub_le (ν : ℝ) (k l : Wavevector) {σ : ℝ} (hσ : 0 ≤ σ) :
    |multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l| ≤
      |rateDefect ν k l| * σ *
        Real.exp (-min (modeDamping ν (k + l)) (pairDamping ν k l) * σ) := by
  rw [multiplier_pair]
  exact ExponentialDuhamel.abs_exp_sub_le _ _ hσ

theorem multiplier_sub_nonpos_of_contraction_nonneg {ν σ : ℝ}
    (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (k l : Wavevector)
    (hkl : 0 ≤ ∑ j : Fin 3, (k j : ℝ) * (l j : ℝ)) :
    multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l ≤ 0 := by
  rw [multiplier_sub_eq_rateDefect_integral]
  apply mul_nonpos_of_nonpos_of_nonneg _ (integral_timeKernel_nonneg ν k l hσ)
  rw [rateDefect_eq_frequency_contraction]
  have h : 0 ≤ 2 * ν * (2 * Real.pi) ^ 2 * ∑ j : Fin 3, (k j : ℝ) * (l j : ℝ) := by positivity
  nlinarith

theorem multiplier_sub_nonneg_of_contraction_nonpos {ν σ : ℝ}
    (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (k l : Wavevector)
    (hkl : (∑ j : Fin 3, (k j : ℝ) * (l j : ℝ)) ≤ 0) :
    0 ≤ multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l := by
  rw [multiplier_sub_eq_rateDefect_integral]
  apply mul_nonneg _ (integral_timeKernel_nonneg ν k l hσ)
  rw [rateDefect_eq_frequency_contraction]
  have h : 2 * ν * (2 * Real.pi) ^ 2 * (∑ j : Fin 3, (k j : ℝ) * (l j : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hkl
  nlinarith

theorem multiplier_sub_eq_zero_of_contraction_eq_zero (ν σ : ℝ) (k l : Wavevector)
    (hkl : (∑ j : Fin 3, (k j : ℝ) * (l j : ℝ)) = 0) :
    multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l = 0 := by
  rw [multiplier_sub_eq_rateDefect_integral, rateDefect_eq_frequency_contraction, hkl, mul_zero, zero_mul]

/-- The all-input convection discrepancy with the signed kernel exposed. -/
def duhamelConvection (ν σ : ℝ) (u : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  fun i ↦ ∑' k : Wavevector,
    ((rateDefect ν k (q - k) *
      ∫ r in (0 : ℝ)..σ, timeKernel ν k (q - k) σ r : ℝ) : ℂ) * outputFiber q u k i

theorem subgridConvection_eq_duhamel (ν σ : ℝ) (u : FourierVelocity) :
    InfiniteFilteredEquation.subgridConvection (fun k ↦ (multiplier ν σ k : ℂ)) u =
      duhamelConvection ν σ u := by
  funext q i
  apply tsum_congr
  intro k
  have h := multiplier_sub_eq_rateDefect_integral ν σ k (q - k)
  rw [add_sub_cancel] at h
  have hc := congrArg (fun x : ℝ ↦ (x : ℂ)) h
  push_cast at hc
  simpa only [Complex.ofReal_mul] using congrArg (fun z : ℂ ↦ z * outputFiber q u k i) hc

/-- The same kernel appears in the actual nonlinear rate, including pressure. -/
theorem nonlinearCommutator_eq_duhamel {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (q : Wavevector) :
    nonlinearCommutator ν σ u q =
      lerayMode q ((-unitTorusDerivativePhase) • duhamelConvection ν σ u q) := by
  rw [nonlinearCommutator_eq_subgridForce hν hσ u hu]
  simp only [InfiniteFilteredEquation.subgridForce, subgridConvection_eq_duhamel]

/-- Exact integrated kernel after pairing with the remaining positive damping rate. -/
theorem integral_weighted_multiplier_defect {ν c : ℝ} (hν : 0 ≤ ν) (hc : 0 < c)
    (k l : Wavevector) :
    (∫ σ : ℝ in Set.Ioi 0, Real.exp (-c * σ) *
      (multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l)) =
      rateDefect ν k l / ((c + modeDamping ν (k + l)) * (c + pairDamping ν k l)) := by
  simp_rw [multiplier_pair]
  have hd : 0 ≤ modeDamping ν (k + l) := by unfold modeDamping; positivity
  have hs : 0 ≤ pairDamping ν k l := by unfold pairDamping modeDamping; positivity
  exact ExponentialDuhamel.integral_weighted_exp_sub _ _ _ (by linarith) (by linarith)

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorKernel
