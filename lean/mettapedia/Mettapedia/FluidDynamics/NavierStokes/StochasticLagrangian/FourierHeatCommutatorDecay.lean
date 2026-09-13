import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorEnergy

/-!
# Retained output heat decay in the commutator energy bound

The two input damping rates dominate half the output damping rate.
Both complementary commutator bounds therefore retain the same half-heat
factor. Their product retains the full output heat multiplier.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorDecay

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail PancakeGalerkinKineticEnergy
open PancakeSignedTransportEnergy PancakeFixedOutputVelocityBound PancakePeriodicVorticityEquation
open PancakeIncomingLowSourceEnergy
open InfiniteConvectionEnergy InfiniteFilteredEquation FourierHeatFlow FourierHeatCommutatorKernel
open FourierHeatCommutatorEnergy FourierVorticityPairDynamics

theorem half_output_damping_le_pair {ν : ℝ} (hν : 0 ≤ ν) (k l : Wavevector) :
    modeDamping ν (k + l) / 2 ≤ pairDamping ν k l := by
  have hn : ‖frequencyVec (k + l)‖ ^ 2 ≤ 2 * (‖frequencyVec k‖ ^ 2 + ‖frequencyVec l‖ ^ 2) := by
    rw [frequencyVec_add]
    have h := norm_add_le (frequencyVec k) (frequencyVec l)
    have hp := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖frequencyVec k‖ - ‖frequencyVec l‖)]
  have h := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ ν * (2 * Real.pi) ^ 2)
  unfold pairDamping modeDamping
  nlinarith

theorem abs_multiplier_defect_le_half_output {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (k l : Wavevector) :
    |multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l| ≤
      multiplier ν (σ / 2) (k + l) := by
  have hd : 0 ≤ modeDamping ν (k + l) := by unfold modeDamping; positivity
  have hq : multiplier ν σ (k + l) ≤ multiplier ν (σ / 2) (k + l) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hp : multiplier ν σ k * multiplier ν σ l ≤ multiplier ν (σ / 2) (k + l) := by
    rw [multiplier_pair]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (half_output_damping_le_pair hν k l) hσ]
  have hq0 := (multiplier_pos ν σ (k + l)).le
  have hp0 := mul_nonneg (multiplier_pos ν σ k).le (multiplier_pos ν σ l).le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_multiplier_defect_le_weighted_half_output {ν σ : ℝ}
    (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (k l : Wavevector) :
    |multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l| ≤
      ((2 * ν * σ) * multiplier ν (σ / 2) (k + l)) *
        (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ * ‖frequencyVec l‖ := by
  have hd : 0 ≤ modeDamping ν (k + l) := by unfold modeDamping; positivity
  have hm : modeDamping ν (k + l) / 2 ≤
      min (modeDamping ν (k + l)) (pairDamping ν k l) :=
    le_min (by linarith) (half_output_damping_le_pair hν k l)
  have he : Real.exp (-min (modeDamping ν (k + l)) (pairDamping ν k l) * σ) ≤
      multiplier ν (σ / 2) (k + l) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hm hσ]
  calc
    _ ≤ |rateDefect ν k l| * σ * multiplier ν (σ / 2) (k + l) :=
      (abs_multiplier_sub_le ν k l hσ).trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ ≤ (2 * ν * (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ * ‖frequencyVec l‖) * σ *
        multiplier ν (σ / 2) (k + l) := by
      apply mul_le_mul_of_nonneg_right _ (multiplier_pos _ _ _).le
      exact mul_le_mul_of_nonneg_right (abs_rateDefect_le hν k l) hσ
    _ = _ := by ring

theorem multiplier_half_sq (ν σ : ℝ) (q : Wavevector) :
    multiplier ν (σ / 2) q ^ 2 = multiplier ν σ q := by
  rw [pow_two, multiplier, ← Real.exp_add]
  unfold multiplier
  congr 1
  ring

theorem norm_heat_subgridForce_le_energy_decay {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2)) (q : Wavevector) :
    ‖coefficientVec (subgridForce (fun k ↦ (multiplier ν σ k : ℂ)) u q)‖ ≤
      (2 * Real.pi) * ‖frequencyVec q‖ * multiplier ν (σ / 2) q * kineticEnergy u := by
  have hm (k : Wavevector) :
      ‖(multiplier ν σ q : ℂ) - (multiplier ν σ k : ℂ) * (multiplier ν σ (q-k) : ℂ)‖ ≤
        multiplier ν (σ / 2) q := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [add_sub_cancel] using abs_multiplier_defect_le_half_output hν hσ k (q-k)
  have hb := norm_weightedConvection_le _ u (multiplier ν (σ / 2) q) hm hu q
  change ‖coefficientVec (subgridConvection (fun k ↦ (multiplier ν σ k : ℂ)) u q)‖ ≤
    multiplier ν (σ / 2) q * ‖frequencyVec q‖ * kineticEnergy u at hb
  change ‖coefficientVec (lerayMode q _)‖ ≤ _
  apply (norm_lerayMode_le q _).trans
  change ‖(-unitTorusDerivativePhase) • coefficientVec (subgridConvection _ u q)‖ ≤ _
  rw [norm_smul, norm_neg, norm_derivativePhase]
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * Real.pi)).trans_eq (by ring)

theorem norm_heat_subgridForce_le_enstrophy_decay {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hd : ∀ k, modeDot k (u k) = 0)
    (hu : Summable (fun k ↦ ‖coefficientVec (fourierCurl u k)‖ ^ 2)) (q : Wavevector) :
    ‖coefficientVec (subgridForce (fun k ↦ (multiplier ν σ k : ℂ)) u q)‖ ≤
      (2 * Real.pi) * ‖frequencyVec q‖ * ((2 * ν * σ) * multiplier ν (σ / 2) q) *
        kineticEnergy (fourierCurl u) := by
  have hm (k : Wavevector) :
      ‖(multiplier ν σ q : ℂ) - (multiplier ν σ k : ℂ) * (multiplier ν σ (q-k) : ℂ)‖ ≤
        ((2 * ν * σ) * multiplier ν (σ / 2) q) *
          (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ * ‖frequencyVec (q-k)‖ := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [add_sub_cancel] using abs_multiplier_defect_le_weighted_half_output hν hσ k (q-k)
  have hb := norm_weightedConvection_le_enstrophy _ u
    ((2 * ν * σ) * multiplier ν (σ / 2) q) q hm
      (mul_nonneg (by positivity) (multiplier_pos ν (σ / 2) q).le) hd hu
  change ‖coefficientVec (subgridConvection (fun k ↦ (multiplier ν σ k : ℂ)) u q)‖ ≤
    ((2 * ν * σ) * multiplier ν (σ / 2) q) * ‖frequencyVec q‖ * kineticEnergy (fourierCurl u) at hb
  change ‖coefficientVec (lerayMode q _)‖ ≤ _
  apply (norm_lerayMode_le q _).trans
  change ‖(-unitTorusDerivativePhase) • coefficientVec (subgridConvection _ u q)‖ ≤ _
  rw [norm_smul, norm_neg, norm_derivativePhase]
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * Real.pi)).trans_eq (by ring)

theorem norm_nonlinearCommutator_sq_le_decay {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ k, modeDot k (u k) = 0) (q : Wavevector) :
    ‖coefficientVec (nonlinearCommutator ν σ u q)‖ ^ 2 ≤
      (2 * ν * σ) * ((2 * Real.pi) * ‖frequencyVec q‖) ^ 2 * multiplier ν σ q *
        (kineticEnergy u * kineticEnergy (fourierCurl u)) := by
  have he : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2) := by
    simpa only [norm_coefficientVec_sq] using InfiniteKineticCancellation.summable_coefficientEnergy u
      (InfiniteKineticCancellation.summable_amplitude u (summable_firstMoment_of_second u hu))
  have hw : Summable (fun k ↦ ‖coefficientVec (fourierCurl u k)‖ ^ 2) := by
    simpa only [norm_coefficientVec_sq] using InfiniteKineticCancellation.summable_curlEnergy u hu
  rw [nonlinearCommutator_eq_subgridForce hν hσ u hu, pow_two]
  have h₁ := norm_heat_subgridForce_le_energy_decay hν hσ u he q
  have h₂ := norm_heat_subgridForce_le_enstrophy_decay hν hσ u hd hw q
  have h := mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)
  apply h.trans_eq
  rw [← multiplier_half_sq ν σ q]
  ring

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorDecay
