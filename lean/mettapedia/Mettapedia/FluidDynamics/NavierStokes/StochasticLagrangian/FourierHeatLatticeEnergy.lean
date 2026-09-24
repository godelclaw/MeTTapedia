import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorDecay
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLatticeDecayEnvelope

/-!
# Summable output-frequency cost for the heat commutator

At every positive heat parameter, the Gaussian output factor makes the
quadratic frequency cost summable on the full lattice. The comparison
constant is used only to establish convergence; the resulting budget
retains the exact Gaussian sum.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatLatticeEnergy

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open FourierHeatFlow FourierVorticityPairDynamics PancakeInfinitePressureCoefficients
open PancakeLatticeDecayEnvelope

theorem sq_mul_exp_neg_sq_le_decay {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) :
    r ^ 2 * Real.exp (-(a * r ^ 2)) ≤ (96 / a ^ 3) * (1 / (1 + r) ^ 4) := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have he := Real.pow_div_factorial_le_exp (a * r ^ 2) (by positivity) 3
  norm_num at he
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(a * r ^ 2))).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  have hp : (1 + r) ^ 4 ≤ 16 * r ^ 4 := by
    calc
      _ ≤ (2 * r) ^ 4 := by gcongr; linarith
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ r ^ 2 * Real.exp (-(a * r ^ 2)) by positivity)
  rw [mul_one_div, le_div_iff₀ (by positivity : 0 < (1 + r) ^ 4)]
  apply (le_div_iff₀ (by positivity : 0 < a ^ 3)).mpr
  have hscaled := mul_le_mul_of_nonneg_right hmul (pow_nonneg ha.le 3)
  nlinarith

theorem summable_frequency_sq_mul_multiplier {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ) :
    Summable (fun q : Wavevector ↦ ‖frequencyVec q‖ ^ 2 * multiplier ν σ q) := by
  let a := ν * (2 * Real.pi) ^ 2 * σ
  have ha : 0 < a := by dsimp [a]; positivity
  apply (summable_latticeDecayWeight.mul_left (96 / a ^ 3)).of_norm_bounded_eventually
  filter_upwards [show ∀ᶠ q : Wavevector in Filter.cofinite, q ≠ 0 from
    Filter.eventually_cofinite_ne 0] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sq_nonneg _) (multiplier_pos ν σ q).le)]
  have hm : multiplier ν σ q = Real.exp (-(a * ‖frequencyVec q‖ ^ 2)) := by
    unfold multiplier modeDamping a
    congr 1
    ring
  rw [hm]
  exact sq_mul_exp_neg_sq_le_decay ha (one_le_norm_frequencyVec hq)

/-- The exact lattice cost, without replacing it by a coarser power bound. -/
def outputEnergyCost (ν σ : ℝ) : ℝ :=
  ∑' q : Wavevector, ‖frequencyVec q‖ ^ 2 * multiplier ν σ q

theorem outputEnergyCost_nonneg (ν σ : ℝ) : 0 ≤ outputEnergyCost ν σ :=
  tsum_nonneg (fun q ↦ mul_nonneg (sq_nonneg _) (multiplier_pos ν σ q).le)

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatLatticeEnergy
