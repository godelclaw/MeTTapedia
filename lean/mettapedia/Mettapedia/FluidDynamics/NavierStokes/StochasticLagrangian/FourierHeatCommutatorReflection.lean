import Mettapedia.Analysis.BalancedResolvent
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorEnergy

/-!
# Reflected low-input cancellation in the integrated heat kernel

The actual heat multiplier defect has a reflected resolvent identity.
Its symmetric test channel is quadratic in the input-frequency contraction;
the unequal-test channel remains linear. No equality of the actual tests,
reflection pairing of all interactions, or dynamic budget is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorReflection

open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open FourierVorticityPairDynamics FourierHeatFlow FourierHeatCommutatorKernel
open FourierHeatCommutatorEnergy

def centerRate (ν c : ℝ) (k l : Wavevector) : ℝ := c + pairDamping ν k l

def outputShift (ν : ℝ) (k l : Wavevector) : ℝ := -rateDefect ν k l

def integratedKernel (ν c : ℝ) (k l : Wavevector) : ℝ :=
  ∫ σ : ℝ in Set.Ioi 0, Real.exp (-c * σ) *
    (multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l)

theorem pairDamping_neg_left (ν : ℝ) (k l : Wavevector) :
    pairDamping ν (-k) l = pairDamping ν k l := by
  simp [pairDamping, modeDamping, norm_frequencyVec_sq, Pi.neg_apply]

theorem outputShift_neg_left (ν : ℝ) (k l : Wavevector) :
    outputShift ν (-k) l = -outputShift ν k l := by
  simp only [outputShift, rateDefect_eq_frequency_contraction, Pi.neg_apply, Int.cast_neg,
    neg_mul, Finset.sum_neg_distrib, mul_neg, neg_neg]

theorem centerRate_neg_left (ν c : ℝ) (k l : Wavevector) :
    centerRate ν c (-k) l = centerRate ν c k l := by
  simp only [centerRate, pairDamping_neg_left]

theorem centerRate_add_outputShift (ν c : ℝ) (k l : Wavevector) :
    centerRate ν c k l + outputShift ν k l = c + modeDamping ν (k + l) := by
  unfold centerRate outputShift rateDefect
  ring

theorem centerRate_sub_outputShift (ν c : ℝ) (k l : Wavevector) :
    centerRate ν c k l - outputShift ν k l = c + modeDamping ν (-k + l) := by
  simpa only [centerRate_neg_left, outputShift_neg_left, sub_eq_add_neg] using
    centerRate_add_outputShift ν c (-k) l

theorem centerRate_pos {ν c : ℝ} (hν : 0 ≤ ν) (hc : 0 < c) (k l : Wavevector) :
    0 < centerRate ν c k l := add_pos_of_pos_of_nonneg hc (pairDamping_nonneg hν k l)

theorem abs_outputShift_lt_centerRate {ν c : ℝ} (hν : 0 ≤ ν) (hc : 0 < c)
    (k l : Wavevector) : |outputShift ν k l| < centerRate ν c k l := by
  have hp : 0 < c + modeDamping ν (k + l) := by unfold modeDamping; positivity
  have hm : 0 < c + modeDamping ν (-k + l) := by unfold modeDamping; positivity
  rw [← centerRate_add_outputShift] at hp
  rw [← centerRate_sub_outputShift] at hm
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem integratedKernel_eq_defect {ν c : ℝ} (hν : 0 ≤ ν) (hc : 0 < c)
    (k l : Wavevector) :
    integratedKernel ν c k l = BalancedResolvent.defect (centerRate ν c k l) (outputShift ν k l) := by
  rw [integratedKernel, integral_weighted_multiplier_defect hν hc,
    BalancedResolvent.defect, centerRate_add_outputShift]
  unfold outputShift centerRate
  rw [neg_neg, mul_comm]

/-- The test-difference term is retained, even after exact heat integration. -/
theorem reflected_pairing_eq {ν c : ℝ} (hν : 0 ≤ ν) (hc : 0 < c)
    (k l : Wavevector) (x y : ℝ) :
    integratedKernel ν c k l * x + integratedKernel ν c (-k) l * y =
      (outputShift ν k l) ^ 2 /
        (centerRate ν c k l * ((centerRate ν c k l) ^ 2 - (outputShift ν k l) ^ 2)) * (x + y) -
      outputShift ν k l / ((centerRate ν c k l) ^ 2 - (outputShift ν k l) ^ 2) * (x - y) := by
  rw [integratedKernel_eq_defect hν hc, integratedKernel_eq_defect hν hc,
    centerRate_neg_left, outputShift_neg_left]
  exact BalancedResolvent.weighted_pair_eq (centerRate_pos hν hc k l)
    (abs_outputShift_lt_centerRate hν hc k l) x y

theorem reflected_kernel_sum_nonneg {ν c : ℝ} (hν : 0 ≤ ν) (hc : 0 < c)
    (k l : Wavevector) : 0 ≤ integratedKernel ν c k l + integratedKernel ν c (-k) l := by
  rw [integratedKernel_eq_defect hν hc, integratedKernel_eq_defect hν hc,
    centerRate_neg_left, outputShift_neg_left]
  exact BalancedResolvent.defect_add_reflected_nonneg (centerRate_pos hν hc k l)
    (abs_outputShift_lt_centerRate hν hc k l)

theorem abs_outputShift_le_half_centerRate_of_separated {ν c : ℝ}
    (hν : 0 ≤ ν) (hc : 0 ≤ c) (k l : Wavevector)
    (hkl : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖ / 4) :
    |outputShift ν k l| ≤ centerRate ν c k l / 2 := by
  have hr := abs_rateDefect_le hν k l
  rw [outputShift, abs_neg]
  apply hr.trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hkl
      (by positivity : 0 ≤ 2 * ν * (2 * Real.pi) ^ 2)) (norm_nonneg (frequencyVec l))
  unfold centerRate pairDamping modeDamping
  have hz : 0 ≤ ν * (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ ^ 2 := by positivity
  nlinarith

theorem abs_reflected_pairing_le_of_separated {ν c : ℝ}
    (hν : 0 ≤ ν) (hc : 0 < c) (k l : Wavevector)
    (hkl : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖ / 4) (x y : ℝ) :
    |integratedKernel ν c k l * x + integratedKernel ν c (-k) l * y| ≤
      (2 * (outputShift ν k l) ^ 2 / (centerRate ν c k l) ^ 3) * |x + y| +
        (2 * |outputShift ν k l| / (centerRate ν c k l) ^ 2) * |x - y| := by
  rw [integratedKernel_eq_defect hν hc, integratedKernel_eq_defect hν hc,
    centerRate_neg_left, outputShift_neg_left]
  exact BalancedResolvent.abs_weighted_pair_le (centerRate_pos hν hc k l)
    (abs_outputShift_le_half_centerRate_of_separated hν hc.le k l hkl) x y

theorem abs_outputShift_le_relative_centerRate {ν c : ℝ} (hν : 0 ≤ ν) (hc : 0 ≤ c)
    (k l : Wavevector) (hl : 0 < ‖frequencyVec l‖) :
    |outputShift ν k l| ≤ (2 * ‖frequencyVec k‖ / ‖frequencyVec l‖) * centerRate ν c k l := by
  rw [outputShift, abs_neg]
  apply (abs_rateDefect_le hν k l).trans
  have hlow : ν * (2 * Real.pi) ^ 2 * ‖frequencyVec l‖ ^ 2 ≤ centerRate ν c k l := by
    unfold centerRate pairDamping modeDamping
    have hz : 0 ≤ ν * (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ ^ 2 := by positivity
    linarith
  calc
    _ = (2 * ‖frequencyVec k‖ / ‖frequencyVec l‖) *
        (ν * (2 * Real.pi) ^ 2 * ‖frequencyVec l‖ ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)

theorem abs_reflected_pairing_le_ratio {ν c : ℝ} (hν : 0 ≤ ν) (hc : 0 < c)
    (k l : Wavevector) (hl : 0 < ‖frequencyVec l‖)
    (hkl : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖ / 4) (x y : ℝ) :
    |integratedKernel ν c k l * x + integratedKernel ν c (-k) l * y| ≤
      (8 * (‖frequencyVec k‖ / ‖frequencyVec l‖) ^ 2 / centerRate ν c k l) * |x + y| +
        (4 * (‖frequencyVec k‖ / ‖frequencyVec l‖) / centerRate ν c k l) * |x - y| := by
  rw [integratedKernel_eq_defect hν hc, integratedKernel_eq_defect hν hc,
    centerRate_neg_left, outputShift_neg_left]
  have hhalf : 2 * ‖frequencyVec k‖ / ‖frequencyVec l‖ ≤ 1 / 2 :=
    (div_le_iff₀ hl).mpr (by linarith)
  have h := BalancedResolvent.abs_weighted_pair_le_ratio (centerRate_pos hν hc k l)
    (by positivity : 0 ≤ 2 * ‖frequencyVec k‖ / ‖frequencyVec l‖) hhalf
    (abs_outputShift_le_relative_centerRate hν hc.le k l hl) x y
  apply h.trans_eq
  ring

theorem abs_integratedKernel_le_ratio {ν c : ℝ} (hν : 0 ≤ ν) (hc : 0 < c)
    (k l : Wavevector) (hl : 0 < ‖frequencyVec l‖)
    (hkl : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖ / 4) :
    |integratedKernel ν c k l| ≤
      4 * (‖frequencyVec k‖ / ‖frequencyVec l‖) / centerRate ν c k l := by
  rw [integratedKernel_eq_defect hν hc]
  have hhalf : 2 * ‖frequencyVec k‖ / ‖frequencyVec l‖ ≤ 1 / 2 :=
    (div_le_iff₀ hl).mpr (by linarith)
  exact (BalancedResolvent.abs_defect_le_ratio (centerRate_pos hν hc k l)
    (by positivity : 0 ≤ 2 * ‖frequencyVec k‖ / ‖frequencyVec l‖) hhalf
    (abs_outputShift_le_relative_centerRate hν hc.le k l hl)).trans_eq (by ring)

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorReflection
