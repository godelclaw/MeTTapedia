import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorReflection
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LerayStretchExchange

/-!
# Quadratic reflected gain for the actual Leray projector tests

The two output projections are constructed at `l+k` and `l-k`. Their
difference supplies the extra low/high factor needed by the odd resolvent
channel. This controls the projector test, not all factors of the quintic
adjoint or the sum of its nonlinear interactions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorLerayReflection

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail PancakeFixedOutputVelocityBound
open LerayStretchExchange FourierHeatCommutatorReflection

theorem norm_frequency_neg (k : Wavevector) : ‖frequencyVec (-k)‖ = ‖frequencyVec k‖ := by
  have h : ‖frequencyVec (-k)‖ ^ 2 = ‖frequencyVec k‖ ^ 2 := by
    simp [norm_frequencyVec_sq, Pi.neg_apply]
  nlinarith [norm_nonneg (frequencyVec (-k)), norm_nonneg (frequencyVec k)]

theorem half_large_norm_le_output (k l : Wavevector)
    (hkl : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖ / 4) :
    ‖frequencyVec l‖ / 2 ≤ ‖frequencyVec (k + l)‖ := by
  have h := norm_sub_le (frequencyVec (k + l)) (frequencyVec k)
  rw [← frequencyVec_sub, show k + l - k = l by abel] at h
  linarith [norm_nonneg (frequencyVec l)]

theorem output_ne_zero (k l : Wavevector) (hl : 0 < ‖frequencyVec l‖)
    (hkl : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖ / 4) : k + l ≠ 0 := by
  intro hz
  have h := half_large_norm_le_output k l hkl
  have hzero : frequencyVec 0 = 0 := by ext i; simp [frequencyVec, coefficientVec, wavevectorCoefficient]
  rw [hz, hzero, norm_zero] at h
  linarith

theorem norm_leray_sub_reflected_le (k l : Wavevector) (hl : 0 < ‖frequencyVec l‖)
    (hkl : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖ / 4) (v : VelocityCoefficient) :
    ‖coefficientVec (lerayMode (k + l) v - lerayMode (-k + l) v)‖ ≤
      (16 * ‖frequencyVec k‖ / ‖frequencyVec l‖) * ‖coefficientVec v‖ := by
  have hkln : ‖frequencyVec (-k)‖ ≤ ‖frequencyVec l‖ / 4 := by
    simpa only [norm_frequency_neg] using hkl
  have hq := half_large_norm_le_output k l hkl
  have hqp : 0 < ‖frequencyVec (k + l)‖ := by linarith
  have h := norm_lerayMode_sub_le_output (k + l) (-(-k + l)) v
    (output_ne_zero k l hl hkl) (neg_ne_zero.mpr (output_ne_zero (-k) l hl hkln))
  rw [lerayMode_neg_frequency, show k + l + -(-k + l) = k + k by abel,
    frequencyVec_add] at h
  have he : ‖frequencyVec k + frequencyVec k‖ = 2 * ‖frequencyVec k‖ := by
    rw [← two_smul ℝ (frequencyVec k), norm_smul]
    norm_num
  rw [he] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (div_le_div_iff₀ hqp hl).mpr
  nlinarith [mul_le_mul_of_nonneg_left hq (norm_nonneg (frequencyVec k))]

def lerayTest (q : Wavevector) (v w : VelocityCoefficient) : ℝ :=
  ⟪coefficientVec (lerayMode q v), coefficientVec w⟫

theorem abs_lerayTest_le (q : Wavevector) (v w : VelocityCoefficient) :
    |lerayTest q v w| ≤ ‖coefficientVec v‖ * ‖coefficientVec w‖ :=
  (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_lerayMode_le q v) (norm_nonneg _))

theorem abs_lerayTest_add_le (q r : Wavevector) (v w : VelocityCoefficient) :
    |lerayTest q v w + lerayTest r v w| ≤ 2 * (‖coefficientVec v‖ * ‖coefficientVec w‖) := by
  have h := (abs_add_le (lerayTest q v w) (lerayTest r v w)).trans
    (add_le_add (abs_lerayTest_le q v w) (abs_lerayTest_le r v w))
  exact h.trans_eq (by ring)

theorem abs_lerayTest_sub_reflected_le (k l : Wavevector) (hl : 0 < ‖frequencyVec l‖)
    (hkl : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖ / 4) (v w : VelocityCoefficient) :
    |lerayTest (k + l) v w - lerayTest (-k + l) v w| ≤
      (16 * ‖frequencyVec k‖ / ‖frequencyVec l‖) *
        (‖coefficientVec v‖ * ‖coefficientVec w‖) := by
  unfold lerayTest
  rw [← inner_sub_left]
  have h := (abs_real_inner_le_norm
    (coefficientVec (lerayMode (k + l) v - lerayMode (-k + l) v)) (coefficientVec w)).trans
      (mul_le_mul_of_nonneg_right (norm_leray_sub_reflected_le k l hl hkl v) (norm_nonneg _))
  exact h.trans_eq (by ring)

/-- The first-order kernel mismatch is paid by an actual projector difference. -/
theorem abs_reflected_leray_pairing_le {ν c : ℝ} (hν : 0 ≤ ν) (hc : 0 < c)
    (k l : Wavevector) (hl : 0 < ‖frequencyVec l‖)
    (hkl : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖ / 4) (v w : VelocityCoefficient) :
    |integratedKernel ν c k l * lerayTest (k + l) v w +
      integratedKernel ν c (-k) l * lerayTest (-k + l) v w| ≤
      (80 * (‖frequencyVec k‖ / ‖frequencyVec l‖) ^ 2 / centerRate ν c k l) *
        (‖coefficientVec v‖ * ‖coefficientVec w‖) := by
  have ha := centerRate_pos hν hc k l
  apply (abs_reflected_pairing_le_ratio hν hc k l hl hkl
    (lerayTest (k + l) v w) (lerayTest (-k + l) v w)).trans
  calc
    _ ≤ (8 * (‖frequencyVec k‖ / ‖frequencyVec l‖) ^ 2 / centerRate ν c k l) *
          (2 * (‖coefficientVec v‖ * ‖coefficientVec w‖)) +
        (4 * (‖frequencyVec k‖ / ‖frequencyVec l‖) / centerRate ν c k l) *
          ((16 * ‖frequencyVec k‖ / ‖frequencyVec l‖) *
            (‖coefficientVec v‖ * ‖coefficientVec w‖)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (abs_lerayTest_add_le _ _ v w) (by positivity)
      · exact mul_le_mul_of_nonneg_left (abs_lerayTest_sub_reflected_le k l hl hkl v w) (by positivity)
    _ = _ := by ring

theorem abs_lerayTest_sub_le (q : Wavevector) (v w v' w' : VelocityCoefficient) :
    |lerayTest q v' w' - lerayTest q v w| ≤
      ‖coefficientVec (v' - v)‖ * ‖coefficientVec w'‖ +
        ‖coefficientVec v‖ * ‖coefficientVec (w' - w)‖ := by
  have he : lerayTest q v' w' - lerayTest q v w =
      lerayTest q (v' - v) w' + lerayTest q v (w' - w) := by
    unfold lerayTest
    rw [lerayMode_sub]
    change ⟪coefficientVec (lerayMode q v'), coefficientVec w'⟫ -
      ⟪coefficientVec (lerayMode q v), coefficientVec w⟫ =
      ⟪coefficientVec (lerayMode q v') - coefficientVec (lerayMode q v), coefficientVec w'⟫ +
      ⟪coefficientVec (lerayMode q v), coefficientVec w' - coefficientVec w⟫
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (abs_lerayTest_le q (v' - v) w')
    (abs_lerayTest_le q v (w' - w)))

/-- Changes of the vector factors remain explicit, rather than being declared coherent. -/
theorem abs_reflected_leray_pairing_le_with_variation {ν c : ℝ}
    (hν : 0 ≤ ν) (hc : 0 < c) (k l : Wavevector) (hl : 0 < ‖frequencyVec l‖)
    (hkl : ‖frequencyVec k‖ ≤ ‖frequencyVec l‖ / 4) (v w v' w' : VelocityCoefficient) :
    |integratedKernel ν c k l * lerayTest (k + l) v w +
      integratedKernel ν c (-k) l * lerayTest (-k + l) v' w'| ≤
      (80 * (‖frequencyVec k‖ / ‖frequencyVec l‖) ^ 2 / centerRate ν c k l) *
        (‖coefficientVec v‖ * ‖coefficientVec w‖) +
      (4 * (‖frequencyVec k‖ / ‖frequencyVec l‖) / centerRate ν c k l) *
        (‖coefficientVec (v' - v)‖ * ‖coefficientVec w'‖ +
          ‖coefficientVec v‖ * ‖coefficientVec (w' - w)‖) := by
  have hkln : ‖frequencyVec (-k)‖ ≤ ‖frequencyVec l‖ / 4 := by
    simpa only [norm_frequency_neg] using hkl
  have hk := abs_integratedKernel_le_ratio hν hc (-k) l hl hkln
  simp only [norm_frequency_neg, centerRate_neg_left] at hk
  have ha := centerRate_pos hν hc k l
  have he : integratedKernel ν c k l * lerayTest (k + l) v w +
      integratedKernel ν c (-k) l * lerayTest (-k + l) v' w' =
      (integratedKernel ν c k l * lerayTest (k + l) v w +
        integratedKernel ν c (-k) l * lerayTest (-k + l) v w) +
      integratedKernel ν c (-k) l * (lerayTest (-k + l) v' w' - lerayTest (-k + l) v w) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add (abs_reflected_leray_pairing_le hν hc k l hl hkl v w)
  rw [abs_mul]
  exact mul_le_mul hk (abs_lerayTest_sub_le (-k + l) v w v' w') (abs_nonneg _) (by positivity)

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorLerayReflection
