import Mettapedia.Analysis.SmoothAnnulus
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputCoordinates

/-!
# Buffered cutoffs for the low-output pressure family

The input and normalized output lie in annuli. A separate parameter buffer
keeps the receiver away from zero wherever all buffers are nonzero. The
regularized receiver denominator is positive everywhere and exact on the
retained support.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff

open Mettapedia.Analysis.SmoothAnnulus
open scoped ContDiff

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "P" => R3 × R3

def parameterCutoff : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
def parameterBuffer : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
def ratio (t : ℝ) : ℝ := t / 128
def receiver (t : ℝ) (p : P) : R3 := ratio t • p.2 - p.1
def retained (t : ℝ) (p : P) : ℝ := parameterCutoff t * cutoff p.1 * cutoff p.2
def jointBuffer (t : ℝ) (p : P) : ℝ := parameterBuffer t * buffer p.1 * buffer p.2
def receiverDenominator (t : ℝ) (p : P) : ℝ := ‖receiver t p‖ ^ 2 + (1 - jointBuffer t p)

theorem parameterBuffer_eq_one (t : ℝ) (ht : parameterCutoff t ≠ 0) : parameterBuffer t = 1 := by
  have h : |t| < 1 := by
    have hmem : t ∈ Function.support parameterCutoff := ht
    rw [ContDiffBump.support_eq] at hmem
    simpa [parameterCutoff, Metric.mem_ball, Real.dist_eq] using hmem
  apply parameterBuffer.one_of_mem_closedBall
  simpa [parameterBuffer, Metric.mem_closedBall, Real.dist_eq] using h.le

theorem parameterCutoff_eq_one (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) : parameterCutoff t = 1 := by
  apply parameterCutoff.one_of_mem_closedBall
  simpa [parameterCutoff, Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg ht.1] using ht.2

theorem jointBuffer_nonneg (t : ℝ) (p : P) : 0 ≤ jointBuffer t p :=
  mul_nonneg (mul_nonneg parameterBuffer.nonneg (buffer_nonneg _)) (buffer_nonneg _)

theorem jointBuffer_le_one (t : ℝ) (p : P) : jointBuffer t p ≤ 1 := by
  have h1 : parameterBuffer t * buffer p.1 ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left (buffer_le_one p.1) parameterBuffer.nonneg).trans
      (by simpa using parameterBuffer.le_one (x := t))
  exact (mul_le_mul_of_nonneg_right h1 (buffer_nonneg p.2)).trans
    (by simpa using buffer_le_one p.2)

theorem receiver_ne_zero_of_jointBuffer_ne_zero (t : ℝ) (p : P) (hb : jointBuffer t p ≠ 0) :
    receiver t p ≠ 0 := by
  have hp := mul_ne_zero_iff.mp hb
  have ht := (mul_ne_zero_iff.mp hp.1).1
  have hk := norm_bounds_of_buffer_ne_zero p.1 (mul_ne_zero_iff.mp hp.1).2
  have hq := norm_bounds_of_buffer_ne_zero p.2 hp.2
  have htn : |t| < 2 := by
    have hmem : t ∈ Function.support parameterBuffer := ht
    rw [ContDiffBump.support_eq] at hmem
    simpa [parameterBuffer, Metric.mem_ball, Real.dist_eq] using hmem
  intro hz
  have he : ratio t • p.2 = p.1 := sub_eq_zero.mp hz
  have hsmall : ‖ratio t • p.2‖ ≤ (2 / 128 : ℝ) * 8 := by
    rw [norm_smul, Real.norm_eq_abs, ratio, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 128)]
    exact mul_le_mul (div_le_div_of_nonneg_right htn.le (by norm_num)) hq.2.le
      (norm_nonneg _) (by norm_num)
  rw [he] at hsmall
  linarith

theorem receiverDenominator_pos (t : ℝ) (p : P) : 0 < receiverDenominator t p := by
  by_cases hb : jointBuffer t p = 0
  · unfold receiverDenominator
    rw [hb]
    positivity
  · have hp := sq_pos_of_pos (norm_pos_iff.mpr (receiver_ne_zero_of_jointBuffer_ne_zero t p hb))
    have hle := jointBuffer_le_one t p
    unfold receiverDenominator
    linarith

theorem buffers_eq_one_of_retained_ne_zero (t : ℝ) (p : P) (hr : retained t p ≠ 0) :
    buffer p.1 = 1 ∧ buffer p.2 = 1 ∧ jointBuffer t p = 1 := by
  have hp := mul_ne_zero_iff.mp hr
  have ht := (mul_ne_zero_iff.mp hp.1).1
  have hk := buffer_eq_one_of_cutoff_ne_zero p.1 (mul_ne_zero_iff.mp hp.1).2
  have hq := buffer_eq_one_of_cutoff_ne_zero p.2 hp.2
  exact ⟨hk, hq, by simp [jointBuffer, hk, hq, parameterBuffer_eq_one t ht]⟩

theorem receiverDenominator_eq_of_retained_ne_zero (t : ℝ) (p : P) (hr : retained t p ≠ 0) :
    receiverDenominator t p = ‖receiver t p‖ ^ 2 := by
  simp [receiverDenominator, (buffers_eq_one_of_retained_ne_zero t p hr).2.2]

theorem contDiff_receiver : ContDiff ℝ ∞ (fun z : ℝ × P ↦ receiver z.1 z.2) := by
  unfold receiver ratio
  fun_prop

theorem contDiff_retained : ContDiff ℝ ∞ (fun z : ℝ × P ↦ retained z.1 z.2) := by
  exact ((parameterCutoff.contDiff.comp contDiff_fst).mul
    (contDiff_cutoff.comp (contDiff_fst.comp contDiff_snd))).mul
    (contDiff_cutoff.comp (contDiff_snd.comp contDiff_snd))

theorem contDiff_jointBuffer : ContDiff ℝ ∞ (fun z : ℝ × P ↦ jointBuffer z.1 z.2) := by
  exact ((parameterBuffer.contDiff.comp contDiff_fst).mul
    (contDiff_buffer.comp (contDiff_fst.comp contDiff_snd))).mul
    (contDiff_buffer.comp (contDiff_snd.comp contDiff_snd))

theorem contDiff_receiverDenominator : ContDiff ℝ ∞ (fun z : ℝ × P ↦ receiverDenominator z.1 z.2) :=
  ((contDiff_norm_sq ℝ).comp contDiff_receiver).add (contDiff_const.sub contDiff_jointBuffer)

theorem tsupport_retained_subset (t : ℝ) :
    tsupport (retained t) ⊆ Metric.closedBall (0 : R3) 4 ×ˢ Metric.closedBall (0 : R3) 4 := by
  apply closure_minimal _ (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall)
  intro p hp
  have hh := mul_ne_zero_iff.mp hp
  have hk := (norm_bounds_of_cutoff_ne_zero p.1 (mul_ne_zero_iff.mp hh.1).2).2.le
  have hq := (norm_bounds_of_cutoff_ne_zero p.2 hh.2).2.le
  simpa only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right] using And.intro hk hq

end Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCutoff
