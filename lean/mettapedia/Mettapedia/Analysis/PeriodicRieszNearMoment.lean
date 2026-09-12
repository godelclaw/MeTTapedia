import Mettapedia.Analysis.PeriodicRieszOperator

/-!
# Uniform smallness of the near-diagonal second moment

The annular kernels have a uniformly bounded first moment. Hence their
second moment inside radius `r` is at most `r` times one fixed constant.
The estimate is uniform in the frequency cutoff and does not require a
bound on the unweighted kernel mass.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis

open MeasureTheory Set UnitTorusPeriodization
open scoped SchwartzMap

namespace AnnularRieszKernel

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

def firstMoment (i j : Fin d) : ℝ := ∫ x : Rd, ‖x‖ * ‖kernel i j x‖

theorem firstMoment_nonneg (i j : Fin d) : 0 ≤ firstMoment i j :=
  integral_nonneg (fun _ ↦ by positivity)

theorem firstMoment_dyadicKernel (i j : Fin d) (n : ℕ) :
    (∫ x : Rd, ‖x‖ * ‖dyadicKernel i j n x‖) =
      2 * (1 / 2 : ℝ) ^ n * firstMoment i j := by
  have h := SchwartzDilation.moment_dilate (scale n) (scale_pos n).ne' (kernel i j) 1
  simpa only [dyadicKernel, pow_one, abs_of_pos (scale_pos n), inv_scale,
    firstMoment, mul_comm, mul_left_comm, mul_assoc] using h

theorem firstMoment_partialKernel_le (i j : Fin d) (N : ℕ) :
    (∫ x : Rd, ‖x‖ * ‖partialKernel i j N x‖) ≤ 4 * firstMoment i j := by
  have hi (n : ℕ) : Integrable (fun x : Rd ↦ ‖x‖ * ‖dyadicKernel i j n x‖) := by
    simpa only [pow_one] using (dyadicKernel i j n).integrable_pow_mul volume 1
  have hp : (∫ x : Rd, ‖x‖ * ‖partialKernel i j N x‖) ≤
      ∑ n ∈ Finset.range N, 2 * (1 / 2 : ℝ) ^ n * firstMoment i j := by
    simp_rw [← firstMoment_dyadicKernel]
    rw [← integral_finsetSum _ (fun n _ ↦ hi n)]
    apply integral_mono (by simpa only [pow_one] using
      (partialKernel i j N).integrable_pow_mul volume 1)
      (integrable_finsetSum _ (fun n _ ↦ hi n))
    intro x
    simp only [partialKernel, sum_apply, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
  have hs : (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) ≤ 2 := by
    have h := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    have hb := h.summable.sum_le_tsum (Finset.range N) (fun n _ ↦ by positivity)
    rw [h.tsum_eq] at hb
    norm_num at hb
    exact hb
  calc
    _ ≤ _ := hp
    _ = (2 * firstMoment i j) * ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ (2 * firstMoment i j) * 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity [firstMoment_nonneg i j])
    _ = _ := by ring

end AnnularRieszKernel

namespace PeriodicRieszNearMoment

variable {d : ℕ}
local notation "Td" => UnitAddTorus (Fin d)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

theorem integrable_entryFirstMoment (i j : Fin d) (N : ℕ) :
    Integrable (fun x : Td ↦ ‖x‖ * ‖PeriodicRieszKernel.kernel i j N x‖) := by
  simpa only [pow_one, PeriodicRieszKernel.kernel] using
    integrable_moment_periodize (AnnularRieszKernel.partialKernel i j N) 1

theorem entryFirstMoment_le (i j : Fin d) (N : ℕ) :
    (∫ x : Td, ‖x‖ * ‖PeriodicRieszKernel.kernel i j N x‖) ≤
      4 * AnnularRieszKernel.firstMoment i j := by
  have h := integral_moment_periodize_le (AnnularRieszKernel.partialKernel i j N) 1
  simp only [pow_one] at h
  exact h.trans (AnnularRieszKernel.firstMoment_partialKernel_le i j N)

def firstMomentBound (d : ℕ) : ℝ :=
  4 * ∑ i : Fin d, ∑ j : Fin d, AnnularRieszKernel.firstMoment i j

theorem firstMomentBound_nonneg (d : ℕ) : 0 ≤ firstMomentBound d := by
  unfold firstMomentBound
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ ↦
    Finset.sum_nonneg (fun j _ ↦ AnnularRieszKernel.firstMoment_nonneg i j)))

theorem integrable_rawFirstMoment (N : ℕ) :
    Integrable (fun x : Td ↦ ‖x‖ * ‖PeriodicRieszOperator.rawKernel N x‖) := by
  have hi := integrable_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) ↦
    integrable_finsetSum Finset.univ (fun j _ ↦ integrable_entryFirstMoment i j N))
  apply hi.mono' ((continuous_norm.measurable.mul
    (PeriodicRieszOperator.measurable_rawKernel N).norm).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity)]
  simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left
    (PeriodicRieszOperator.norm_rawKernel_le N x) (norm_nonneg x)

theorem rawFirstMoment_le (N : ℕ) :
    (∫ x : Td, ‖x‖ * ‖PeriodicRieszOperator.rawKernel N x‖) ≤ firstMomentBound d := by
  have hi := integrable_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) ↦
    integrable_finsetSum Finset.univ (fun j _ ↦ integrable_entryFirstMoment i j N))
  calc
    _ ≤ ∫ x : Td, ∑ i : Fin d, ∑ j : Fin d, ‖x‖ * ‖PeriodicRieszKernel.kernel i j N x‖ :=
      integral_mono (integrable_rawFirstMoment N) hi (fun x ↦ by
        simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left
          (PeriodicRieszOperator.norm_rawKernel_le N x) (norm_nonneg x))
    _ = ∑ i : Fin d, ∑ j : Fin d, ∫ x : Td, ‖x‖ * ‖PeriodicRieszKernel.kernel i j N x‖ := by
      rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦
        integrable_entryFirstMoment i j N))]
      congr 1
      funext i
      exact integral_finsetSum _ (fun j _ ↦ integrable_entryFirstMoment i j N)
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, 4 * AnnularRieszKernel.firstMoment i j :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ entryFirstMoment_le i j N))
    _ = _ := by simp only [firstMomentBound, Finset.mul_sum]

theorem integrable_firstMoment (N : ℕ) :
    Integrable (fun x : Td ↦ ‖x‖ * ‖PeriodicRieszOperator.kernel N x‖) := by
  have hn : Integrable (fun x : Td ↦ ‖x‖ * ‖PeriodicRieszOperator.rawKernel N (-x)‖) := by
    simpa only [norm_neg] using (integrable_rawFirstMoment (d := d) N).comp_neg
  have hi := ((integrable_rawFirstMoment N).add hn).const_mul (1 / 2 : ℝ)
  apply hi.mono' ((continuous_norm.measurable.mul
    (PeriodicRieszOperator.measurable_kernel N).norm).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity)]
  have hb := mul_le_mul_of_nonneg_left (PeriodicRieszOperator.norm_kernel_le N x) (norm_nonneg x)
  simpa only [Pi.add_apply, mul_add, mul_left_comm] using hb

theorem firstMoment_le (N : ℕ) :
    (∫ x : Td, ‖x‖ * ‖PeriodicRieszOperator.kernel N x‖) ≤ firstMomentBound d := by
  have hn : Integrable (fun x : Td ↦ ‖x‖ * ‖PeriodicRieszOperator.rawKernel N (-x)‖) := by
    simpa only [norm_neg] using (integrable_rawFirstMoment (d := d) N).comp_neg
  have he : (∫ x : Td, ‖x‖ * ‖PeriodicRieszOperator.rawKernel N (-x)‖) =
      ∫ x : Td, ‖x‖ * ‖PeriodicRieszOperator.rawKernel N x‖ := by
    simpa only [norm_neg] using integral_neg_eq_self
      (fun x : Td ↦ ‖x‖ * ‖PeriodicRieszOperator.rawKernel N x‖) volume
  have hb := integral_mono (integrable_firstMoment N)
    (((integrable_rawFirstMoment N).add hn).const_mul (1 / 2 : ℝ)) (fun x ↦ by
      have h := mul_le_mul_of_nonneg_left (PeriodicRieszOperator.norm_kernel_le N x) (norm_nonneg x)
      simpa only [Pi.add_apply, mul_add, mul_left_comm] using h)
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add (integrable_rawFirstMoment N) hn, he] at hb
  linarith only [hb, rawFirstMoment_le (d := d) N]

theorem nearSecondMoment_le (r : ℝ) (hr : 0 ≤ r) (N : ℕ) :
    (∫ x in Metric.ball (0 : Td) r, ‖x‖ ^ 2 * ‖PeriodicRieszOperator.kernel N x‖) ≤
      r * firstMomentBound d := by
  have hm := setIntegral_mono_on (s := Metric.ball (0 : Td) r)
    (PeriodicRieszOperator.integrable_secondMoment N).integrableOn
    ((integrable_firstMoment N).const_mul r).integrableOn measurableSet_ball (fun x hx ↦ by
      have hx' : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
      have h := mul_le_mul_of_nonneg_right hx' (mul_nonneg (norm_nonneg x)
        (norm_nonneg (PeriodicRieszOperator.kernel N x)))
      nlinarith only [h])
  have hb := setIntegral_le_integral (s := Metric.ball (0 : Td) r)
    ((integrable_firstMoment (d := d) N).const_mul r)
    (Filter.Eventually.of_forall (fun x ↦ by positivity))
  have hf := mul_le_mul_of_nonneg_left (firstMoment_le (d := d) N) hr
  simp only [integral_const_mul] at hb hm
  exact hm.trans (hb.trans hf)

end PeriodicRieszNearMoment
end Mettapedia.Analysis
