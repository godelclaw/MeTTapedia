import Mettapedia.Analysis.DyadicAnnulusPartition

/-!
# A globally smooth dyadic normalization multiplier

The reciprocal of the dyadic sum need not extend continuously to zero.
A smooth inner buffer replaces it by one near zero, without changing its
value on the annular cutoff's support. Multiplication by this correction
therefore normalizes an existing annularly supported symbol exactly.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DyadicAnnulus

open Set Filter SmoothAnnulus
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

def smoothCorrection (x : E) : ℝ :=
  (innerBuffer (E := E)) x + (1 - (innerBuffer (E := E)) x) / normalizer x

theorem smoothCorrection_eq_one_of_norm_le (x : E) (hx : ‖x‖ ≤ 1 / 4) :
    smoothCorrection x = 1 := by
  have h : (innerBuffer (E := E)) x = 1 := (innerBuffer (E := E)).one_of_mem_closedBall (by
    simpa [innerBuffer, Metric.mem_closedBall, dist_zero_right] using hx)
  simp [smoothCorrection, h]

@[simp] theorem smoothCorrection_zero : smoothCorrection (0 : E) = 1 :=
  smoothCorrection_eq_one_of_norm_le _ (by simp)

theorem smoothCorrection_eq_inv_of_cutoff_ne_zero (x : E) (hx : cutoff x ≠ 0) :
    smoothCorrection x = (normalizer x)⁻¹ := by
  have h : (innerBuffer (E := E)) x = 0 := (innerBuffer (E := E)).zero_of_le_dist (by
    simpa [innerBuffer, dist_zero_right] using (norm_bounds_of_cutoff_ne_zero x hx).1.le)
  simp [smoothCorrection, h]

theorem normalizedCutoff_eq_mul_smoothCorrection (x : E) :
    normalizedCutoff x = cutoff x * smoothCorrection x := by
  by_cases hx : cutoff x = 0
  · simp [normalizedCutoff, hx]
  · rw [smoothCorrection_eq_inv_of_cutoff_ne_zero x hx]
    rfl

theorem smoothCorrection_nonneg (x : E) : 0 ≤ smoothCorrection x :=
  add_nonneg (innerBuffer (E := E)).nonneg
    (div_nonneg (sub_nonneg.mpr (innerBuffer (E := E)).le_one) (normalizer_nonneg x))

theorem smoothCorrection_le_one (x : E) : smoothCorrection x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h := div_le_self (sub_nonneg.mpr ((innerBuffer (E := E)).le_one (x := x)))
    (normalizer_bounds x hx).1
  unfold smoothCorrection
  linarith

@[fun_prop] theorem contDiff_smoothCorrection : ContDiff ℝ ∞ (smoothCorrection (E := E)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    have hU : ∀ᶠ y : E in 𝓝 0, y ∈ Metric.ball 0 (1 / 4 : ℝ) :=
      Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [hU] with y hy
    have hy' : ‖y‖ < 1 / 4 := by simpa [Metric.mem_ball, dist_zero_right] using hy
    exact smoothCorrection_eq_one_of_norm_le y hy'.le
  · exact (innerBuffer (E := E)).contDiff.contDiffAt.add
      ((contDiffAt_const.sub (innerBuffer (E := E)).contDiff.contDiffAt).div
        (contDiffAt_normalizer x hx)
        (ne_of_gt (lt_of_lt_of_le (by norm_num) (normalizer_bounds x hx).1)))

end Mettapedia.Analysis.DyadicAnnulus
