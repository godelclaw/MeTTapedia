import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! A smooth annular cutoff with a larger buffer and a positive squared-norm denominator. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SmoothAnnulus

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

def innerBump : ContDiffBump (0 : E) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
def outerBump : ContDiffBump (0 : E) := ⟨2, 4, by norm_num, by norm_num⟩
def innerBuffer : ContDiffBump (0 : E) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
def outerBuffer : ContDiffBump (0 : E) := ⟨4, 8, by norm_num, by norm_num⟩

def cutoff (x : E) : ℝ := (outerBump (E := E)) x * (1 - (innerBump (E := E)) x)
def buffer (x : E) : ℝ := (outerBuffer (E := E)) x * (1 - (innerBuffer (E := E)) x)
def denominator (x : E) : ℝ := ‖x‖ ^ 2 + (1 - buffer x)

theorem cutoff_nonneg (x : E) : 0 ≤ cutoff x :=
  mul_nonneg (outerBump (E := E)).nonneg (sub_nonneg.mpr (innerBump (E := E)).le_one)

theorem cutoff_le_one (x : E) : cutoff x ≤ 1 := by
  exact (mul_le_mul_of_nonneg_left (sub_le_self 1 (innerBump (E := E)).nonneg) (outerBump (E := E)).nonneg).trans
    (by simpa using (outerBump (E := E)).le_one (x := x))

theorem buffer_nonneg (x : E) : 0 ≤ buffer x :=
  mul_nonneg (outerBuffer (E := E)).nonneg (sub_nonneg.mpr (innerBuffer (E := E)).le_one)

theorem buffer_le_one (x : E) : buffer x ≤ 1 := by
  exact (mul_le_mul_of_nonneg_left (sub_le_self 1 (innerBuffer (E := E)).nonneg) (outerBuffer (E := E)).nonneg).trans
    (by simpa using (outerBuffer (E := E)).le_one (x := x))

theorem norm_bounds_of_cutoff_ne_zero (x : E) (hx : cutoff x ≠ 0) :
    1 / 2 < ‖x‖ ∧ ‖x‖ < 4 := by
  have ho : (outerBump (E := E)) x ≠ 0 := (mul_ne_zero_iff.mp hx).1
  have hi : (innerBump (E := E)) x ≠ 1 := by
    intro h
    simp [cutoff, h] at hx
  constructor
  · by_contra hn
    apply hi
    apply (innerBump (E := E)).one_of_mem_closedBall
    simpa [innerBump, Metric.mem_closedBall, dist_zero_right] using (le_of_not_gt hn)
  · have hmem := ho
    change x ∈ Function.support (outerBump (E := E)) at hmem
    rw [ContDiffBump.support_eq] at hmem
    simpa [outerBump, Metric.mem_ball, dist_zero_right] using hmem

theorem norm_bounds_of_buffer_ne_zero (x : E) (hx : buffer x ≠ 0) :
    1 / 4 < ‖x‖ ∧ ‖x‖ < 8 := by
  have ho : (outerBuffer (E := E)) x ≠ 0 := (mul_ne_zero_iff.mp hx).1
  have hi : (innerBuffer (E := E)) x ≠ 1 := by
    intro h
    simp [buffer, h] at hx
  constructor
  · by_contra hn
    apply hi
    apply (innerBuffer (E := E)).one_of_mem_closedBall
    simpa [innerBuffer, Metric.mem_closedBall, dist_zero_right] using (le_of_not_gt hn)
  · have hmem := ho
    change x ∈ Function.support (outerBuffer (E := E)) at hmem
    rw [ContDiffBump.support_eq] at hmem
    simpa [outerBuffer, Metric.mem_ball, dist_zero_right] using hmem

theorem buffer_eq_one_of_cutoff_ne_zero (x : E) (hx : cutoff x ≠ 0) : buffer x = 1 := by
  have hb := norm_bounds_of_cutoff_ne_zero x hx
  have ho : (outerBuffer (E := E)) x = 1 := (outerBuffer (E := E)).one_of_mem_closedBall (by
    simpa [outerBuffer, Metric.mem_closedBall, dist_zero_right] using hb.2.le)
  have hi : (innerBuffer (E := E)) x = 0 := (innerBuffer (E := E)).zero_of_le_dist (by
    simpa [innerBuffer, dist_zero_right] using hb.1.le)
  simp [buffer, ho, hi]

theorem cutoff_eq_one (x : E) (hlo : 1 ≤ ‖x‖) (hhi : ‖x‖ ≤ 2) : cutoff x = 1 := by
  have ho : (outerBump (E := E)) x = 1 := (outerBump (E := E)).one_of_mem_closedBall (by
    simpa [outerBump, Metric.mem_closedBall, dist_zero_right] using hhi)
  have hi : (innerBump (E := E)) x = 0 := (innerBump (E := E)).zero_of_le_dist (by
    simpa [innerBump, dist_zero_right] using hlo)
  simp [cutoff, ho, hi]

theorem buffer_zero : buffer (0 : E) = 0 := by
  have h : (innerBuffer (E := E)) (0 : E) = 1 := (innerBuffer (E := E)).one_of_mem_closedBall (by
    simp [innerBuffer, Metric.mem_closedBall])
  simp [buffer, h]

theorem denominator_pos (x : E) : 0 < denominator x := by
  by_cases hx : x = 0
  · simp [denominator, hx, buffer_zero]
  · have hp := sq_pos_of_pos (norm_pos_iff.mpr hx)
    have hb := buffer_le_one x
    unfold denominator
    linarith

theorem denominator_eq_norm_sq (x : E) (hx : cutoff x ≠ 0) : denominator x = ‖x‖ ^ 2 := by
  simp [denominator, buffer_eq_one_of_cutoff_ne_zero x hx]

theorem contDiff_cutoff : ContDiff ℝ ∞ (cutoff (E := E)) :=
  (outerBump (E := E)).contDiff.mul (contDiff_const.sub (innerBump (E := E)).contDiff)

theorem contDiff_buffer : ContDiff ℝ ∞ (buffer (E := E)) :=
  (outerBuffer (E := E)).contDiff.mul (contDiff_const.sub (innerBuffer (E := E)).contDiff)

theorem hasCompactSupport_cutoff [FiniteDimensional ℝ E] : HasCompactSupport (cutoff (E := E)) :=
  (outerBump (E := E)).hasCompactSupport.mul_right

theorem tsupport_cutoff_subset : tsupport (cutoff (E := E)) ⊆ Metric.closedBall 0 4 := by
  unfold cutoff
  calc
    _ ⊆ tsupport (outerBump (E := E) : E → ℝ) := tsupport_mul_subset_left
    _ = Metric.closedBall 0 4 := (outerBump (E := E)).tsupport_eq

end Mettapedia.Analysis.SmoothAnnulus
