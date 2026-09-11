import Mettapedia.Analysis.LocallyLipschitz
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A square-root norm weight multiplied by its vector

The scalar factor need not be differentiable at zero. Its product with the
vector is locally Lipschitz, and has derivative zero at zero. The two-state
bound retains the vanishing amplitude instead of differentiating the scalar
factor in isolation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialSquareRoot

open Real Asymptotics Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialSqrt (w : E) : E := Real.sqrt ‖w‖ • w

theorem sqrt_sub_mul_sqrt_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| * Real.sqrt b ≤ |a - b| := by
  have he : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    nlinarith only [Real.sq_sqrt ha, Real.sq_sqrt hb]
  rw [← he, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg a)) (abs_nonneg _)

omit [NormedSpace ℝ E] in
/-- A cutoff difference retains its vanishing input factor at zero. -/
theorem sqrt_norm_sub_mul_norm_le (w v : E) :
    |Real.sqrt ‖w‖ - Real.sqrt ‖v‖| * ‖v‖ ≤ Real.sqrt ‖v‖ * ‖w - v‖ := by
  have h := mul_le_mul_of_nonneg_right
    (sqrt_sub_mul_sqrt_le ‖w‖ ‖v‖ (norm_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg ‖v‖)
  rw [mul_assoc, Real.mul_self_sqrt (norm_nonneg v)] at h
  exact h.trans (by simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le w v) (Real.sqrt_nonneg ‖v‖))

omit [NormedSpace ℝ E] in
theorem abs_mul_sqrt_norm_sub_mul_norm_le (a b : ℝ) (w v : E) :
    |a * Real.sqrt ‖w‖ - b * Real.sqrt ‖v‖| * ‖v‖ ≤
      |a - b| * Real.sqrt ‖v‖ * ‖v‖ + |a| * Real.sqrt ‖v‖ * ‖w - v‖ := by
  have he : a * Real.sqrt ‖w‖ - b * Real.sqrt ‖v‖ =
      (a - b) * Real.sqrt ‖v‖ + a * (Real.sqrt ‖w‖ - Real.sqrt ‖v‖) := by ring
  have h := mul_le_mul_of_nonneg_right
    (abs_add_le ((a - b) * Real.sqrt ‖v‖) (a * (Real.sqrt ‖w‖ - Real.sqrt ‖v‖))) (norm_nonneg v)
  simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg ‖v‖)] at h
  have hb := mul_le_mul_of_nonneg_left (sqrt_norm_sub_mul_norm_le w v) (abs_nonneg a)
  rw [he]
  nlinarith only [h, hb]

theorem norm_radialSqrt_sub_le (w v : E) :
    ‖radialSqrt w - radialSqrt v‖ ≤ (Real.sqrt ‖w‖ + Real.sqrt ‖v‖) * ‖w - v‖ := by
  have hid : radialSqrt w - radialSqrt v =
      Real.sqrt ‖w‖ • (w - v) + (Real.sqrt ‖w‖ - Real.sqrt ‖v‖) • v := by
    unfold radialSqrt
    module
  have h := sqrt_sub_mul_sqrt_le ‖w‖ ‖v‖ (norm_nonneg _) (norm_nonneg _)
  have hm := mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg ‖v‖)
  rw [mul_assoc, Real.mul_self_sqrt (norm_nonneg v)] at hm
  have hdiff := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le w v) (Real.sqrt_nonneg ‖v‖)
  have hn := norm_add_le (Real.sqrt ‖w‖ • (w - v)) ((Real.sqrt ‖w‖ - Real.sqrt ‖v‖) • v)
  rw [hid]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ‖w‖)] at hn
  nlinarith only [hn, hm, hdiff]

theorem lipschitzOnWith_radialSqrt (R : ℝ) :
    LipschitzOnWith ⟨2 * Real.sqrt R, by positivity⟩ (radialSqrt : E → E) (Metric.closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro w hw v hv
  simp only [Metric.mem_closedBall, dist_zero_right] at hw hv
  simp only [dist_eq_norm]
  change ‖radialSqrt w - radialSqrt v‖ ≤ (2 * Real.sqrt R) * ‖w - v‖
  exact (norm_radialSqrt_sub_le w v).trans
    (mul_le_mul_of_nonneg_right (by linarith only [Real.sqrt_le_sqrt hw, Real.sqrt_le_sqrt hv])
      (norm_nonneg _))

theorem locallyLipschitz_radialSqrt : LocallyLipschitz (radialSqrt : E → E) := by
  intro w
  let R := ‖w‖ + 1
  refine ⟨⟨2 * Real.sqrt R, by positivity⟩, Metric.ball 0 R, ?_,
    (lipschitzOnWith_radialSqrt R).mono Metric.ball_subset_closedBall⟩
  apply Metric.isOpen_ball.mem_nhds
  simp only [Metric.mem_ball, dist_zero_right, R]
  linarith

theorem continuous_radialSqrt : Continuous (radialSqrt : E → E) :=
  (Real.continuous_sqrt.comp continuous_norm).smul continuous_id

theorem hasFDerivAt_radialSqrt_zero : HasFDerivAt (radialSqrt : E → E) (0 : E →L[ℝ] E) 0 := by
  have hs : (fun w : E ↦ Real.sqrt ‖w‖) =o[𝓝 0] (fun _ ↦ (1 : ℝ)) := by
    apply (isLittleO_const_iff (by norm_num : (1 : ℝ) ≠ 0)).mpr
    simpa only [Function.comp_def, norm_zero, Real.sqrt_zero] using
      (Real.continuous_sqrt.comp continuous_norm).continuousAt.tendsto (x := (0 : E))
  have h := hs.smul_isBigO (isBigO_refl (fun w : E ↦ w) (𝓝 0))
  apply HasFDerivAt.of_isLittleO
  simpa only [radialSqrt, norm_zero, Real.sqrt_zero, zero_smul, map_zero,
    zero_apply, sub_zero, one_smul] using h

theorem differentiable_radialSqrt {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    Differentiable ℝ (radialSqrt : F → F) := by
  intro w
  by_cases hw : w = 0
  · subst w
    exact hasFDerivAt_radialSqrt_zero.differentiableAt
  · exact ((differentiableAt_id.norm ℝ hw).sqrt (norm_ne_zero_iff.mpr hw)).smul differentiableAt_id

theorem norm_derivative_radialSqrt_le {w : ℝ → E} {v z : E} {t : ℝ}
    (hw : HasDerivAt w v t) (hz : HasDerivAt (fun s ↦ radialSqrt (w s)) z t) :
    ‖z‖ ≤ 2 * Real.sqrt ‖w t‖ * ‖v‖ := by
  have hlim' : Tendsto
      (fun s ↦ (Real.sqrt ‖w s‖ + Real.sqrt ‖w t‖) * ‖slope w t s‖)
      (𝓝[≠] t) (𝓝 ((Real.sqrt ‖w t‖ + Real.sqrt ‖w t‖) * ‖v‖)) :=
    (hw.continuousAt.norm.sqrt.tendsto.mono_left nhdsWithin_le_nhds |>.add tendsto_const_nhds).mul
      hw.tendsto_slope.norm
  rw [← two_mul] at hlim'
  apply le_of_tendsto_of_tendsto' hz.tendsto_slope.norm hlim'
  intro s
  simp only [slope_def_module, norm_smul]
  calc
    _ ≤ ‖(s - t)⁻¹‖ * ((Real.sqrt ‖w s‖ + Real.sqrt ‖w t‖) * ‖w s - w t‖) :=
      mul_le_mul_of_nonneg_left (norm_radialSqrt_sub_le (w s) (w t)) (norm_nonneg _)
    _ = _ := by ring

theorem norm_deriv_smul_radialSqrt_sq_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a : ℝ → ℝ} {w : ℝ → F} {ad : ℝ} {v : F} {t : ℝ}
    (ha : HasDerivAt a ad t) (hw : HasDerivAt w v t) :
    ‖deriv (fun s ↦ a s • radialSqrt (w s)) t‖ ^ 2 ≤
      2 * ad ^ 2 * ‖w t‖ ^ 3 + 8 * a t ^ 2 * ‖w t‖ * ‖v‖ ^ 2 := by
  have hr : HasDerivAt (fun s ↦ radialSqrt (w s)) (deriv (fun s ↦ radialSqrt (w s)) t) t :=
    ((differentiable_radialSqrt (w t)).comp t hw.differentiableAt).hasDerivAt
  have hb := norm_derivative_radialSqrt_le hw hr
  have hn := norm_add_le (ad • radialSqrt (w t)) (a t • deriv (fun s ↦ radialSqrt (w s)) t)
  have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg (a t))
  simp only [norm_smul, Real.norm_eq_abs, radialSqrt, abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  have hd : deriv (fun s ↦ a s • radialSqrt (w s)) t =
      ad • radialSqrt (w t) + a t • deriv (fun s ↦ radialSqrt (w s)) t := by
    exact (ha.smul hr).deriv.trans (add_comm _ _)
  rw [hd]
  have hN : ‖ad • radialSqrt (w t) + a t • deriv (fun s ↦ radialSqrt (w s)) t‖ ≤
      |ad| * (Real.sqrt ‖w t‖ * ‖w t‖) + |a t| * (2 * Real.sqrt ‖w t‖ * ‖v‖) := by
    exact hn.trans (add_le_add le_rfl hm)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hN 2
  have hcross := sq_nonneg (|ad| * (Real.sqrt ‖w t‖ * ‖w t‖) -
    |a t| * (2 * Real.sqrt ‖w t‖ * ‖v‖))
  calc
    _ ≤ 2 * (|ad| * (Real.sqrt ‖w t‖ * ‖w t‖)) ^ 2 +
        2 * (|a t| * (2 * Real.sqrt ‖w t‖ * ‖v‖)) ^ 2 := by nlinarith only [hs, hcross]
    _ = _ := by
      simp only [mul_pow, sq_abs, Real.sq_sqrt (norm_nonneg (w t))]
      ring

end Mettapedia.Analysis.RadialSquareRoot
