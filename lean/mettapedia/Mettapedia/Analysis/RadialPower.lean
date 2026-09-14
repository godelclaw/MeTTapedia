import Mettapedia.Analysis.LocallyLipschitz
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Product-weighted increments of radial powers

The map `x ↦ ‖x‖ ^ n • x` controls the product-weighted increment with
constant one. This retains both endpoint weights and is valid at zero.
The cubic case includes a local Lipschitz and derivative estimate for use
with the dissipation associated with the eighth power of a vector norm.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialPower

open Real Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialPower (n : ℕ) (x : E) : E := ‖x‖ ^ n • x

theorem continuous_radialPower (n : ℕ) : Continuous (radialPower n : E → E) :=
  (continuous_norm.pow n).smul continuous_id

theorem norm_radialPower (n : ℕ) (a : E) : ‖radialPower n a‖ = ‖a‖ ^ (n + 1) := by
  simp only [radialPower, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) _), pow_succ]

theorem radial_gap_mul_norm_le (n : ℕ) (a b : E) (hab : ‖b‖ ≤ ‖a‖) :
    (‖a‖ ^ n - ‖b‖ ^ n) * ‖b‖ ≤ ‖radialPower n a - radialPower n b‖ := by
  calc
    _ ≤ ‖a‖ ^ (n + 1) - ‖b‖ ^ (n + 1) := by
      simp only [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left hab (pow_nonneg (norm_nonneg a) n)]
    _ ≤ _ := by simpa only [norm_radialPower] using
      norm_sub_norm_le (radialPower n a) (radialPower n b)

theorem norm_pow_mul_norm_sub_le_of_norm_le (n : ℕ) (a b : E) (hab : ‖b‖ ≤ ‖a‖) :
    ‖a‖ ^ n * ‖a - b‖ ≤ 2 * ‖radialPower n a - radialPower n b‖ := by
  have hp : 0 ≤ ‖a‖ ^ n - ‖b‖ ^ n :=
    sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg b) hab n)
  have he : ‖a‖ ^ n • (a - b) =
      radialPower n a - radialPower n b - (‖a‖ ^ n - ‖b‖ ^ n) • b := by
    unfold radialPower
    module
  have hn := norm_sub_le (radialPower n a - radialPower n b)
    ((‖a‖ ^ n - ‖b‖ ^ n) • b)
  rw [← he] at hn
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp,
    abs_of_nonneg (pow_nonneg (norm_nonneg a) n)] at hn
  linarith only [hn, radial_gap_mul_norm_le n a b hab]

/-- A max-weight increment is controlled uniformly, including opposite endpoints. -/
theorem max_norm_pow_mul_norm_sub_le (n : ℕ) (a b : E) :
    max ‖a‖ ‖b‖ ^ n * ‖a - b‖ ≤ 2 * ‖radialPower n a - radialPower n b‖ := by
  rcases le_total ‖b‖ ‖a‖ with hab | hab
  · simpa only [max_eq_left hab] using norm_pow_mul_norm_sub_le_of_norm_le n a b hab
  · simpa only [max_eq_right hab, norm_sub_rev] using
      norm_pow_mul_norm_sub_le_of_norm_le n b a hab

theorem norm_radialPower_double_sub_le_of_norm_le (n : ℕ) (a b : E) (hab : ‖b‖ ≤ ‖a‖) :
    ‖radialPower (2 * n) a - radialPower (2 * n) b‖ ≤
      2 * ‖a‖ ^ n * ‖radialPower n a - radialPower n b‖ := by
  have hp : 0 ≤ ‖a‖ ^ n - ‖b‖ ^ n :=
    sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg b) hab n)
  have he : radialPower (2 * n) a - radialPower (2 * n) b =
      ‖a‖ ^ n • (radialPower n a - radialPower n b) +
        (‖a‖ ^ n - ‖b‖ ^ n) • radialPower n b := by
    simp only [radialPower, two_mul, pow_add, mul_smul]
    module
  rw [he]
  have hn := norm_add_le (‖a‖ ^ n • (radialPower n a - radialPower n b))
    ((‖a‖ ^ n - ‖b‖ ^ n) • radialPower n b)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp,
    abs_of_nonneg (pow_nonneg (norm_nonneg a) n), norm_radialPower, pow_succ] at hn
  have h := mul_le_mul (pow_le_pow_left₀ (norm_nonneg b) hab n)
    (radial_gap_mul_norm_le n a b hab) (mul_nonneg hp (norm_nonneg b))
    (pow_nonneg (norm_nonneg a) n)
  nlinarith only [hn, h]

theorem norm_radialPower_double_sub_le (n : ℕ) (a b : E) :
    ‖radialPower (2 * n) a - radialPower (2 * n) b‖ ≤
      2 * max ‖a‖ ‖b‖ ^ n * ‖radialPower n a - radialPower n b‖ := by
  rcases le_total ‖b‖ ‖a‖ with hab | hab
  · simpa only [max_eq_left hab] using norm_radialPower_double_sub_le_of_norm_le n a b hab
  · simpa only [max_eq_right hab, norm_sub_rev] using
      norm_radialPower_double_sub_le_of_norm_le n b a hab

/-- The exact defect is a product of two equally ordered radial differences. -/
theorem norm_sub_sq_identity (n : ℕ) (a b : E) :
    ‖radialPower n a - radialPower n b‖ ^ 2 -
      ‖a‖ ^ n * ‖b‖ ^ n * ‖a - b‖ ^ 2 =
    (‖a‖ ^ n - ‖b‖ ^ n) * (‖a‖ ^ (n + 2) - ‖b‖ ^ (n + 2)) := by
  simp only [radialPower, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) _), real_inner_smul_left,
    real_inner_smul_right, pow_add]
  ring

theorem product_weighted_norm_sub_sq_le (n : ℕ) (a b : E) :
    ‖a‖ ^ n * ‖b‖ ^ n * ‖a - b‖ ^ 2 ≤
      ‖radialPower n a - radialPower n b‖ ^ 2 := by
  have h : 0 ≤ (‖a‖ ^ n - ‖b‖ ^ n) * (‖a‖ ^ (n + 2) - ‖b‖ ^ (n + 2)) := by
    rcases le_total ‖b‖ ‖a‖ with hab | hab
    · exact mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hab n))
        (sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hab (n + 2)))
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (pow_le_pow_left₀ (norm_nonneg _) hab n))
        (sub_nonpos.mpr (pow_le_pow_left₀ (norm_nonneg _) hab (n + 2)))
  linarith only [norm_sub_sq_identity n a b, h]

theorem norm_radialPower_three_sub_le (a b : E) :
    ‖radialPower 3 a - radialPower 3 b‖ ≤
      (‖a‖ ^ 3 + ‖b‖ * (‖a‖ ^ 2 + ‖a‖ * ‖b‖ + ‖b‖ ^ 2)) * ‖a - b‖ := by
  have he : radialPower 3 a - radialPower 3 b =
      ‖a‖ ^ 3 • (a - b) + (‖a‖ ^ 3 - ‖b‖ ^ 3) • b := by
    unfold radialPower
    module
  have hp : |‖a‖ ^ 3 - ‖b‖ ^ 3| ≤
      ‖a - b‖ * (‖a‖ ^ 2 + ‖a‖ * ‖b‖ + ‖b‖ ^ 2) := by
    have hfac : ‖a‖ ^ 3 - ‖b‖ ^ 3 =
        (‖a‖ - ‖b‖) * (‖a‖ ^ 2 + ‖a‖ * ‖b‖ + ‖b‖ ^ 2) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by positivity :
      0 ≤ ‖a‖ ^ 2 + ‖a‖ * ‖b‖ + ‖b‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le a b) (by positivity)
  rw [he]
  have hn := norm_add_le (‖a‖ ^ 3 • (a - b)) ((‖a‖ ^ 3 - ‖b‖ ^ 3) • b)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖a‖ ^ 3)] at hn
  have hm := mul_le_mul_of_nonneg_right hp (norm_nonneg b)
  nlinarith only [hn, hm]

theorem lipschitzOnWith_radialPower_three (R : ℝ) (hR : 0 ≤ R) :
    LipschitzOnWith ⟨4 * R ^ 3, by positivity⟩ (radialPower 3 : E → E)
      (Metric.closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  simp only [Metric.mem_closedBall, dist_zero_right] at ha hb
  simp only [dist_eq_norm]
  change _ ≤ 4 * R ^ 3 * ‖a - b‖
  apply (norm_radialPower_three_sub_le a b).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ R ^ 3 + R * (R ^ 2 + R * R + R ^ 2) := by gcongr
    _ = _ := by ring

theorem locallyLipschitz_radialPower_three : LocallyLipschitz (radialPower 3 : E → E) := by
  intro x
  refine ⟨⟨4 * (‖x‖ + 1) ^ 3, by positivity⟩, Metric.ball 0 (‖x‖ + 1), ?_,
    (lipschitzOnWith_radialPower_three (‖x‖ + 1) (by positivity)).mono Metric.ball_subset_closedBall⟩
  exact Metric.isOpen_ball.mem_nhds (by simp)

theorem hasFDerivAt_radialPower_three_zero :
    HasFDerivAt (radialPower 3 : E → E) (0 : E →L[ℝ] E) 0 := by
  have hs : (fun x : E ↦ ‖x‖ ^ 3) =o[𝓝 0] (fun _ ↦ (1 : ℝ)) := by
    apply (isLittleO_const_iff (by norm_num : (1 : ℝ) ≠ 0)).mpr
    have hc : Continuous (fun x : E ↦ ‖x‖ ^ 3) := continuous_norm.pow 3
    simpa using hc.continuousAt.tendsto (x := (0 : E))
  have h := hs.smul_isBigO (isBigO_refl (fun x : E ↦ x) (𝓝 0))
  apply HasFDerivAt.of_isLittleO
  simpa only [radialPower, norm_zero, zero_pow (by omega : 3 ≠ 0), zero_smul,
    map_zero, zero_apply, sub_zero, one_smul] using h

theorem differentiable_radialPower_three : Differentiable ℝ (radialPower 3 : E → E) := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact hasFDerivAt_radialPower_three_zero.differentiableAt
  · exact ((differentiableAt_id.norm ℝ hx).pow 3).smul differentiableAt_id

theorem norm_derivative_radialPower_three_le {w : ℝ → E} {v z : E} {t : ℝ}
    (hw : HasDerivAt w v t) (hz : HasDerivAt (fun s ↦ radialPower 3 (w s)) z t) :
    ‖z‖ ≤ 4 * ‖w t‖ ^ 3 * ‖v‖ := by
  have hc : Tendsto (fun s ↦ ‖w s‖) (𝓝[≠] t) (𝓝 ‖w t‖) :=
    hw.continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := ((hc.pow 3).add ((tendsto_const_nhds (x := ‖w t‖)).mul
    (((hc.pow 2).add (hc.mul (tendsto_const_nhds (x := ‖w t‖)))).add
      (tendsto_const_nhds (x := ‖w t‖ ^ 2))))).mul hw.tendsto_slope.norm
  have hlim' : Tendsto (fun s ↦
      (‖w s‖ ^ 3 + ‖w t‖ * (‖w s‖ ^ 2 + ‖w s‖ * ‖w t‖ + ‖w t‖ ^ 2)) * ‖slope w t s‖)
      (𝓝[≠] t) (𝓝 (4 * ‖w t‖ ^ 3 * ‖v‖)) := by
    convert hlim using 1
    congr 1
    ring
  apply le_of_tendsto_of_tendsto' hz.tendsto_slope.norm hlim'
  intro s
  simp only [slope_def_module, norm_smul]
  calc
    _ ≤ ‖(s - t)⁻¹‖ * ((‖w s‖ ^ 3 + ‖w t‖ *
        (‖w s‖ ^ 2 + ‖w s‖ * ‖w t‖ + ‖w t‖ ^ 2)) * ‖w s - w t‖) :=
      mul_le_mul_of_nonneg_left (norm_radialPower_three_sub_le (w s) (w t)) (norm_nonneg _)
    _ = _ := by ring

end Mettapedia.Analysis.RadialPower
