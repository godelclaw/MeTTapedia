import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralGapTiltWeight

/-!
# The square-root corner of a linear gap cutoff

A linear energy ramp is adequate for continuous weighted freezing, but
its square root is not Lipschitz at the cutoff boundary. Quadratic
increments give an exact witness, with no numerical approximation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GapCutoffRegularity

open SpectralGapTiltWeight
open scoped NNReal

theorem gapCutoff_quadratic_increment (gamma : ℝ) (hg : 0 < gamma)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    gapCutoff gamma (gamma + gamma * r ^ 2) = r ^ 2 := by
  have hid : (gamma + gamma * r ^ 2 - gamma) / gamma = r ^ 2 := by
    field_simp
    ring
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  simp only [gapCutoff, hid, min_eq_right hr2, max_eq_right (sq_nonneg r)]

theorem sqrt_gapCutoff_quadratic_increment (gamma : ℝ) (hg : 0 < gamma)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.sqrt (gapCutoff gamma (gamma + gamma * r ^ 2)) = r := by
  rw [gapCutoff_quadratic_increment gamma hg r hr hr1, Real.sqrt_sq hr]

theorem not_lipschitzWith_sqrt_gapCutoff (gamma : ℝ) (hg : 0 < gamma) (K : ℝ≥0) :
    ¬ LipschitzWith K (fun g : ℝ ↦ Real.sqrt (gapCutoff gamma g)) := by
  intro h
  let d : ℝ := 2 * (gamma * (K : ℝ) + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : 1 ≤ d := by
    dsimp [d]
    have hK := mul_nonneg hg.le K.coe_nonneg
    linarith
  let r : ℝ := 1 / d
  have hr : 0 < r := one_div_pos.mpr hd
  have hr1 : r ≤ 1 := (div_le_one hd).mpr hd1
  have hrd : r * d = 1 := one_div_mul_cancel (ne_of_gt hd)
  have hb := h.dist_le_mul (gamma + gamma * r ^ 2) gamma
  rw [sqrt_gapCutoff_quadratic_increment gamma hg r hr.le hr1,
    gapCutoff_eq_zero gamma gamma hg le_rfl, Real.sqrt_zero,
    Real.dist_eq, sub_zero, abs_of_pos hr, Real.dist_eq,
    add_sub_cancel_left, abs_of_nonneg (by positivity : 0 ≤ gamma * r ^ 2)] at hb
  have hbad : 1 ≤ (K : ℝ) * gamma * r :=
    (mul_le_mul_iff_left₀ hr).mp (by nlinarith only [hb])
  have hdK : d ≤ (K : ℝ) * gamma := by
    calc
      d = 1 * d := by ring
      _ ≤ ((K : ℝ) * gamma * r) * d := mul_le_mul_of_nonneg_right hbad hd.le
      _ = (K : ℝ) * gamma := by rw [mul_assoc, hrd, mul_one]
  dsimp [d] at hdK
  have hK := K.coe_nonneg
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.GapCutoffRegularity
