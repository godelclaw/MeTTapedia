import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeTwoShearDiffusion

/-!
# Finite-time comparison across two-shear spectral crossings

The comparison is polynomial on the three possible amplitude-ordering
regions, including their boundaries. It therefore does not differentiate
the absolute value at an eigenvalue collision or exclude crossing points.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeTwoShearFiniteTime

open PancakeTwoShearDiffusion

theorem shearDefect_scale (c f g : ℝ) (hc : 0 ≤ c) :
    shearDefect (c * f) (c * g) = c ^ 3 * shearDefect f g := by
  unfold shearDefect
  rw [← mul_sub, ← mul_add, abs_mul, abs_of_nonneg hc]
  ring

theorem pairedDefect_scale (c f g : ℝ) (hc : 0 ≤ c) :
    pairedDefect (c * f) (c * g) = c ^ 3 * pairedDefect f g := by
  unfold pairedDefect
  rw [show -(c * f) = c * (-f) by ring, shearDefect_scale c f g hc,
    shearDefect_scale c (-f) g hc]
  ring

theorem pairedDefect_neg_left (f g : ℝ) : pairedDefect (-f) g = pairedDefect f g := by
  unfold pairedDefect
  rw [neg_neg]
  ring

theorem shearDefect_neg_neg (f g : ℝ) : shearDefect (-f) (-g) = shearDefect f g := by
  unfold shearDefect
  rw [show -f - -g = -(f - g) by ring, abs_neg,
    show -f + -g = -(f + g) by ring, neg_sq]

theorem pairedDefect_neg_right (f g : ℝ) : pairedDefect f (-g) = pairedDefect f g := by
  unfold pairedDefect
  rw [show shearDefect f (-g) = shearDefect (-f) g from by
    simpa only [neg_neg] using shearDefect_neg_neg (-f) g,
    shearDefect_neg_neg]
  ring

theorem pairedDefect_abs (f g : ℝ) : pairedDefect |f| |g| = pairedDefect f g := by
  rcases le_total 0 f with hf | hf <;> rcases le_total 0 g with hg | hg
  · rw [abs_of_nonneg hf, abs_of_nonneg hg]
  · rw [abs_of_nonneg hf, abs_of_nonpos hg, pairedDefect_neg_right]
  · rw [abs_of_nonpos hf, abs_of_nonneg hg, pairedDefect_neg_left]
  · rw [abs_of_nonpos hf, abs_of_nonpos hg, pairedDefect_neg_left, pairedDefect_neg_right]

/-- Damping the fast amplitude can increase the defect. The lower bound
holds even if the two amplitudes cross during the damping. -/
theorem pairedDefect_damping_lower (alpha f g : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    (1 - alpha ^ 2) * (4 * g - 8 * f) * f ^ 2 ≤
      pairedDefect (alpha * f) g - pairedDefect f g := by
  have haf : alpha * f ≤ f := by nlinarith
  have ha2 : 0 ≤ 1 - alpha ^ 2 := by nlinarith
  apply sub_nonneg.mp
  rcases le_total f g with hfg | hgf
  · rw [pairedDefect_small (alpha * f) g (mul_nonneg ha hf) (haf.trans hfg),
      pairedDefect_small f g hf hfg]
    have hid : 4 * g * (g ^ 2 - (alpha * f) ^ 2) - 4 * g * (g ^ 2 - f ^ 2) -
        (1 - alpha ^ 2) * (4 * g - 8 * f) * f ^ 2 = 8 * (1 - alpha ^ 2) * f ^ 3 := by ring
    rw [hid]
    positivity
  · rcases le_total (alpha * f) g with hag | hga
    · rw [pairedDefect_small (alpha * f) g (mul_nonneg ha hf) hag,
        pairedDefect_large f g hg hgf]
      have hid : 4 * g * (g ^ 2 - (alpha * f) ^ 2) - 4 * f * (f ^ 2 - g ^ 2) -
          (1 - alpha ^ 2) * (4 * g - 8 * f) * f ^ 2 =
            4 * ((f + g) * (f - g) ^ 2 + 2 * f * (g ^ 2 - (alpha * f) ^ 2)) := by ring
      rw [hid]
      have hsq : 0 ≤ g ^ 2 - (alpha * f) ^ 2 := by nlinarith [mul_nonneg ha hf]
      positivity
    · rw [pairedDefect_large (alpha * f) g hg hga, pairedDefect_large f g hg hgf]
      have hid : 4 * (alpha * f) * ((alpha * f) ^ 2 - g ^ 2) - 4 * f * (f ^ 2 - g ^ 2) -
          (1 - alpha ^ 2) * (4 * g - 8 * f) * f ^ 2 =
            4 * f * (1 - alpha) *
              ((alpha * f - g) * (f - g) + (1 - alpha ^ 2) * f ^ 2) := by ring
      rw [hid]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hf) (sub_nonneg.mpr ha1))
        (add_nonneg (mul_nonneg (sub_nonneg.mpr hga) (sub_nonneg.mpr hgf))
          (mul_nonneg ha2 (sq_nonneg f)))

theorem pairedDefect_damping_lower_bounded (alpha f g eps : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hf : 0 ≤ f) (hg : 0 ≤ g) (hfe : f ≤ eps) :
    (1 - alpha ^ 2) * (4 * g - 8 * eps) * f ^ 2 ≤
      pairedDefect (alpha * f) g - pairedDefect f g := by
  apply le_trans ?_ (pairedDefect_damping_lower alpha f g ha ha1 hf hg)
  have ha2 : 0 ≤ 1 - alpha ^ 2 := by nlinarith
  gcongr

end Mettapedia.FluidDynamics.NavierStokes.PancakeTwoShearFiniteTime
