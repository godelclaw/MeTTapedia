import Mettapedia.Analysis.ODE.QuadraticFormBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Dissipative comparison with an almost-everywhere differential equation

This extends the dissipative comparison interface in `QuadraticFormBound`
to absolutely continuous paths and integrable forcing. In particular, the
equation need not hold at eigenvalue collisions. The norm derivative away
from zero is reused from the OpenAI-derived quadratic-form estimates; at
zero, the norm has a minimum. Absolute continuity rules out singular changes
invisible to an almost-everywhere derivative.
-/

namespace Mettapedia.Analysis.ODE

open Set Filter MeasureTheory
open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]

theorem absolutelyContinuousOnInterval_norm {u : ℝ → H} {a b : ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ ‖u t‖) a b := by
  apply squeeze_zero (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)) ?_ hu
  intro I
  exact Finset.sum_le_sum (fun _ _ ↦ by simpa only [dist_eq_norm] using dist_norm_norm_le _ _)

variable [InnerProductSpace ℝ H]

/-- A dissipative linear equation cannot increase the norm by more than
the integrated forcing. Absolute continuity and an almost-everywhere
equation suffice; continuity of the forcing is not required. -/
theorem norm_le_initial_add_integral_of_ae_dissipative {u f : ℝ → H} {a b : ℝ}
    (A : ℝ → H →L[ℝ] H) (hab : a ≤ b)
    (hu : AbsolutelyContinuousOnInterval u a b) (hf : IntervalIntegrable f volume a b)
    (hode : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt u (A t (u t) + f t) t)
    (hA : ∀ t ∈ uIcc a b, ∀ x : H, ⟪x, A t x⟫ ≤ 0) :
    ‖u b‖ ≤ ‖u a‖ + ∫ t in a..b, ‖f t‖ := by
  have hn := absolutelyContinuousOnInterval_norm hu
  have hd : ∀ᵐ t, t ∈ uIcc a b → deriv (fun τ ↦ ‖u τ‖) t ≤ ‖f t‖ := by
    filter_upwards [hode] with t ht hmem
    by_cases hz : u t = 0
    · have hmin : IsLocalMin (fun τ ↦ ‖u τ‖) t :=
        Filter.Eventually.of_forall (fun τ ↦ by simp only [hz, norm_zero]; exact norm_nonneg _)
      rw [hmin.deriv_eq_zero]
      exact norm_nonneg _
    · have hd : HasDerivAt (fun τ ↦ ‖u τ‖) (⟪u t, A t (u t) + f t⟫ / ‖u t‖) t :=
        hasDerivWithinAt_univ.mp
          (hasDerivWithinAt_norm_of_ne_zero ((ht hmem).hasDerivWithinAt (s := univ)) hz)
      rw [hd.deriv]
      apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
      rw [inner_add_right]
      nlinarith [hA t hmem (u t), real_inner_le_norm (u t) (f t)]
  have hi := intervalIntegral.integral_mono_ae_restrict hab hn.intervalIntegrable_deriv hf.norm
    (by
      change ∀ᵐ t ∂volume.restrict (Icc a b), deriv (fun τ ↦ ‖u τ‖) t ≤ ‖f t‖
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hd] with t ht hmem
      exact ht (by simpa only [uIcc_of_le hab] using hmem))
  rw [hn.integral_deriv_eq_sub] at hi
  linarith

end Mettapedia.Analysis.ODE
