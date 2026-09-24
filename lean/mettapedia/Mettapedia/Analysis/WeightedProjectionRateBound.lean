import Mettapedia.Analysis.WeightedProjectionCurvatureBound
import Mettapedia.Analysis.WeightedProjectionVariation

/-!
# Uniform first-variation bounds for weighted projection energy

The constants are independent of positive regularization. No inverse
vorticity magnitude or derivative of the minimizing coefficient occurs.
The bound applies at zeros of the first vector and to arbitrary first
variations. It is a magnitude bound, not a sign or dynamical estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedProjectionRateBound

open scoped RealInnerProductSpace
open RegularizedProjection WeightedProjectionCurvatureBound WeightedProjectionVariation
open WeightedProjectionParabolic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_residual_le (δ : ℝ) (hδ : 0 < δ) (a b : E) :
    ‖RegularizedProjection.residual δ a b‖ ≤ ‖b‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (norm_residual_sq_le δ hδ a b)

theorem abs_coefficient_mul_norm_le (δ : ℝ) (hδ : 0 < δ) (a b : E) :
    |coefficient δ a b| * ‖a‖ ≤ ‖b‖ := by
  apply (sq_le_sq₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  simpa only [mul_pow, sq_abs] using coefficient_sq_mul_norm_sq_le δ hδ a b

theorem norm_firstGradient_le (δ : ℝ) (hδ : 0 < δ) (a b : E) :
    ‖firstGradient δ a b‖ ≤ 8 * ‖a‖ ^ 5 * ‖b‖ ^ 2 := by
  have hE := energy_nonneg δ hδ.le a b
  calc
    _ ≤ ‖(6 * ‖a‖ ^ 4 * energy δ a b) • a‖ +
        ‖(2 * ‖a‖ ^ 6 * coefficient δ a b) • RegularizedProjection.residual δ a b‖ :=
      norm_sub_le _ _
    _ = 6 * ‖a‖ ^ 5 * energy δ a b +
        2 * ‖a‖ ^ 5 * (|coefficient δ a b| * ‖a‖) * ‖RegularizedProjection.residual δ a b‖ := by
      rw [norm_smul, norm_smul]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (by positivity : 0 ≤ ‖a‖ ^ 4),
        abs_of_nonneg (by positivity : 0 ≤ ‖a‖ ^ 6), abs_of_nonneg hE]
      ring
    _ ≤ 6 * ‖a‖ ^ 5 * ‖b‖ ^ 2 + 2 * ‖a‖ ^ 5 * ‖b‖ * ‖b‖ := by
      gcongr
      · exact energy_le_norm_sq δ hδ a b
      · exact abs_coefficient_mul_norm_le δ hδ a b
      · exact norm_residual_le δ hδ a b
    _ = _ := by ring

theorem norm_secondGradient_le (δ : ℝ) (hδ : 0 < δ) (a b : E) :
    ‖secondGradient δ a b‖ ≤ 2 * ‖a‖ ^ 6 * ‖b‖ := by
  rw [secondGradient, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * ‖a‖ ^ 6)]
  exact mul_le_mul_of_nonneg_left (norm_residual_le δ hδ a b) (by positivity)

theorem abs_weightedRate_le (δ : ℝ) (hδ : 0 < δ) (a b v z : E) :
    |weightedRate δ a b v z| ≤ 8 * ‖a‖ ^ 5 * ‖b‖ ^ 2 * ‖v‖ + 2 * ‖a‖ ^ 6 * ‖b‖ * ‖z‖ := by
  rw [weightedRate_eq]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_firstGradient_le δ hδ a b) (norm_nonneg _))
  · exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_secondGradient_le δ hδ a b) (norm_nonneg _))

/-- A strain-driven variation with a separately retained derivative source. -/
theorem abs_strain_weightedRate_le (δ : ℝ) (hδ : 0 < δ) (a b : E)
    (S : E →L[ℝ] E) (f : E) :
    |weightedRate δ a b (S a) (-S b + f)| ≤
      10 * ‖a‖ ^ 6 * ‖S‖ * ‖b‖ ^ 2 + 2 * ‖a‖ ^ 6 * ‖b‖ * ‖f‖ := by
  have hz : ‖-S b + f‖ ≤ ‖S‖ * ‖b‖ + ‖f‖ :=
    (norm_add_le _ _).trans (by rw [norm_neg]; exact add_le_add (S.le_opNorm b) le_rfl)
  apply (abs_weightedRate_le δ hδ a b (S a) (-S b + f)).trans
  calc
    _ ≤ 8 * ‖a‖ ^ 5 * ‖b‖ ^ 2 * (‖S‖ * ‖a‖) +
        2 * ‖a‖ ^ 6 * ‖b‖ * (‖S‖ * ‖b‖ + ‖f‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (S.le_opNorm a) (by positivity))
        (mul_le_mul_of_nonneg_left hz (by positivity))
    _ = _ := by ring

end Mettapedia.Analysis.WeightedProjectionRateBound
