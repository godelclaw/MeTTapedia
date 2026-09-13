import Mettapedia.Analysis.WeightedProjectionParabolic

/-!
# An upper bound for weighted projection curvature

The bound is uniform in the positive regularization parameter. It uses
only the magnitudes of the two fields and their first variations, with
no derivative of the minimizing coefficient. This is the sign needed
when the projection energy is subtracted from another energy.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedProjectionCurvatureBound

open scoped RealInnerProductSpace
open RegularizedProjection RegularizedProjectionParabolic WeightedProjectionParabolic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_residual_sq_le (δ : ℝ) (hδ : 0 < δ) (a b : E) :
    ‖RegularizedProjection.residual δ a b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
  have h := energy_le_norm_sq δ hδ a b
  have hn : 0 ≤ δ * coefficient δ a b ^ 2 := by positivity
  unfold energy at h
  linarith only [h, hn]

theorem coefficient_sq_mul_norm_sq_le (δ : ℝ) (hδ : 0 < δ) (a b : E) :
    coefficient δ a b ^ 2 * ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by
  have h := objective_eq_energy_add_sq δ hδ a b 0
  simp only [zero_smul, sub_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero,
    zero_sub, neg_sq] at h
  have hJ := energy_nonneg δ hδ.le a b
  have hn : 0 ≤ δ * coefficient δ a b ^ 2 := by positivity
  nlinarith only [h, hJ, hn]

theorem norm_sub_sq_le_twice (v z : E) :
    ‖v - z‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
  have h := sq_nonneg ‖v + z‖
  rw [norm_add_sq_real] at h
  rw [norm_sub_sq_real]
  linarith only [h]

theorem weighted_relativeRate_sq_le (δ : ℝ) (hδ : 0 < δ) (a b v z : E) :
    ‖a‖ ^ 6 * ‖z - coefficient δ a b • v‖ ^ 2 ≤
      2 * ‖a‖ ^ 6 * ‖z‖ ^ 2 + 2 * ‖a‖ ^ 4 * ‖b‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := norm_sub_sq_le_twice z (coefficient δ a b • v)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  have h1 := mul_le_mul_of_nonneg_left h (show 0 ≤ ‖a‖ ^ 6 by positivity)
  have h2 := mul_le_mul_of_nonneg_left (coefficient_sq_mul_norm_sq_le δ hδ a b)
    (show 0 ≤ 2 * ‖a‖ ^ 4 * ‖v‖ ^ 2 by positivity)
  nlinarith only [h1, h2]

/-- No inverse regularization, spatial supremum, or coefficient-rate term
is used. The numerical constants are not asserted optimal. -/
theorem weightedCurvature_le (δ : ℝ) (hδ : 0 < δ) (a b v z : E) :
    weightedCurvature δ a b v z ≤
      70 * ‖a‖ ^ 4 * ‖b‖ ^ 2 * ‖v‖ ^ 2 + 28 * ‖a‖ ^ 6 * ‖z‖ ^ 2 := by
  let r := RegularizedProjection.residual δ a b
  let y := z - coefficient δ a b • v
  have hcs : ⟪a, v⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖v‖ ^ 2 := by
    simpa only [sq, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le a v
  have hJ := energy_nonneg δ hδ.le a b
  have hfirst1 := mul_le_mul_of_nonneg_left hcs
    (show 0 ≤ 24 * ‖a‖ ^ 2 * energy δ a b by positivity)
  have hfirst2 := mul_le_mul_of_nonneg_left (energy_le_norm_sq δ hδ a b)
    (show 0 ≤ 30 * ‖a‖ ^ 4 * ‖v‖ ^ 2 by positivity)
  have hfirst :
      (24 * ‖a‖ ^ 2 * ⟪a, v⟫ ^ 2 + 6 * ‖a‖ ^ 4 * ‖v‖ ^ 2) * energy δ a b ≤
        30 * ‖a‖ ^ 4 * ‖b‖ ^ 2 * ‖v‖ ^ 2 := by
    nlinarith only [hfirst1, hfirst2]
  have hs := sq_nonneg ‖(‖a‖ * ⟪a, v⟫) • r - ‖a‖ ^ 3 • y‖
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right] at hs
  have hm1 := mul_le_mul_of_nonneg_left hcs
    (show 0 ≤ ‖a‖ ^ 2 * ‖r‖ ^ 2 by positivity)
  have hm2 := mul_le_mul_of_nonneg_left (norm_residual_sq_le δ hδ a b)
    (show 0 ≤ ‖a‖ ^ 4 * ‖v‖ ^ 2 by positivity)
  have hmixed : 24 * ‖a‖ ^ 4 * ⟪a, v⟫ * ⟪r, y⟫ ≤
      12 * ‖a‖ ^ 4 * ‖b‖ ^ 2 * ‖v‖ ^ 2 + 12 * ‖a‖ ^ 6 * ‖y‖ ^ 2 := by
    change ‖a‖ ^ 4 * ‖v‖ ^ 2 * ‖r‖ ^ 2 ≤ _ at hm2
    nlinarith only [hs, hm1, hm2]
  have hnegative : 0 ≤
      2 * ‖a‖ ^ 6 * (δ + ‖a‖ ^ 2) * coefficientRate δ a b v z ^ 2 := by positivity
  have hy := weighted_relativeRate_sq_le δ hδ a b v z
  change ‖a‖ ^ 6 * ‖y‖ ^ 2 ≤ _ at hy
  unfold weightedCurvature energyRate energyCurvature
  change _ + 12 * ‖a‖ ^ 4 * ⟪a, v⟫ * (2 * ⟪r, y⟫) +
    ‖a‖ ^ 6 * (2 * ‖y‖ ^ 2 - 2 * (δ + ‖a‖ ^ 2) * coefficientRate δ a b v z ^ 2) ≤ _
  nlinarith only [hfirst, hmixed, hnegative, hy]

end Mettapedia.Analysis.WeightedProjectionCurvatureBound
