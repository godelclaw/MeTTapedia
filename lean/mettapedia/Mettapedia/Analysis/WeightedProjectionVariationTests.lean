import Mettapedia.Analysis.WeightedProjectionVariation

/-!
# Regression identities for signed projection source work

Simultaneous radial forcing of the two inputs need not have zero work.
These tests concern the first variation, not an unforced NS solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedProjectionVariationTests

open scoped RealInnerProductSpace
open WeightedProjectionParabolic WeightedProjectionVariation RegularizedProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_rate (δ : ℝ) (a b : E) :
    weightedRate δ a b a b = 8 * weightedEnergy δ a b -
      2 * δ * ‖a‖ ^ 6 * coefficient δ a b ^ 2 := by
  simp only [weightedRate, RegularizedProjectionParabolic.energyRate,
    weightedEnergy, energy, RegularizedProjection.residual, real_inner_self_eq_norm_sq]
  ring

theorem negative_radial_rate (δ : ℝ) (a b : E) :
    weightedRate δ a b (-a) (-b) = -weightedRate δ a b a b := by
  simpa only [neg_one_smul, neg_one_mul] using weightedRate_smul δ a b a b (-1)

theorem zero_field_rate (δ : ℝ) (b v z : E) : weightedRate δ (0 : E) b v z = 0 := by
  simp [weightedRate]

theorem radial_rate_ge (δ : ℝ) (a b : E) :
    6 * weightedEnergy δ a b ≤ weightedRate δ a b a b := by
  rw [radial_rate]
  unfold weightedEnergy energy
  nlinarith only [mul_nonneg (pow_nonneg (norm_nonneg a) 6)
    (sq_nonneg ‖RegularizedProjection.residual δ a b‖)]

theorem radial_rate_nonneg (δ : ℝ) (hδ : 0 ≤ δ) (a b : E) :
    0 ≤ weightedRate δ a b a b := by
  have hW : 0 ≤ weightedEnergy δ a b := mul_nonneg (by positivity) (energy_nonneg δ hδ a b)
  linarith only [radial_rate_ge δ a b, hW]

end Mettapedia.Analysis.WeightedProjectionVariationTests
