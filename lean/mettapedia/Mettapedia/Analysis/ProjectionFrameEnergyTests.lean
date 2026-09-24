import Mettapedia.Analysis.QuadraticProjectionFrame
import Mettapedia.Analysis.WeightedMixedDerivative

/-!
# Regression tests for vector transfer and mixed-derivative payment

Coordinate projections alone do not dominate the product of vector norms.
The mixed-derivative estimate is integrated, not an inequality for unrelated
pointwise jets. Neither counterexample is asserted to be an NS solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.ProjectionFrameEnergyTests

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def axis (i : Fin 3) : R3 := EuclideanSpace.single i 1

theorem norm_axis (i : Fin 3) : ‖axis i‖ = 1 := by simp [axis, PiLp.norm_single]

theorem coordinate_product_vanishes :
    (∑ j : Fin 3, (axis 0 j) ^ 6 * (axis 1 j) ^ 2) = 0 := by
  norm_num [axis, PiLp.single_apply, Fin.sum_univ_three]

theorem no_coordinate_lower_bound (c : ℝ) (hc : 0 < c) :
    ¬ ∀ a z : R3, c * ‖a‖ ^ 6 * ‖z‖ ^ 2 ≤ ∑ j : Fin 3, (a j) ^ 6 * (z j) ^ 2 := by
  intro h
  have he := h (axis 0) (axis 1)
  rw [norm_axis, norm_axis, coordinate_product_vanishes] at he
  norm_num at he
  exact (not_le_of_gt hc) he

theorem frame_sees_orthogonal_axes : QuadraticProjectionFrame.moment 3 1 (axis 0) (axis 1) > 0 := by
  apply QuadraticProjectionFrame.moment_pos
  · exact norm_ne_zero_iff.mp (by rw [norm_axis]; norm_num)
  · exact norm_ne_zero_iff.mp (by rw [norm_axis]; norm_num)

theorem no_pointwise_mixed_bound :
    ¬ ∀ a v w b c h : ℝ,
      ‖a‖ ^ 6 * ‖h‖ ^ 2 ≤ ‖a‖ ^ 6 * ‖b‖ ^ 2 + 7 * ‖a‖ ^ 6 * ‖c‖ ^ 2 +
        24 * ‖a‖ ^ 4 * ‖v‖ ^ 4 + 18 * ‖a‖ ^ 4 * ‖w‖ ^ 4 := by
  intro h
  have he := h 1 0 0 0 0 1
  norm_num at he

end Mettapedia.Analysis.ProjectionFrameEnergyTests
