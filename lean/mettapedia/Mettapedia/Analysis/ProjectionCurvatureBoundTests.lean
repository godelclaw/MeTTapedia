import Mettapedia.Analysis.WeightedProjectionCurvatureBound
import Mettapedia.Analysis.UnitTorusQuarticSecondEnergy
import Mettapedia.Analysis.WeightedProjectionParabolicTests

/-!
# Sign and pointwise-coercivity regression tests

Positive and negative weighted curvatures are possible. The integrated
quartic estimate must not be replaced by a pointwise Hessian estimate:
the displayed real jets make the fourth-power second derivative vanish
while the weighted second-derivative square is strictly positive.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.ProjectionCurvatureBoundTests

open WeightedProjectionParabolic RegularizedProjectionParabolic RegularizedProjection
open UnitTorusQuarticSecondEnergy

theorem positive_weightedCurvature : weightedCurvature 1 (1 : ℝ) 0 0 1 = 1 := by
  norm_num [weightedCurvature, energy, energyRate, energyCurvature, coefficientRate,
    coefficient, RegularizedProjection.residual, RCLike.inner_apply]

theorem quarticSecond_cancellation : quarticSecond 1 1 (-3) = 0 := by
  norm_num [quarticSecond]

theorem no_pointwise_weightedSecond_bound (C : ℝ) :
    ¬ ∀ f v z : ℝ, f ^ 6 * z ^ 2 ≤ C * quarticSecond f v z ^ 2 := by
  intro h
  have h1 := h 1 1 (-3)
  norm_num [quarticSecond_cancellation] at h1

end Mettapedia.Analysis.ProjectionCurvatureBoundTests
