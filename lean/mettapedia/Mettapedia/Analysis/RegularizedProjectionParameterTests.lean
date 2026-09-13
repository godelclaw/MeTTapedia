import Mettapedia.Analysis.RegularizedProjectionParameter

/-!
# Sign regressions for changing regularization

Even equal, nonzero inputs give both signs when the normalization grows.
These are algebraic tests, not examples of Navier--Stokes trajectories.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RegularizedProjectionParameterTests

open RegularizedProjectionParameter RegularizedProjection

theorem aligned_scaleRate_negative : scaleRate 1 1 1 (1 : ℝ) 1 = -3 / 8 := by
  norm_num [scaleRate, RegularizedProjection.residual, coefficient, Real.norm_eq_abs]

theorem aligned_scaleRate_positive : scaleRate 1 3 1 (1 : ℝ) 1 = 1 / 8 := by
  norm_num [scaleRate, RegularizedProjection.residual, coefficient, Real.norm_eq_abs]

theorem constant_scaleRate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ν κ : ℝ) (a b : E) : scaleRate ν κ 0 a b = 0 := by
  simp [scaleRate]

end Mettapedia.Analysis.RegularizedProjectionParameterTests
