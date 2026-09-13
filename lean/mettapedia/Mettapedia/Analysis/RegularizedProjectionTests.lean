import Mettapedia.Analysis.RegularizedProjection

/-! # Sharpness, zero-vector, and curvature tests for regularized projection -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RegularizedProjectionTests

open RegularizedProjection
open scoped RealInnerProductSpace

theorem coefficient_at_zero : coefficient 1 (0 : ℝ) 1 = 0 := by
  norm_num [coefficient]

theorem energy_at_zero : energy 1 (0 : ℝ) 1 = 1 := by
  norm_num [energy, RegularizedProjection.residual, coefficient]

theorem sharp_inner_residual : ⟪(1 : ℝ), residual 1 (1 : ℝ) 1⟫ ^ 2 = 1 / 4 := by
  norm_num [RegularizedProjection.residual, coefficient, RCLike.inner_apply]

/-- Minimizing in the scalar coefficient does not make the resulting
function jointly convex in the two vectors. -/
theorem midpoint_convexity_fails :
    2 * energy 1 (0 : ℝ) 1 > energy 1 (-1 : ℝ) 1 + energy 1 (1 : ℝ) 1 := by
  norm_num [energy, RegularizedProjection.residual, coefficient, RCLike.inner_apply]

theorem moving_minimum_derivative :
    HasDerivAt (fun t : ℝ ↦ energy 1 (1 : ℝ) t) 1 1 := by
  convert
    (hasDerivAt_energy 1 (by norm_num) (hasDerivAt_const (1 : ℝ) (1 : ℝ))
      (hasDerivAt_id (1 : ℝ))) using 1 <;>
    norm_num [RegularizedProjection.residual, coefficient, RCLike.inner_apply]

end Mettapedia.Analysis.RegularizedProjectionTests
