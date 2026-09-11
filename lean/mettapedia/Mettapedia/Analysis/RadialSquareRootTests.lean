import Mettapedia.Analysis.RadialSquareRoot
import Mettapedia.Analysis.LocallyLipschitzComposition

/-! Regressions for vanishing radial weights and weighted cutoff differences. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialSquareRootTests

open RadialSquareRoot

private theorem sqrt_four : Real.sqrt 4 = 2 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)

example : radialSqrt (4 : ℝ) = 8 ∧ radialSqrt (-4 : ℝ) = -8 := by
  norm_num [radialSqrt, sqrt_four]

/-- This checks an actual derivative, not Lean's default value for `deriv`. -/
example : HasDerivAt (radialSqrt : ℝ → ℝ) 0 0 := by
  simpa using (hasFDerivAt_radialSqrt_zero (E := ℝ)).hasDerivAt

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : E) :
    ‖radialSqrt w‖ ^ 2 = ‖w‖ ^ 3 := by
  simp only [radialSqrt, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (norm_nonneg w)]
  ring

/-- The weighted two-point estimate is attained when the first vector is zero. -/
example : |Real.sqrt ‖(0 : ℝ)‖ - Real.sqrt ‖(4 : ℝ)‖| * ‖(4 : ℝ)‖ =
    Real.sqrt ‖(4 : ℝ)‖ * ‖(0 : ℝ) - 4‖ := by
  norm_num [sqrt_four]

/-- Equal vectors leave the scalar-factor variation channel. -/
example : |2 * Real.sqrt ‖(4 : ℝ)‖ - 1 * Real.sqrt ‖(4 : ℝ)‖| * ‖(4 : ℝ)‖ =
    |(2 : ℝ) - 1| * Real.sqrt ‖(4 : ℝ)‖ * ‖(4 : ℝ)‖ := by
  norm_num [sqrt_four]

example : deriv (fun t : ℝ ↦ t • radialSqrt t) 0 = 0 := by
  have hr : HasDerivAt (radialSqrt : ℝ → ℝ) 0 0 := by
    simpa using (hasFDerivAt_radialSqrt_zero (E := ℝ)).hasDerivAt
  have hh : HasDerivAt (fun t : ℝ ↦ t • radialSqrt t)
      ((0 : ℝ) • (0 : ℝ) + (1 : ℝ) • radialSqrt (0 : ℝ)) 0 :=
    (hasDerivAt_id (0 : ℝ)).smul hr
  simpa [radialSqrt] using hh.deriv

end Mettapedia.Analysis.RadialSquareRootTests

#print axioms LocallyLipschitz.comp_contDiffAt
#print axioms LocallyLipschitz.sqrt
#print axioms LocallyLipschitz.inv_real
#print axioms LocallyLipschitz.div_real
#print axioms Mettapedia.Analysis.RadialSquareRoot.sqrt_sub_mul_sqrt_le
#print axioms Mettapedia.Analysis.RadialSquareRoot.sqrt_norm_sub_mul_norm_le
#print axioms Mettapedia.Analysis.RadialSquareRoot.abs_mul_sqrt_norm_sub_mul_norm_le
#print axioms Mettapedia.Analysis.RadialSquareRoot.norm_radialSqrt_sub_le
#print axioms Mettapedia.Analysis.RadialSquareRoot.lipschitzOnWith_radialSqrt
#print axioms Mettapedia.Analysis.RadialSquareRoot.locallyLipschitz_radialSqrt
#print axioms Mettapedia.Analysis.RadialSquareRoot.continuous_radialSqrt
#print axioms Mettapedia.Analysis.RadialSquareRoot.hasFDerivAt_radialSqrt_zero
#print axioms Mettapedia.Analysis.RadialSquareRoot.differentiable_radialSqrt
#print axioms Mettapedia.Analysis.RadialSquareRoot.norm_derivative_radialSqrt_le
#print axioms Mettapedia.Analysis.RadialSquareRoot.norm_deriv_smul_radialSqrt_sq_le
