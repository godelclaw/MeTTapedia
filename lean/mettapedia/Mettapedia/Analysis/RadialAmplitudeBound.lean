import Mettapedia.Analysis.RadialAmplitudeCurvature
import Mettapedia.Analysis.NormalVorticityEnergy

/-!
# Amplitude curvature controlled by normal vorticity

The normal component is measured per unit separation. The remaining factor
has the weighted-gradient degree of the corresponding vorticity dissipation.
This pointwise inequality does not bound the normal component, sum the image
coefficients, or control the other curvature channels.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialPancakeCurvature

open SignedCrossKernel EuclideanCrossProduct NormalVorticityEnergy
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem abs_amplitudeCurvature_radialOperator_le
    (n : ℕ) (c k : ℝ) (h a v w : R3) :
    |amplitudeCurvature n
      (c • ContinuousLinearMap.id ℝ R3 + k • (innerSL ℝ h).smulRight h) a v w| ≤
      2 * (2 * (n + 2) : ℝ) * |k| * ‖h‖ ^ 2 * ‖a‖ ^ (2 * (n + 2)) *
        ‖v - w‖ ^ 2 * |component a h| := by
  have ht : |tripleProduct (v - w) a h| ≤ ‖v - w‖ * ‖a‖ * ‖h‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_cross_le _ _) (norm_nonneg h))
  rw [amplitudeCurvature_radialOperator]
  simp only [abs_mul, abs_pow, abs_norm, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
    abs_of_nonneg (show (0 : ℝ) ≤ 2 * (n + 2) by positivity)]
  calc
    _ ≤ 2 * (2 * (n + 2) : ℝ) * |k| * ‖a‖ ^ (2 * (n + 1)) *
        (‖a‖ * ‖v - w‖) * (‖v - w‖ * ‖a‖ * ‖h‖) * |⟪h, a⟫| := by
      gcongr
      · exact abs_real_inner_le_norm _ _
    _ = _ := by
      rw [← abs_component_mul_norm a h,
        show 2 * (n + 2) = 2 * (n + 1) + 2 by omega, pow_add]
      ring

theorem abs_amplitudeCurvature_tensor_le (N n : ℕ) (e : R3) (he : ‖e‖ = 1)
    {h : R3} (hh : h ≠ 0) (a v w : R3) :
    |amplitudeCurvature n (RadialRieszRegularization.tensor N h) a v w| ≤
      2 * (2 * (n + 2) : ℝ) * |RadialRieszRegularization.radialCoefficient N e h| *
        ‖h‖ ^ 2 * ‖a‖ ^ (2 * (n + 2)) * ‖v - w‖ ^ 2 * |component a h| := by
  rw [RadialRieszRegularization.tensor_eq N e he hh]
  exact abs_amplitudeCurvature_radialOperator_le n _ _ h a v w

end Mettapedia.Analysis.RadialPancakeCurvature
