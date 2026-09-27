import Mathlib.Tactic

/-!
# Sign certificates for high angular Gaussian parents

The circulation heat bracket is positive for angular index at least five.
The rational allowance for the negative pressure contribution to total
enstrophy curvature is less than one for angular index at least six.

These are finite algebraic inequalities. The heat-resolvent identities,
their application to the Navier--Stokes equation, and the nonlinear time
estimates are analytic arguments in the symmetry-defect note; they are
not formalized by this module.
-/

namespace Mettapedia.FluidDynamics.NavierStokes.HelicalHighModeFeedback

/-- The factor in the Gaussian circulation heat-resolvent integrand. -/
noncomputable def circulationHeatBracket (m s : ℝ) : ℝ :=
  2 * m * (m - 4 / (1 + 8 * s)) - 2 * (m - 2)

/-- The negative pressure allowance divided by the positive remaining
quadratic enstrophy coefficient. -/
noncomputable def pressureAllowanceRatio (m : ℝ) : ℝ :=
  (4 * m ^ 5 + 18 * m ^ 4 + 23 * m ^ 3 + 3 * m ^ 2 - 14 * m + 88) /
    ((m - 2) * (m - 1) * (m + 1) ^ 2 * (m + 2) * (m + 3))

theorem circulationHeatBracket_pos (m s : ℝ) (hm : 5 ≤ m) (hs : 0 ≤ s) :
    0 < circulationHeatBracket m s := by
  have hm0 : 0 < m := by linarith
  have hm5 : 0 ≤ m - 5 := by linarith
  have hd : 0 < 1 + 8 * s := by positivity
  have hb : 0 < 2 * (m * m - 5 * m + 2) := by
    calc
      0 < 2 * (m - 5) ^ 2 + 10 * (m - 5) + 4 := by positivity
      _ = 2 * (m * m - 5 * m + 2) := by ring
  have hi : circulationHeatBracket m s =
      2 * (m * m - 5 * m + 2) + 64 * m * s / (1 + 8 * s) := by
    unfold circulationHeatBracket
    field_simp [ne_of_gt hd]
    ring
  have hr : 0 ≤ 64 * m * s / (1 + 8 * s) := by positivity
  rw [hi]
  linarith

theorem pressureAllowanceRatio_lt_one (m : ℝ) (hm : 6 ≤ m) :
    pressureAllowanceRatio m < 1 := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hm6 : 0 ≤ m - 6 := by linarith
  have hd : 0 < (m - 2) * (m - 1) * (m + 1) ^ 2 * (m + 2) * (m + 3) := by
    positivity
  unfold pressureAllowanceRatio
  apply (div_lt_one hd).mpr
  have hi :
      (m - 2) * (m - 1) * (m + 1) ^ 2 * (m + 2) * (m + 3) -
        (4 * m ^ 5 + 18 * m ^ 4 + 23 * m ^ 3 + 3 * m ^ 2 - 14 * m + 88) =
      (m - 6) ^ 6 + 36 * (m - 6) ^ 5 + 520 * (m - 6) ^ 4 +
        3797 * (m - 6) ^ 3 + 14332 * (m - 6) ^ 2 + 24594 * (m - 6) + 11048 := by
    ring
  have hp : 0 <
      (m - 6) ^ 6 + 36 * (m - 6) ^ 5 + 520 * (m - 6) ^ 4 +
        3797 * (m - 6) ^ 3 + 14332 * (m - 6) ^ 2 + 24594 * (m - 6) + 11048 := by
    positivity
  linarith

end Mettapedia.FluidDynamics.NavierStokes.HelicalHighModeFeedback
