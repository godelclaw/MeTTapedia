import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Explicit quadratic remainder when absorbing a square-root energy cost. -/

set_option autoImplicit false

namespace Mettapedia.Analysis.SqrtEnergyAbsorption

theorem mul_sqrt_le (K D epsilon : ℝ) (hD : 0 ≤ D) (hepsilon : 0 < epsilon) :
    K * Real.sqrt D ≤ epsilon * D + K ^ 2 / (4 * epsilon) := by
  have h : K * Real.sqrt D - epsilon * D ≤ K ^ 2 / (4 * epsilon) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * epsilon)).mpr
    nlinarith [sq_nonneg (2 * epsilon * Real.sqrt D - K),
      congrArg (fun x : ℝ ↦ epsilon ^ 2 * x) (Real.sq_sqrt hD)]
  linarith

end Mettapedia.Analysis.SqrtEnergyAbsorption
