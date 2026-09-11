import Mettapedia.Analysis.DyadicHighPass

/-! The high-input partition includes its zero, transition, and exterior cases. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DyadicHighPassTests

open DyadicAnnulus DyadicHighPass

example : multiplier (0 : ℝ) = 0 := by simp

example : multiplier (1 / 2 : ℝ) = 0 ∧ multiplier (-1 / 2 : ℝ) = 0 :=
  ⟨multiplier_eq_zero_of_norm_le _ (by norm_num),
    multiplier_eq_zero_of_norm_le _ (by norm_num)⟩

example : multiplier (2 : ℝ) = 1 := multiplier_eq_one_of_le_norm _ (by norm_num)

example : multiplier (1 : ℝ) = 1 / 2 := multiplier_eq_half_of_norm_eq_one _ (by norm_num)

/-- The one-sided annular sum is not identically one away from the origin. -/
example : HasSum (fun j : ℕ ↦ normalizedCutoff ((1 / 2 : ℝ) ^ j • (1 : ℝ))) (1 / 2) := by
  simpa only [multiplier_eq_half_of_norm_eq_one (1 : ℝ) (by norm_num)] using
    hasSum_annuli (1 : ℝ)

end Mettapedia.Analysis.DyadicHighPassTests

#print axioms Mettapedia.Analysis.DyadicHighPass.multiplier_nonneg
#print axioms Mettapedia.Analysis.DyadicHighPass.multiplier_le_one
#print axioms Mettapedia.Analysis.DyadicHighPass.multiplier_eq_zero_of_norm_le
#print axioms Mettapedia.Analysis.DyadicHighPass.multiplier_eq_one_of_le_norm
#print axioms Mettapedia.Analysis.DyadicHighPass.multiplier_eq_half_of_norm_eq_one
#print axioms Mettapedia.Analysis.DyadicHighPass.hasSum_annuli
