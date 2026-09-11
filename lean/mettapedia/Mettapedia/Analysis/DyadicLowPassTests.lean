import Mettapedia.Analysis.DyadicLowPass

/-! Low-pass tests at the origin, the inner ball, the transition, and the outer boundary. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DyadicLowPassTests

open DyadicAnnulus DyadicLowPass

example : multiplier (0 : ℝ) = 1 ∧ (∑' n : ℕ, normalizedCutoff ((2 : ℝ) ^ n • (0 : ℝ))) = 0 := by
  simp

example : multiplier (1 : ℝ) = 1 ∧ multiplier (-1 : ℝ) = 1 :=
  ⟨multiplier_eq_one_of_norm_le _ (by norm_num), multiplier_eq_one_of_norm_le _ (by norm_num)⟩

example : multiplier (4 : ℝ) = 0 := multiplier_eq_zero_of_le_norm _ (by norm_num)

example : multiplier (2 : ℝ) = 1 / 2 := multiplier_eq_half_of_norm_eq_two _ (by norm_num)

example : HasSum (fun n : ℕ ↦ normalizedCutoff ((2 : ℝ) ^ n • (0 : ℝ)) • (0 : ℂ)) 0 := by
  simp

end Mettapedia.Analysis.DyadicLowPassTests

#print axioms Mettapedia.Analysis.DyadicLowPass.multiplier_nonneg
#print axioms Mettapedia.Analysis.DyadicLowPass.multiplier_le_one
#print axioms Mettapedia.Analysis.DyadicLowPass.multiplier_eq_one_of_norm_le
#print axioms Mettapedia.Analysis.DyadicLowPass.multiplier_eq_zero_of_le_norm
#print axioms Mettapedia.Analysis.DyadicLowPass.multiplier_eq_cutoff_add
#print axioms Mettapedia.Analysis.DyadicLowPass.multiplier_eq_half_of_norm_eq_two
#print axioms Mettapedia.Analysis.DyadicLowPass.hasSum_mul
#print axioms Mettapedia.Analysis.DyadicLowPass.hasSum_smul
