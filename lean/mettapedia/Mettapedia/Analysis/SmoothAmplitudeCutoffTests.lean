import Mettapedia.Analysis.SmoothAmplitudeCutoffEvolution
import Mettapedia.Analysis.SmoothAmplitudePairing

/-! # Zero, subthreshold and second-variation checks for rational amplitude retention -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SmoothAmplitudeCutoffTests

open SmoothAmplitudeCutoff
open scoped RealInnerProductSpace

theorem subthreshold_pair_weight : pairWeight 1 (1 / 2 : ℝ) (1 / 2 : ℝ) = 1 / 25 := by
  norm_num [pairWeight, retainedWeight, Real.norm_eq_abs]

theorem zero_value_rate_curvature :
    retainedWeight 1 (0 : ℝ) = 0 ∧ retainedRate 1 (0 : ℝ) 1 = 0 ∧
      retainedCurvature 1 (0 : ℝ) 1 = 2 := by
  norm_num [retainedWeight, retainedRate, retainedCurvature]

theorem threshold_value_rate_curvature :
    retainedWeight 1 (1 : ℝ) = 1 / 2 ∧ retainedRate 1 (1 : ℝ) 1 = 1 / 2 ∧
      retainedCurvature 1 (1 : ℝ) 1 = -1 / 2 := by
  norm_num [retainedWeight, retainedRate, retainedCurvature]

theorem retained_second_derivative_at_threshold :
    HasDerivAt (fun t : ℝ ↦ retainedRate 1 (1 + t) 1) (-1 / 2) 0 := by
  have ha : HasDerivAt (fun t : ℝ ↦ 1 + t) 1 0 := (hasDerivAt_id 0).const_add 1
  have h := hasDerivAt_retainedRate 1 (by norm_num) ha (hasDerivAt_const 0 (1 : ℝ))
  norm_num [retainedRate, retainedCurvature] at h ⊢
  exact h

end Mettapedia.Analysis.SmoothAmplitudeCutoffTests
