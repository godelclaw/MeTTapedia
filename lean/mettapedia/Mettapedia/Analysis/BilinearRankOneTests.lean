import Mettapedia.Analysis.BilinearRankOne
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

/-! Real and complex rank-one bilinear checks, including the non-Hermitian phase. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearRankOneTests

open BilinearRankOne

example : rankOne (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ) (3 : ℝ) 2 5 = 30 := by
  norm_num

example : rankOne (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ ℂ)
    (1 : ℂ) Complex.I Complex.I = -1 := by simp

example : ‖rankOne (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ ℂ) (3 : ℂ)‖ = 3 := by
  simp

end Mettapedia.Analysis.BilinearRankOneTests

#print axioms Mettapedia.Analysis.BilinearRankOne.rankOne_apply
#print axioms Mettapedia.Analysis.BilinearRankOne.norm_rankOne
