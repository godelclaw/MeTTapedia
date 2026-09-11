import Mettapedia.Analysis.BilinearSeries
import Mettapedia.Analysis.UnitTorusContinuousFourier

/-! Cross interactions, complex phase, and coefficient extraction tests. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearSeriesTests

open BilinearSeries UnitTorusContinuousFourier

/-- All four cross interactions are present. -/
example : HasSum (fun p : Fin 2 × Fin 2 ↦ (![1, 2] p.1 : ℝ) * ![4, 5] p.2) 27 := by
  have h := hasSum_apply (ContinuousLinearMap.mul ℝ ℝ)
    (![1, 2] : Fin 2 → ℝ) (![4, 5] : Fin 2 → ℝ) Summable.of_finite Summable.of_finite
  norm_num [tsum_fintype, Fin.sum_univ_two] at h
  exact h

/-- Keeping only matching indices gives the wrong result. -/
example : (∑ i : Fin 2, (![1, 2] i : ℝ) * ![4, 5] i) ≠
    (∑ i : Fin 2, (![1, 2] i : ℝ)) * (∑ j : Fin 2, (![4, 5] j : ℝ)) := by
  norm_num [Fin.sum_univ_two]

example : HasSum (fun _ : Unit × Unit ↦ (Complex.I : ℂ) * Complex.I) (-1) := by
  have h := hasSum_apply (ContinuousLinearMap.mul ℂ ℂ)
    (fun _ : Unit ↦ Complex.I) (fun _ : Unit ↦ Complex.I)
    Summable.of_finite Summable.of_finite
  simpa using h

example : UnitAddTorus.mFourierCoeff
    (fun x : UnitAddTorus (Fin 1) ↦ UnitAddTorus.mFourier (fun _ ↦ 1) x • Complex.I)
    (fun _ ↦ 1) = Complex.I := by
  rw [mFourierCoeff_monomial, if_pos rfl]

example : UnitAddTorus.mFourierCoeff
    (fun x : UnitAddTorus (Fin 1) ↦ UnitAddTorus.mFourier (fun _ ↦ 1) x • Complex.I)
    (fun _ ↦ 0) = 0 := by
  rw [mFourierCoeff_monomial]
  rw [if_neg]
  intro h
  have hh := congrFun h (0 : Fin 1)
  norm_num at hh

end Mettapedia.Analysis.BilinearSeriesTests

#print axioms Mettapedia.Analysis.BilinearSeries.summable_norm_apply
#print axioms Mettapedia.Analysis.BilinearSeries.hasSum_apply
#print axioms Mettapedia.Analysis.UnitTorusContinuousFourier.norm_coefficientCLM_le
#print axioms Mettapedia.Analysis.UnitTorusContinuousFourier.mFourierCoeff_monomial
#print axioms Mettapedia.Analysis.UnitTorusContinuousFourier.hasSum_mFourierCoeff
