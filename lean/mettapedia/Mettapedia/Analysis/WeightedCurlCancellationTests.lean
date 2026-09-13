import Mettapedia.Analysis.WeightedCurlCancellation

/-!
# Sign and weight checks for the curl cancellation

These are first-jet algebra checks, not periodic counterexamples. The
nonzero weighted divergence records the amplitude term before integration.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedCurlCancellationTests

open WeightedCurlCancellation
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def a : R3 := WithLp.toLp 2 ![1, 0, 0]
def D : Fin 3 → R3 := ![WithLp.toLp 2 ![1, 0, 0], WithLp.toLp 2 ![0, -1, 1], 0]

theorem curlJet_D : curlJet D = a := by
  ext i
  fin_cases i <;> norm_num [curlJet, D, a, Matrix.cons_val_two]
theorem divergence_D : (∑ j : Fin 3, D j j) = 0 := by
  norm_num [D, Fin.sum_univ_three, Matrix.cons_val_two]
theorem norm_a_sq : ‖a‖ ^ 2 = 1 := by simp [a, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

theorem unweighted_fluxRate_zero : (∑ j : Fin 3, fluxRate 0 a a (D j) 0 j) = 0 := by
  rw [sum_fluxRate 0 a a D (fun _ ↦ 0) curlJet_D.symm divergence_D (by simp)]
  simp [weightRate]

theorem sixth_weight_fluxRate_six : (∑ j : Fin 3, fluxRate 3 a a (D j) 0 j) = 6 := by
  rw [sum_fluxRate 3 a a D (fun _ ↦ 0) curlJet_D.symm divergence_D (by simp)]
  simp only [weightRate, real_inner_self_eq_norm_sq, norm_a_sq, inner_zero_right,
    mul_zero, Finset.sum_const_zero, zero_add]
  norm_num [a, D, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem fluxRate_zero_vorticity (n : ℕ) (q v z : R3) (j : Fin 3) :
    fluxRate n 0 q v z j = 0 := by
  cases n <;> simp [fluxRate, weightRate]

end Mettapedia.Analysis.WeightedCurlCancellationTests
