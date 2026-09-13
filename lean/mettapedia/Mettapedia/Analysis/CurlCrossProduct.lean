import Mettapedia.Analysis.UnitTorusCurlPairing

/-! # Curl of a cross product with explicit divergence terms -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.EuclideanCrossProduct

open WeightedCurlCancellation
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem curlJet_cross (a b : R3) (D E : Fin 3 → R3) :
    curlJet (fun j ↦ cross (D j) b + cross a (E j)) =
      (∑ j : Fin 3, b j • D j) - (∑ j : Fin 3, a j • E j) +
        (∑ j : Fin 3, E j j) • a - (∑ j : Fin 3, D j j) • b := by
  ext i
  fin_cases i <;> simp [curlJet, cross, cross_apply, Fin.sum_univ_three] <;> ring

theorem curlJet_cross_of_divergence_zero (a b : R3) (D E : Fin 3 → R3)
    (hD : ∑ j : Fin 3, D j j = 0) (hE : ∑ j : Fin 3, E j j = 0) :
    curlJet (fun j ↦ cross (D j) b + cross a (E j)) =
      (∑ j : Fin 3, b j • D j) - (∑ j : Fin 3, a j • E j) := by
  rw [curlJet_cross, hD, hE, zero_smul, zero_smul, add_zero, sub_zero]

end Mettapedia.Analysis.EuclideanCrossProduct
