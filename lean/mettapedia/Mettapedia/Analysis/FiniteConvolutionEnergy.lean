import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A finite convolution energy estimate

An additive convolution with a normed-group-valued kernel is bounded by
the squared sum of its nonnegative source weights times the receiver
energy. Cauchy--Schwarz is applied with those weights, not with counting
measure. The estimate therefore has no source- or output-cardinality loss.
-/

set_option autoImplicit false

namespace Mettapedia.Analysis.FiniteConvolutionEnergy

open scoped BigOperators

variable {G E : Type*} [AddCommGroup G] [DecidableEq G] [NormedAddCommGroup E]

theorem sum_fiber_weight_le (P K : Finset G) (w : G → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (q : G) :
    (∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, w pk.1) ≤ ∑ p ∈ P, w p := by
  classical
  simp only [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_le_sum
  intro p hp
  simp only [← eq_sub_iff_add_eq', Finset.sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact hw p hp

/-- Weighted finite Young inequality, allowing a kernel that depends on
both input modes. The output set need only contain their sums. -/
theorem sum_norm_sq_le (P K Q : Finset G) (w b : G → ℝ) (H : G → G → E)
    (hw : ∀ p ∈ P, 0 ≤ w p)
    (hH : ∀ p ∈ P, ∀ k ∈ K, ‖H p k‖ ≤ w p * b k)
    (hQ : ∀ p ∈ P, ∀ k ∈ K, p + k ∈ Q) :
    (∑ q ∈ Q, ‖∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, H pk.1 pk.2‖ ^ 2) ≤
      (∑ p ∈ P, w p) ^ 2 * ∑ k ∈ K, b k ^ 2 := by
  classical
  have hpoint (q : G) : ‖∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, H pk.1 pk.2‖ ^ 2 ≤
      (∑ p ∈ P, w p) * ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, w pk.1 * b pk.2 ^ 2 := by
    let F := (P ×ˢ K).filter (fun pk ↦ pk.1 + pk.2 = q)
    have hm (pk : G × G) (hpk : pk ∈ F) : pk.1 ∈ P ∧ pk.2 ∈ K :=
      Finset.mem_product.mp (Finset.mem_filter.mp hpk).1
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul F
      (fun pk hpk ↦ hw _ (hm pk hpk).1)
      (fun pk hpk ↦ mul_nonneg (hw _ (hm pk hpk).1) (sq_nonneg (b pk.2)))
      (fun pk hpk ↦ show ‖H pk.1 pk.2‖ ^ 2 ≤ w pk.1 * (w pk.1 * b pk.2 ^ 2) by
        have h := pow_le_pow_left₀ (norm_nonneg _) (hH _ (hm pk hpk).1 _ (hm pk hpk).2) 2
        nlinarith only [h])
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le F (fun pk ↦ H pk.1 pk.2)) 2
    have hs := mul_le_mul_of_nonneg_right (sum_fiber_weight_le P K w hw q)
      (Finset.sum_nonneg (fun pk hpk ↦ mul_nonneg (hw _ (hm pk hpk).1) (sq_nonneg (b pk.2))))
    exact hn.trans (hcs.trans hs)
  have hs := Finset.sum_le_sum (fun q (_ : q ∈ Q) ↦ hpoint q)
  rw [← Finset.mul_sum] at hs
  have hf : (∑ q ∈ Q, ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, w pk.1 * b pk.2 ^ 2) =
      (∑ p ∈ P, w p) * ∑ k ∈ K, b k ^ 2 := by
    rw [Finset.sum_fiberwise_of_maps_to
      (fun pk hpk ↦ hQ _ (Finset.mem_product.mp hpk).1 _ (Finset.mem_product.mp hpk).2)]
    simp only [Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hf] at hs
  nlinarith only [hs]

end Mettapedia.Analysis.FiniteConvolutionEnergy
