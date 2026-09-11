import Mettapedia.Analysis.FiniteConvolutionEnergy

/-!
# Young's inequality with finitely indexed source shifts

Several source indices may have the same shift. They are retained before
squaring, and the source cost is the sum of their actual weights, not the
number of indices or distinct shifts.
-/

set_option autoImplicit false

namespace Mettapedia.Analysis.FiniteGroupedConvolutionEnergy

open scoped BigOperators

variable {ι G E : Type*} [AddCommGroup G] [DecidableEq G] [NormedAddCommGroup E]

theorem sum_fiber_weight_le (I : Finset ι) (K : Finset G) (shift : ι → G) (w : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (q : G) :
    (∑ ik ∈ I ×ˢ K with shift ik.1 + ik.2 = q, w ik.1) ≤ ∑ i ∈ I, w i := by
  classical
  simp only [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_le_sum
  intro i hi
  simp only [← eq_sub_iff_add_eq', Finset.sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact hw i hi

theorem sum_norm_sq_le (I : Finset ι) (K Q : Finset G) (shift : ι → G)
    (w : ι → ℝ) (b : G → ℝ) (H : ι → G → E)
    (hw : ∀ i ∈ I, 0 ≤ w i)
    (hH : ∀ i ∈ I, ∀ k ∈ K, ‖H i k‖ ≤ w i * b k)
    (hQ : ∀ i ∈ I, ∀ k ∈ K, shift i + k ∈ Q) :
    (∑ q ∈ Q, ‖∑ ik ∈ I ×ˢ K with shift ik.1 + ik.2 = q, H ik.1 ik.2‖ ^ 2) ≤
      (∑ i ∈ I, w i) ^ 2 * ∑ k ∈ K, b k ^ 2 := by
  classical
  have hpoint (q : G) : ‖∑ ik ∈ I ×ˢ K with shift ik.1 + ik.2 = q, H ik.1 ik.2‖ ^ 2 ≤
      (∑ i ∈ I, w i) * ∑ ik ∈ I ×ˢ K with shift ik.1 + ik.2 = q, w ik.1 * b ik.2 ^ 2 := by
    let F := (I ×ˢ K).filter (fun ik ↦ shift ik.1 + ik.2 = q)
    have hm (ik : ι × G) (hik : ik ∈ F) : ik.1 ∈ I ∧ ik.2 ∈ K :=
      Finset.mem_product.mp (Finset.mem_filter.mp hik).1
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul F
      (fun ik hik ↦ hw _ (hm ik hik).1)
      (fun ik hik ↦ mul_nonneg (hw _ (hm ik hik).1) (sq_nonneg (b ik.2)))
      (fun ik hik ↦ show ‖H ik.1 ik.2‖ ^ 2 ≤ w ik.1 * (w ik.1 * b ik.2 ^ 2) by
        have h := pow_le_pow_left₀ (norm_nonneg _) (hH _ (hm ik hik).1 _ (hm ik hik).2) 2
        nlinarith only [h])
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le F (fun ik ↦ H ik.1 ik.2)) 2
    have hs := mul_le_mul_of_nonneg_right (sum_fiber_weight_le I K shift w hw q)
      (Finset.sum_nonneg (fun ik hik ↦ mul_nonneg (hw _ (hm ik hik).1) (sq_nonneg (b ik.2))))
    exact hn.trans (hcs.trans hs)
  have hs := Finset.sum_le_sum (fun q (_ : q ∈ Q) ↦ hpoint q)
  rw [← Finset.mul_sum] at hs
  have hf : (∑ q ∈ Q, ∑ ik ∈ I ×ˢ K with shift ik.1 + ik.2 = q, w ik.1 * b ik.2 ^ 2) =
      (∑ i ∈ I, w i) * ∑ k ∈ K, b k ^ 2 := by
    rw [Finset.sum_fiberwise_of_maps_to
      (fun ik hik ↦ hQ _ (Finset.mem_product.mp hik).1 _ (Finset.mem_product.mp hik).2)]
    simp only [Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hf] at hs
  nlinarith only [hs]

end Mettapedia.Analysis.FiniteGroupedConvolutionEnergy
