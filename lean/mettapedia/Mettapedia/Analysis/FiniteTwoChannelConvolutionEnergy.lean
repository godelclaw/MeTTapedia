import Mettapedia.Analysis.FiniteConvolutionEnergy
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.Linarith

/-!
# Finite convolution energy with two separate source channels

A kernel bounded by the sum of two separable products retains both
channels in the energy estimate. Combining their source weights first
would lose the vanishing of an individual error channel.
-/

set_option autoImplicit false

namespace Mettapedia.Analysis.FiniteConvolutionEnergy

open scoped BigOperators

variable {G E : Type*} [AddCommGroup G] [DecidableEq G] [NormedAddCommGroup E]

theorem sum_norm_sq_le_two_channels (P K Q : Finset G) (w₁ w₂ b₁ b₂ : G → ℝ) (H : G → G → E)
    (hw₁ : ∀ p ∈ P, 0 ≤ w₁ p) (hw₂ : ∀ p ∈ P, 0 ≤ w₂ p)
    (hb₁ : ∀ k ∈ K, 0 ≤ b₁ k) (hb₂ : ∀ k ∈ K, 0 ≤ b₂ k)
    (hH : ∀ p ∈ P, ∀ k ∈ K, ‖H p k‖ ≤ w₁ p * b₁ k + w₂ p * b₂ k)
    (hQ : ∀ p ∈ P, ∀ k ∈ K, p + k ∈ Q) :
    (∑ q ∈ Q, ‖∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, H pk.1 pk.2‖ ^ 2) ≤
      2 * (∑ p ∈ P, w₁ p) ^ 2 * (∑ k ∈ K, b₁ k ^ 2) +
        2 * (∑ p ∈ P, w₂ p) ^ 2 * (∑ k ∈ K, b₂ k ^ 2) := by
  have hpoint (q : G) :
      ‖∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, H pk.1 pk.2‖ ^ 2 ≤
        2 * (∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, w₁ pk.1 * b₁ pk.2) ^ 2 +
          2 * (∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, w₂ pk.1 * b₂ pk.2) ^ 2 := by
    have ht := (norm_sum_le ((P ×ˢ K).filter (fun pk ↦ pk.1 + pk.2 = q))
      (fun pk ↦ H pk.1 pk.2)).trans
        (Finset.sum_le_sum (fun pk hpk ↦ hH _ (Finset.mem_product.mp (Finset.mem_filter.mp hpk).1).1
          _ (Finset.mem_product.mp (Finset.mem_filter.mp hpk).1).2))
    rw [Finset.sum_add_distrib] at ht
    have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
    nlinarith only [hs, sq_nonneg
      ((∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, w₁ pk.1 * b₁ pk.2) -
        (∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, w₂ pk.1 * b₂ pk.2))]
  have h₁ := sum_norm_sq_le P K Q w₁ b₁ (fun p k ↦ w₁ p * b₁ k) hw₁
    (fun p hp k hk ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw₁ p hp) (hb₁ k hk))]) hQ
  have h₂ := sum_norm_sq_le P K Q w₂ b₂ (fun p k ↦ w₂ p * b₂ k) hw₂
    (fun p hp k hk ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw₂ p hp) (hb₂ k hk))]) hQ
  simp only [Real.norm_eq_abs, sq_abs] at h₁ h₂
  have h := Finset.sum_le_sum (fun q (_ : q ∈ Q) ↦ hpoint q)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  nlinarith only [h, h₁, h₂]

end Mettapedia.Analysis.FiniteConvolutionEnergy
