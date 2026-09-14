import Mettapedia.Analysis.ShiftedSeriesSquareBound
import Mathlib.Algebra.Order.Chebyshev

/-!
# Square-sum bounds with finitely many shifted envelopes

An additive envelope assigns different weights to different derivative
placements. The only counting factor is the fixed number of envelopes,
not the number of input or output frequencies.
-/

set_option autoImplicit false

namespace Mettapedia.Analysis.FiniteEnvelopeSquareBound

open Filter
open scoped Topology

variable {ι G κ E : Type*} [NormedAddCommGroup E]

theorem norm_sum_sq_le (P : Finset ι) (J : Finset κ) (f : ι → E) (g : κ → ι → ℝ)
    (hf : ∀ p ∈ P, ‖f p‖ ≤ ∑ j ∈ J, g j p) :
    ‖∑ p ∈ P, f p‖ ^ 2 ≤ (J.card : ℝ) * ∑ j ∈ J, (∑ p ∈ P, g j p) ^ 2 := by
  have h : ‖∑ p ∈ P, f p‖ ≤ ∑ j ∈ J, ∑ p ∈ P, g j p := by
    calc
      _ ≤ ∑ p ∈ P, ‖f p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ P, ∑ j ∈ J, g j p := Finset.sum_le_sum hf
      _ = _ := Finset.sum_comm
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans sq_sum_le_card_mul_sum_sq

theorem sum_norm_sum_sq_le (P : Finset ι) (Q : Finset G) (J : Finset κ)
    (f : ι → G → E) (w : κ → ι → ℝ) (b : κ → G → ℝ) (e : ι → G ≃ G)
    (hw : ∀ j ∈ J, ∀ p ∈ P, 0 ≤ w j p) (hb : ∀ j ∈ J, ∀ q, 0 ≤ b j q)
    (hsb : ∀ j ∈ J, Summable (fun q ↦ b j q ^ 2))
    (hf : ∀ p ∈ P, ∀ q, ‖f p q‖ ≤ ∑ j ∈ J, w j p * b j (e p q)) :
    (∑ q ∈ Q, ‖∑ p ∈ P, f p q‖ ^ 2) ≤
      (J.card : ℝ) * ∑ j ∈ J, (∑ p ∈ P, w j p) ^ 2 * ∑' q, b j q ^ 2 := by
  have hj (j : κ) (hj : j ∈ J) :
      (∑ q ∈ Q, (∑ p ∈ P, w j p * b j (e p q)) ^ 2) ≤
        (∑ p ∈ P, w j p) ^ 2 * ∑' q, b j q ^ 2 := by
    have h := ShiftedSeriesSquareBound.sum_norm_sum_sq_le P Q
      (fun p q ↦ w j p * b j (e p q)) (w j) (b j) e (hw j hj) (hsb j hj)
      (fun p hp q ↦ by rw [Real.norm_of_nonneg (mul_nonneg (hw j hj p hp) (hb j hj _))])
    simpa only [Real.norm_eq_abs, sq_abs] using h
  calc
    _ ≤ ∑ q ∈ Q, (J.card : ℝ) * ∑ j ∈ J, (∑ p ∈ P, w j p * b j (e p q)) ^ 2 :=
      Finset.sum_le_sum (fun q _ ↦ norm_sum_sq_le P J (fun p ↦ f p q)
        (fun j p ↦ w j p * b j (e p q)) (fun p hp ↦ hf p hp q))
    _ = (J.card : ℝ) * ∑ j ∈ J, ∑ q ∈ Q, (∑ p ∈ P, w j p * b j (e p q)) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hj) (by positivity)

theorem sum_norm_tsum_sq_le (Q : Finset G) (J : Finset κ)
    (f : ι → G → E) (w : κ → ι → ℝ) (b : κ → G → ℝ) (e : ι → G ≃ G)
    (hw : ∀ j ∈ J, ∀ p, 0 ≤ w j p) (hb : ∀ j ∈ J, ∀ q, 0 ≤ b j q)
    (hsw : ∀ j ∈ J, Summable (w j)) (hsb : ∀ j ∈ J, Summable (fun q ↦ b j q ^ 2))
    (hsf : ∀ q, Summable (fun p ↦ f p q))
    (hf : ∀ p q, ‖f p q‖ ≤ ∑ j ∈ J, w j p * b j (e p q)) :
    (∑ q ∈ Q, ‖∑' p, f p q‖ ^ 2) ≤
      (J.card : ℝ) * ∑ j ∈ J, (∑' p, w j p) ^ 2 * ∑' q, b j q ^ 2 := by
  have ht : Tendsto (fun P : Finset ι ↦ ∑ q ∈ Q, ‖∑ p ∈ P, f p q‖ ^ 2)
      atTop (𝓝 (∑ q ∈ Q, ‖∑' p, f p q‖ ^ 2)) :=
    tendsto_finsetSum _ (fun q _ ↦ (hsf q).hasSum.norm.pow 2)
  apply le_of_tendsto' ht
  intro P
  apply (sum_norm_sum_sq_le P Q J f w b e (fun j hj p _ ↦ hw j hj p) hb hsb
    (fun p _ q ↦ hf p q)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ ↦ hw j hj p))
      ((hsw j hj).sum_le_tsum P (fun p _ ↦ hw j hj p)) 2) (tsum_nonneg (fun _ ↦ sq_nonneg _))

theorem summable_norm_tsum_sq (J : Finset κ)
    (f : ι → G → E) (w : κ → ι → ℝ) (b : κ → G → ℝ) (e : ι → G ≃ G)
    (hw : ∀ j ∈ J, ∀ p, 0 ≤ w j p) (hb : ∀ j ∈ J, ∀ q, 0 ≤ b j q)
    (hsw : ∀ j ∈ J, Summable (w j)) (hsb : ∀ j ∈ J, Summable (fun q ↦ b j q ^ 2))
    (hsf : ∀ q, Summable (fun p ↦ f p q))
    (hf : ∀ p q, ‖f p q‖ ≤ ∑ j ∈ J, w j p * b j (e p q)) :
    Summable (fun q ↦ ‖∑' p, f p q‖ ^ 2) :=
  summable_of_sum_le (fun _ ↦ sq_nonneg _)
    (sum_norm_tsum_sq_le · J f w b e hw hb hsw hsb hsf hf)

theorem tsum_norm_tsum_sq_le (J : Finset κ)
    (f : ι → G → E) (w : κ → ι → ℝ) (b : κ → G → ℝ) (e : ι → G ≃ G)
    (hw : ∀ j ∈ J, ∀ p, 0 ≤ w j p) (hb : ∀ j ∈ J, ∀ q, 0 ≤ b j q)
    (hsw : ∀ j ∈ J, Summable (w j)) (hsb : ∀ j ∈ J, Summable (fun q ↦ b j q ^ 2))
    (hsf : ∀ q, Summable (fun p ↦ f p q))
    (hf : ∀ p q, ‖f p q‖ ≤ ∑ j ∈ J, w j p * b j (e p q)) :
    (∑' q, ‖∑' p, f p q‖ ^ 2) ≤
      (J.card : ℝ) * ∑ j ∈ J, (∑' p, w j p) ^ 2 * ∑' q, b j q ^ 2 :=
  (summable_norm_tsum_sq J f w b e hw hb hsw hsb hsf hf).tsum_le_of_sum_le
    (sum_norm_tsum_sq_le · J f w b e hw hb hsw hsb hsf hf)

end Mettapedia.Analysis.FiniteEnvelopeSquareBound
