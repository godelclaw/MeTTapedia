import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Square-sum bounds for shifted vector series

An absolutely summable nonnegative input weight and a square-summable
output envelope bound the full vector series. Shifts are bijections,
so no input- or output-cardinality multiplier occurs.
-/

set_option autoImplicit false

namespace Mettapedia.Analysis.ShiftedSeriesSquareBound

open Filter
open scoped Topology

variable {ι G E : Type*} [NormedAddCommGroup E]

theorem norm_sum_sq_le (P : Finset ι) (f : ι → E) (w b : ι → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p)
    (hf : ∀ p ∈ P, ‖f p‖ ≤ w p * b p) :
    ‖∑ p ∈ P, f p‖ ^ 2 ≤ (∑ p ∈ P, w p) * ∑ p ∈ P, w p * b p ^ 2 := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul P hw
    (fun p hp ↦ mul_nonneg (hw p hp) (sq_nonneg _))
  intro p hp
  exact (pow_le_pow_left₀ (norm_nonneg _) (hf p hp) 2).trans_eq (by ring)

theorem sum_norm_sum_sq_le (P : Finset ι) (Q : Finset G) (f : ι → G → E)
    (w : ι → ℝ) (b : G → ℝ) (e : ι → G ≃ G)
    (hw : ∀ p ∈ P, 0 ≤ w p)
    (hsb : Summable (fun q ↦ b q ^ 2))
    (hf : ∀ p ∈ P, ∀ q, ‖f p q‖ ≤ w p * b (e p q)) :
    (∑ q ∈ Q, ‖∑ p ∈ P, f p q‖ ^ 2) ≤
      (∑ p ∈ P, w p) ^ 2 * ∑' q, b q ^ 2 := by
  have hW : 0 ≤ ∑ p ∈ P, w p := Finset.sum_nonneg hw
  have hq (p : ι) : (∑ q ∈ Q, b (e p q) ^ 2) ≤ ∑' q, b q ^ 2 := by
    have h := (hsb.comp_injective (e p).injective).sum_le_tsum Q (fun _ _ ↦ sq_nonneg _)
    simpa only [(e p).tsum_eq (fun q ↦ b q ^ 2)] using h
  calc
    _ ≤ ∑ q ∈ Q, (∑ p ∈ P, w p) * ∑ p ∈ P, w p * b (e p q) ^ 2 :=
      Finset.sum_le_sum (fun q _ ↦ norm_sum_sq_le P (fun p ↦ f p q) w (fun p ↦ b (e p q))
        hw (fun p hp ↦ hf p hp q))
    _ = (∑ p ∈ P, w p) * ∑ p ∈ P, w p * ∑ q ∈ Q, b (e p q) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ (∑ p ∈ P, w p) * ∑ p ∈ P, w p * ∑' q, b q ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum
        (fun p hp ↦ mul_le_mul_of_nonneg_left (hq p) (hw p hp))) hW
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem sum_norm_tsum_sq_le (Q : Finset G) (f : ι → G → E)
    (w : ι → ℝ) (b : G → ℝ) (e : ι → G ≃ G)
    (hw : ∀ p, 0 ≤ w p) (hsw : Summable w)
    (hsb : Summable (fun q ↦ b q ^ 2)) (hsf : ∀ q, Summable (fun p ↦ f p q))
    (hf : ∀ p q, ‖f p q‖ ≤ w p * b (e p q)) :
    (∑ q ∈ Q, ‖∑' p, f p q‖ ^ 2) ≤ (∑' p, w p) ^ 2 * ∑' q, b q ^ 2 := by
  have ht : Tendsto (fun P : Finset ι ↦ ∑ q ∈ Q, ‖∑ p ∈ P, f p q‖ ^ 2)
      atTop (𝓝 (∑ q ∈ Q, ‖∑' p, f p q‖ ^ 2)) :=
    tendsto_finsetSum _ (fun q _ ↦ (hsf q).hasSum.norm.pow 2)
  apply le_of_tendsto' ht
  intro P
  apply (sum_norm_sum_sq_le P Q f w b e (fun p _ ↦ hw p) hsb (fun p _ q ↦ hf p q)).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ ↦ hw p))
      (hsw.sum_le_tsum P (fun p _ ↦ hw p)) 2) (tsum_nonneg (fun _ ↦ sq_nonneg _))

theorem summable_norm_tsum_sq (f : ι → G → E)
    (w : ι → ℝ) (b : G → ℝ) (e : ι → G ≃ G)
    (hw : ∀ p, 0 ≤ w p) (hsw : Summable w)
    (hsb : Summable (fun q ↦ b q ^ 2)) (hsf : ∀ q, Summable (fun p ↦ f p q))
    (hf : ∀ p q, ‖f p q‖ ≤ w p * b (e p q)) :
    Summable (fun q ↦ ‖∑' p, f p q‖ ^ 2) :=
  summable_of_sum_le (fun _ ↦ sq_nonneg _)
    (fun Q ↦ sum_norm_tsum_sq_le Q f w b e hw hsw hsb hsf hf)

theorem tsum_norm_tsum_sq_le (f : ι → G → E)
    (w : ι → ℝ) (b : G → ℝ) (e : ι → G ≃ G)
    (hw : ∀ p, 0 ≤ w p) (hsw : Summable w)
    (hsb : Summable (fun q ↦ b q ^ 2)) (hsf : ∀ q, Summable (fun p ↦ f p q))
    (hf : ∀ p q, ‖f p q‖ ≤ w p * b (e p q)) :
    (∑' q, ‖∑' p, f p q‖ ^ 2) ≤ (∑' p, w p) ^ 2 * ∑' q, b q ^ 2 :=
  (summable_norm_tsum_sq f w b e hw hsw hsb hsf hf).tsum_le_of_sum_le
    (fun Q ↦ sum_norm_tsum_sq_le Q f w b e hw hsw hsb hsf hf)

end Mettapedia.Analysis.ShiftedSeriesSquareBound
