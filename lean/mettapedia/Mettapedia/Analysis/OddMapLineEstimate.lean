import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unoriented-line estimates for odd Lipschitz maps

For an odd map, reversing the reference direction changes no output norm.
The squared freezing error therefore costs the smaller of the two oriented
direction distances. Finite nonnegative weights retain their actual sum,
not the number of reference directions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.OddMapLineEstimate

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem norm_sub_norm_sq_le_unoriented (f : E → F) (hodd : ∀ r, f (-r) = -f r)
    (L : ℝ)
    (h : ∀ e r, ‖e‖ = 1 → ‖r‖ = 1 → ‖f e - f r‖ ≤ L * ‖e - r‖)
    (e r : E) (he : ‖e‖ = 1) (hr : ‖r‖ = 1) :
    (‖f e‖ - ‖f r‖) ^ 2 ≤ L ^ 2 * min (‖e - r‖ ^ 2) (‖e + r‖ ^ 2) := by
  have oriented (s : E) (hs : ‖s‖ = 1) :
      (‖f e‖ - ‖f s‖) ^ 2 ≤ L ^ 2 * ‖e - s‖ ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg (‖f e‖ - ‖f s‖))
      ((abs_norm_sub_norm_le (f e) (f s)).trans (h e s he hs)) 2
    simpa only [sq_abs, mul_pow] using hp
  rcases le_total (‖e - r‖ ^ 2) (‖e + r‖ ^ 2) with hp | hn
  · simpa only [min_eq_left hp] using oriented r hr
  · simpa only [min_eq_right hn, hodd, norm_neg, sub_neg_eq_add] using
      oriented (-r) (by simpa using hr)

theorem abs_weight_mul_norm_sub_norm_le (f : E → F) (hodd : ∀ r, f (-r) = -f r)
    (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ e r, ‖e‖ = 1 → ‖r‖ = 1 → ‖f e - f r‖ ≤ L * ‖e - r‖)
    (e r : E) (he : ‖e‖ = 1) (hr : ‖r‖ = 1) (a d : ℝ) (hd : 0 ≤ d)
    (hline : a ^ 2 * min (‖e - r‖ ^ 2) (‖e + r‖ ^ 2) ≤ 2 * d ^ 2) :
    |a * (‖f e‖ - ‖f r‖)| ≤ 2 * L * d := by
  have hn := mul_le_mul_of_nonneg_left
    (norm_sub_norm_sq_le_unoriented f hodd L h e r he hr) (sq_nonneg a)
  have hl := mul_le_mul_of_nonneg_left hline (sq_nonneg L)
  have hs : (a * (‖f e‖ - ‖f r‖)) ^ 2 ≤ (2 * L * d) ^ 2 := by
    nlinarith only [hn, hl, sq_nonneg (L * d)]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hL) hd)).mp
    (by simpa only [sq_abs] using hs)

theorem norm_sq_le_oriented (f : E → F) (L : ℝ)
    (e r : E) (h : ‖f e - f r‖ ≤ L * ‖e - r‖) :
    ‖f e‖ ^ 2 ≤ 2 * ‖f r‖ ^ 2 + 2 * L ^ 2 * ‖e - r‖ ^ 2 := by
  have hn := (norm_le_norm_sub_add (f e) (f r)).trans (add_le_add h le_rfl)
  have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith only [hp, sq_nonneg (‖f r‖ - L * ‖e - r‖)]

theorem norm_sq_le_unoriented (f : E → F) (hodd : ∀ r, f (-r) = -f r)
    (L : ℝ)
    (h : ∀ e r, ‖e‖ = 1 → ‖r‖ = 1 → ‖f e - f r‖ ≤ L * ‖e - r‖)
    (e r : E) (he : ‖e‖ = 1) (hr : ‖r‖ = 1) :
    ‖f e‖ ^ 2 ≤ 2 * ‖f r‖ ^ 2 + 2 * L ^ 2 * min (‖e - r‖ ^ 2) (‖e + r‖ ^ 2) := by
  have hpos := norm_sq_le_oriented f L e r (h e r he hr)
  have hneg := norm_sq_le_oriented f L e (-r) (h e (-r) he (by simpa using hr))
  simp only [hodd, norm_neg, sub_neg_eq_add] at hneg
  rcases le_total (‖e - r‖ ^ 2) (‖e + r‖ ^ 2) with hp | hn
  · simpa only [min_eq_left hp] using hpos
  · simpa only [min_eq_right hn] using hneg

theorem sum_weight_mul_norm_sq_le {ι : Type*} [Fintype ι]
    (f : E → F) (hodd : ∀ r, f (-r) = -f r) (L : ℝ)
    (h : ∀ e r, ‖e‖ = 1 → ‖r‖ = 1 → ‖f e - f r‖ ≤ L * ‖e - r‖)
    (e : E) (he : ‖e‖ = 1) (r : ι → E) (hr : ∀ i, ‖r i‖ = 1)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i) * ‖f e‖ ^ 2 ≤ 2 * (∑ i, a i * ‖f (r i)‖ ^ 2) +
      2 * L ^ 2 * ∑ i, a i * min (‖e - r i‖ ^ 2) (‖e + r i‖ ^ 2) := by
  classical
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ i, a i * (2 * ‖f (r i)‖ ^ 2 +
        2 * L ^ 2 * min (‖e - r i‖ ^ 2) (‖e + r i‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (norm_sq_le_unoriented f hodd L h e (r i) he (hr i)) (ha i)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

end Mettapedia.Analysis.OddMapLineEstimate
