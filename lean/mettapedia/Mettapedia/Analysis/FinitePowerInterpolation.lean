import Mathlib.Analysis.MeanInequalities

/-!
# The finite-support cost of replacing squares by `8/5` powers

The cardinality factor is explicit and sharp for constant coefficients.
In particular an `ell^(8/5)` Fourier cost is not a physical `L^(8/5)` norm.
-/

namespace Mettapedia.Analysis.FinitePowerInterpolation

theorem sum_eight_fifths_le_card_one_fifth_mul_sum_sq {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i ^ (8 / 5 : ℝ)) ≤
      (s.card : ℝ) ^ (1 / 5 : ℝ) * (∑ i ∈ s, f i ^ 2) ^ (4 / 5 : ℝ) := by
  have h := Real.inner_le_Lp_mul_Lq s (fun i ↦ f i ^ (8 / 5 : ℝ)) (fun _ ↦ (1 : ℝ))
    (by norm_num [Real.holderConjugate_iff] : (5 / 4 : ℝ).HolderConjugate 5)
  have he : (∑ i ∈ s, |f i ^ (8 / 5 : ℝ)| ^ (5 / 4 : ℝ)) = ∑ i ∈ s, f i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_nonneg (Real.rpow_nonneg (hf i hi) _), ← Real.rpow_mul (hf i hi)]
    norm_num
  simpa only [mul_one, he, abs_one, Real.one_rpow, Finset.sum_const, nsmul_eq_mul,
    mul_one, one_mul, show (1 / (5 / 4) : ℝ) = 4 / 5 by norm_num, mul_comm] using h

theorem card_factor_equality {ι : Type*} (s : Finset ι) :
    (∑ _ ∈ s, (1 : ℝ) ^ (8 / 5 : ℝ)) =
      (s.card : ℝ) ^ (1 / 5 : ℝ) * (∑ _ ∈ s, (1 : ℝ) ^ 2) ^ (4 / 5 : ℝ) := by
  simp only [Real.one_rpow, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← Real.rpow_add_of_nonneg (Nat.cast_nonneg _) (by norm_num) (by norm_num)]
  norm_num

end Mettapedia.Analysis.FinitePowerInterpolation
