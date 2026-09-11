import Mettapedia.Analysis.GeometricMinSeries

/-! Degenerate costs, a sharp cutoff, and non-dyadic ratios. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.GeometricMinSeriesTests

open GeometricMinSeries

example : Summable (fun m : ℕ ↦ min (3 * (1 / 2 : ℝ) ^ m) 0) :=
  summable_min (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (∑' m : ℕ, min (8 * (1 / 2 : ℝ) ^ m) 1) = 5 := by
  have hs := summable_min (A := (8 : ℝ)) (D := 1) (q := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [← hs.sum_add_tsum_nat_add 3]
  have ht (m : ℕ) : min (8 * (1 / 2 : ℝ) ^ (m + 3)) 1 = (1 / 2 : ℝ) ^ m := by
    have hp : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have he : 8 * (1 / 2 : ℝ) ^ (m + 3) = (1 / 2 : ℝ) ^ m := by rw [pow_add]; ring
    rw [he, min_eq_left hp]
  simp_rw [ht]
  rw [hasSum_geometric_two.tsum_eq]
  norm_num [Fin.sum_univ_succ, Finset.sum_range_succ]

example (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    (∑' m : ℕ, min (A * (1 / 3 : ℝ) ^ m) D) ≤
      D * (5 / 2 + Real.log (1 + A / D) / Real.log 3) := by
  have h := tsum_min_le_logarithmic hA hD
    (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1)
  have hlog : -Real.log (1 / 3 : ℝ) = Real.log 3 := by rw [one_div, Real.log_inv, neg_neg]
  rw [hlog] at h
  norm_num at h
  exact h

example : Summable (fun j : ℕ ↦ ∑' m : ℕ,
    (1 / 2 : ℝ) ^ j * min (8 * (1 / 2 : ℝ) ^ m) 1) := by
  have h := iterated_tsum_le_logarithmic_of_nonneg_of_le
    (a := fun j m ↦ (1 / 2 : ℝ) ^ j * min (8 * (1 / 2 : ℝ) ^ m) 1)
    (C := (1 : ℝ)) (A := 8) (D := 1) (by norm_num) (by norm_num) (by norm_num)
    (fun j m ↦ by positivity)
    (fun j m ↦ by simp)
  exact h.2.1

example (a : ℕ → ℕ → ℝ) (ha : ∀ j m, 0 ≤ a j m)
    (hzero : ∀ j m, a j m ≤ 0) :
    (∀ j, Summable (a j)) ∧ Summable (fun j ↦ ∑' m, a j m) ∧ (∑' j, ∑' m, a j m) ≤ 0 := by
  have h := iterated_tsum_le_logarithmic_of_nonneg_of_le
    (C := (2 : ℝ)) (A := 1) (D := 0) (by norm_num) (by norm_num) (by norm_num) ha
    (fun j m ↦ by simpa [min_eq_right (by positivity : (0 : ℝ) ≤ 1 * (1 / 2 : ℝ) ^ m)] using hzero j m)
  simpa using h

end Mettapedia.Analysis.GeometricMinSeriesTests

#print axioms Mettapedia.Analysis.GeometricMinSeries.summable_min
#print axioms Mettapedia.Analysis.GeometricMinSeries.tsum_min_le_cutoff
#print axioms Mettapedia.Analysis.GeometricMinSeries.exists_logarithmic_cutoff
#print axioms Mettapedia.Analysis.GeometricMinSeries.tsum_min_le_logarithmic
#print axioms Mettapedia.Analysis.GeometricMinSeries.tsum_min_half_pow_le
#print axioms Mettapedia.Analysis.GeometricMinSeries.tsum_le_logarithmic_of_nonneg_of_le
#print axioms Mettapedia.Analysis.GeometricMinSeries.iterated_tsum_le_logarithmic_of_nonneg_of_le
