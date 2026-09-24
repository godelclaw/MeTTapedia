import Mettapedia.Analysis.DyadicAnnulusCorrection

/-! Boundary, zero-mode, and exact-reconstruction regressions for the dyadic partition. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DyadicAnnulusTests

open DyadicAnnulus
open scoped ContDiff

/-- The old bands double-count a unit frequency. -/
example : normalizer (1 : ℝ) = 2 := normalizer_eq_two_of_norm_eq_one _ (by norm_num)

/-- The new unit-frequency weight is one half, not one. -/
example : normalizedCutoff (1 : ℝ) = 1 / 2 := normalizedCutoff_eq_half_of_norm_eq_one _ (by norm_num)

example : normalizedCutoff (2 : ℝ) = 1 / 2 := by
  have h := normalizer_smul (E := ℝ) 1 1
  norm_num [normalizer_eq_two_of_norm_eq_one (1 : ℝ) (by norm_num)] at h
  rw [normalizedCutoff, h, SmoothAnnulus.cutoff_eq_one 2 (by norm_num) (by norm_num)]

/-- The support endpoints vanish exactly. -/
example : normalizedCutoff (1 / 2 : ℝ) = 0 ∧ normalizedCutoff (4 : ℝ) = 0 :=
  ⟨normalizedCutoff_eq_zero_of_norm_le _ (by norm_num),
    normalizedCutoff_eq_zero_of_le_norm _ (by norm_num)⟩

/-- At zero the annular sum is zero, while the smooth correction is one. -/
example : (∑' z : ℤ, normalizedCutoff ((2 : ℝ) ^ z • (0 : ℝ))) = 0 ∧
    smoothCorrection (0 : ℝ) = 1 := by simp

/-- A very small input is still reconstructed by the nonnegative bands. -/
example : (∑' n : ℕ, normalizedCutoff ((2 : ℝ) ^ n • (1 / 1024 : ℝ))) = 1 :=
  tsum_normalizedCutoff_nat _ (by norm_num) (by norm_num)

/-- A negative input uses the same radial normalization. -/
example : (∑' z : ℤ, normalizedCutoff ((2 : ℝ) ^ z • (-7 : ℝ))) = 1 :=
  tsum_normalizedCutoff _ (by norm_num)

example : ContDiff ℝ ∞ (normalizedCutoff (E := ℝ)) ∧
    ContDiff ℝ ∞ (smoothCorrection (E := ℝ)) :=
  ⟨contDiff_normalizedCutoff, contDiff_smoothCorrection⟩

end Mettapedia.Analysis.DyadicAnnulusTests

#print axioms Mettapedia.Analysis.DyadicAnnulus.smoothCorrection_eq_one_of_norm_le
#print axioms Mettapedia.Analysis.DyadicAnnulus.smoothCorrection_zero
#print axioms Mettapedia.Analysis.DyadicAnnulus.smoothCorrection_eq_inv_of_cutoff_ne_zero
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff_eq_mul_smoothCorrection
#print axioms Mettapedia.Analysis.DyadicAnnulus.smoothCorrection_nonneg
#print axioms Mettapedia.Analysis.DyadicAnnulus.smoothCorrection_le_one
#print axioms Mettapedia.Analysis.DyadicAnnulus.contDiff_smoothCorrection
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff_zero
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff_nonneg
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff_le_cutoff
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff_le_one
#print axioms Mettapedia.Analysis.DyadicAnnulus.cutoff_ne_zero_of_normalizedCutoff_ne_zero
#print axioms Mettapedia.Analysis.DyadicAnnulus.norm_bounds_of_normalizedCutoff_ne_zero
#print axioms Mettapedia.Analysis.DyadicAnnulus.buffer_eq_one_of_normalizedCutoff_ne_zero
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff_eq_zero_of_norm_le
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff_eq_zero_of_le_norm
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff_smul
#print axioms Mettapedia.Analysis.DyadicAnnulus.summable_normalizedCutoff
#print axioms Mettapedia.Analysis.DyadicAnnulus.tsum_normalizedCutoff
#print axioms Mettapedia.Analysis.DyadicAnnulus.exists_finset_support_normalizedCutoff
#print axioms Mettapedia.Analysis.DyadicAnnulus.contDiff_normalizedCutoff
#print axioms Mettapedia.Analysis.DyadicAnnulus.hasCompactSupport_normalizedCutoff
#print axioms Mettapedia.Analysis.DyadicAnnulus.tsupport_normalizedCutoff_subset
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff_smul_eq_zero_of_neg
#print axioms Mettapedia.Analysis.DyadicAnnulus.summable_normalizedCutoff_nat
#print axioms Mettapedia.Analysis.DyadicAnnulus.tsum_normalizedCutoff_nat
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizer_eq_two_of_norm_eq_one
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff_eq_half_of_norm_eq_one
#print axioms Mettapedia.Analysis.DyadicAnnulus.band_zero
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizer_zero
#print axioms Mettapedia.Analysis.DyadicAnnulus.band_nonneg
#print axioms Mettapedia.Analysis.DyadicAnnulus.band_le_one
#print axioms Mettapedia.Analysis.DyadicAnnulus.norm_dyadic_smul
#print axioms Mettapedia.Analysis.DyadicAnnulus.band_smul
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizer_smul
#print axioms Mettapedia.Analysis.DyadicAnnulus.band_eq_zero_of_scaled_norm_le
#print axioms Mettapedia.Analysis.DyadicAnnulus.band_eq_zero_of_le_scaled_norm
#print axioms Mettapedia.Analysis.DyadicAnnulus.band_eq_zero_of_not_mem_three
#print axioms Mettapedia.Analysis.DyadicAnnulus.band_eq_zero_of_not_mem_five
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizer_eq_sum_three
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizer_eq_sum_five
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizer_bounds_of_normalized
#print axioms Mettapedia.Analysis.DyadicAnnulus.exists_normalizing_scale
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizer_bounds
#print axioms Mettapedia.Analysis.DyadicAnnulus.normalizer_nonneg
#print axioms Mettapedia.Analysis.DyadicAnnulus.exists_finset_support_band
#print axioms Mettapedia.Analysis.DyadicAnnulus.summable_band
#print axioms Mettapedia.Analysis.DyadicAnnulus.contDiff_band
#print axioms Mettapedia.Analysis.DyadicAnnulus.contDiffAt_normalizer
