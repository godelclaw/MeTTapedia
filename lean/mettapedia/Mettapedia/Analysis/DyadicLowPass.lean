import Mettapedia.Analysis.DyadicAnnulusPartition

/-!
# The low-pass multiplier assembled from the normalized dyadic annuli

The value at the origin is filled with one. Away from zero, the multiplier
is the sum of all annuli at or below the reference scale. It is contractive,
equals one on the unit ball, and vanishes outside the ball of radius four.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DyadicLowPass

open DyadicAnnulus
open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

def multiplier (x : E) : ℝ := if x = 0 then 1 else ∑' n : ℕ, normalizedCutoff ((2 : ℝ) ^ n • x)

@[simp] theorem multiplier_zero : multiplier (0 : E) = 1 := by simp [multiplier]

theorem multiplier_nonneg (x : E) : 0 ≤ multiplier x := by
  unfold multiplier
  split_ifs
  · norm_num
  · exact tsum_nonneg (fun _ ↦ normalizedCutoff_nonneg _)

theorem multiplier_le_one (x : E) : multiplier x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h := tsum_nat_add_neg_add_one (summable_normalizedCutoff x)
  rw [tsum_normalizedCutoff x hx] at h
  simp only [zpow_natCast] at h
  have hsneg : Summable (fun n : ℕ ↦
      normalizedCutoff ((2 : ℝ) ^ (-(↑n + 1) : ℤ) • x)) :=
    (summable_normalizedCutoff x).comp_injective
      (show Function.Injective (fun n : ℕ ↦ (-(↑n + 1) : ℤ)) from by
        intro a b hab
        change -((a : ℤ) + 1) = -((b : ℤ) + 1) at hab
        omega)
  rw [(summable_normalizedCutoff_nat x).tsum_add hsneg] at h
  have hn : 0 ≤ ∑' n : ℕ, normalizedCutoff ((2 : ℝ) ^ (-(↑n + 1) : ℤ) • x) :=
    tsum_nonneg (fun _ ↦ normalizedCutoff_nonneg _)
  rw [multiplier, if_neg hx]
  linarith

theorem multiplier_eq_one_of_norm_le (x : E) (hx : ‖x‖ ≤ 1) : multiplier x = 1 := by
  by_cases hzero : x = 0
  · simp [hzero]
  · rw [multiplier, if_neg hzero]
    exact tsum_normalizedCutoff_nat x hzero hx

theorem multiplier_eq_zero_of_le_norm (x : E) (hx : 4 ≤ ‖x‖) : multiplier x = 0 := by
  have hzero : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    norm_num at hx
  rw [multiplier, if_neg hzero]
  have hz (n : ℕ) : normalizedCutoff ((2 : ℝ) ^ n • x) = 0 := by
    apply normalizedCutoff_eq_zero_of_le_norm
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ n)]
    exact hx.trans (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num)))
  simp only [hz, tsum_zero]

theorem multiplier_eq_cutoff_add (x : E) (hx : x ≠ 0) :
    multiplier x = normalizedCutoff x + multiplier ((2 : ℝ) • x) := by
  rw [multiplier, if_neg hx, (summable_normalizedCutoff_nat x).tsum_eq_zero_add]
  simp only [pow_zero, one_smul]
  rw [multiplier, if_neg (smul_ne_zero (by norm_num) hx)]
  simp only [pow_succ, smul_smul]

theorem multiplier_eq_half_of_norm_eq_two (x : E) (hx : ‖x‖ = 2) :
    multiplier x = 1 / 2 := by
  have hzero : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; norm_num at hx
  have hn : normalizer x = 2 := by
    have hs := normalizer_smul (-1 : ℤ) x
    have hu : ‖(2 : ℝ) ^ (-1 : ℤ) • x‖ = 1 := by
      rw [norm_dyadic_smul, hx]
      norm_num
    exact hs.symm.trans (normalizer_eq_two_of_norm_eq_one _ hu)
  rw [multiplier_eq_cutoff_add x hzero,
    multiplier_eq_zero_of_le_norm _ (by rw [norm_smul, hx]; norm_num),
    add_zero, normalizedCutoff, SmoothAnnulus.cutoff_eq_one x (by linarith) hx.le, hn]

/-- The annular sum acts as the filled low-pass multiplier whenever the
zero-frequency amplitude vanishes. This does not assert a partition at zero. -/
theorem hasSum_mul {x : E} (a : ℝ) (hzero : x = 0 → a = 0) :
    HasSum (fun n : ℕ ↦ normalizedCutoff ((2 : ℝ) ^ n • x) * a) (multiplier x * a) := by
  by_cases hx : x = 0
  · simp [hzero hx]
  · rw [multiplier, if_neg hx]
    exact (summable_normalizedCutoff_nat x).hasSum.mul_right a

theorem hasSum_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x : E} (a : F) (hzero : x = 0 → a = 0) :
    HasSum (fun n : ℕ ↦ normalizedCutoff ((2 : ℝ) ^ n • x) • a) (multiplier x • a) := by
  by_cases hx : x = 0
  · simp [hzero hx]
  · rw [multiplier, if_neg hx]
    exact (summable_normalizedCutoff_nat x).hasSum.smul_const a

end Mettapedia.Analysis.DyadicLowPass
