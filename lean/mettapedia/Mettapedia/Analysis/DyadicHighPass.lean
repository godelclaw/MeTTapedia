import Mettapedia.Analysis.DyadicLowPass

/-! The exact high-input dyadic partition and its low-pass complement. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DyadicHighPass

open DyadicAnnulus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

def multiplier (x : E) : ℝ := 1 - DyadicLowPass.multiplier ((2 : ℝ) • x)

@[simp] theorem multiplier_zero : multiplier (0 : E) = 0 := by simp [multiplier]

theorem multiplier_nonneg (x : E) : 0 ≤ multiplier x :=
  sub_nonneg.mpr (DyadicLowPass.multiplier_le_one _)

theorem multiplier_le_one (x : E) : multiplier x ≤ 1 :=
  sub_le_self _ (DyadicLowPass.multiplier_nonneg _)

theorem multiplier_eq_zero_of_norm_le (x : E) (hx : ‖x‖ ≤ 1 / 2) : multiplier x = 0 := by
  rw [multiplier, DyadicLowPass.multiplier_eq_one_of_norm_le]
  · ring
  · rw [norm_smul]
    norm_num only [Real.norm_ofNat]
    linarith

theorem multiplier_eq_one_of_le_norm (x : E) (hx : 2 ≤ ‖x‖) : multiplier x = 1 := by
  rw [multiplier, DyadicLowPass.multiplier_eq_zero_of_le_norm]
  · ring
  · rw [norm_smul]
    norm_num only [Real.norm_ofNat]
    linarith

theorem multiplier_eq_half_of_norm_eq_one (x : E) (hx : ‖x‖ = 1) :
    multiplier x = 1 / 2 := by
  rw [multiplier, DyadicLowPass.multiplier_eq_half_of_norm_eq_two]
  · norm_num
  · simp [norm_smul, hx]

theorem summable_annuli (x : E) :
    Summable (fun j : ℕ ↦ normalizedCutoff ((1 / 2 : ℝ) ^ j • x)) := by
  have hs := (summable_normalizedCutoff x).comp_injective
    (show Function.Injective (fun j : ℕ ↦ -(j : ℤ)) from by
      intro a b h
      change -(a : ℤ) = -(b : ℤ) at h
      omega)
  simpa only [Function.comp_def, zpow_neg, zpow_natCast, ← inv_pow, one_div] using hs

theorem hasSum_annuli (x : E) :
    HasSum (fun j : ℕ ↦ normalizedCutoff ((1 / 2 : ℝ) ^ j • x)) (multiplier x) := by
  by_cases hx : x = 0
  · subst x; simp
  have hs : Summable (fun z : ℤ ↦ normalizedCutoff ((2 : ℝ) ^ (-z) • x)) :=
    (summable_normalizedCutoff x).comp_injective (neg_injective (G := ℤ))
  have ht : (∑' z : ℤ, normalizedCutoff ((2 : ℝ) ^ (-z) • x)) = 1 := by
    exact ((Equiv.neg ℤ).tsum_eq (fun z ↦ normalizedCutoff ((2 : ℝ) ^ z • x))).trans
      (tsum_normalizedCutoff x hx)
  have h := tsum_nat_add_neg_add_one hs
  rw [ht] at h
  simp only [neg_neg, zpow_neg, zpow_natCast, ← inv_pow, ← Int.natCast_add_one,
    zpow_natCast, pow_succ, mul_smul] at h
  have hp := summable_normalizedCutoff_nat ((2 : ℝ) • x)
  have hm := summable_annuli x
  simp only [one_div] at hm
  rw [hm.tsum_add hp] at h
  have hl : DyadicLowPass.multiplier ((2 : ℝ) • x) =
      ∑' n : ℕ, normalizedCutoff ((2 : ℝ) ^ n • ((2 : ℝ) • x)) := by
    rw [DyadicLowPass.multiplier, if_neg (smul_ne_zero (by norm_num) hx)]
  have he : (∑' j : ℕ, normalizedCutoff ((1 / 2 : ℝ) ^ j • x)) = multiplier x := by
    rw [multiplier, hl]
    simp only [one_div]
    linarith
  exact he ▸ (summable_annuli x).hasSum

end Mettapedia.Analysis.DyadicHighPass
