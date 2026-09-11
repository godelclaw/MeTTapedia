import Mettapedia.Analysis.SmoothAnnulus
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Exact normalization of dyadic annuli

The sum of the dyadic annular cutoffs is positive away from zero and invariant
under dyadic scaling. After normalization to the unit annulus, only three
indices contribute. Five fixed indices suffice in a neighborhood, giving
smoothness of the normalizer away from zero.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DyadicAnnulus

open SmoothAnnulus Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

def band (z : ℤ) (x : E) : ℝ := cutoff ((2 : ℝ) ^ z • x)
def normalizer (x : E) : ℝ := ∑' z : ℤ, band z x

@[simp] theorem band_zero (z : ℤ) : band z (0 : E) = 0 := by simp [band]
@[simp] theorem normalizer_zero : normalizer (0 : E) = 0 := by simp [normalizer]

theorem band_nonneg (z : ℤ) (x : E) : 0 ≤ band z x := cutoff_nonneg _
theorem band_le_one (z : ℤ) (x : E) : band z x ≤ 1 := cutoff_le_one _

omit [HasContDiffBump E] in
theorem norm_dyadic_smul (z : ℤ) (x : E) : ‖(2 : ℝ) ^ z • x‖ = (2 : ℝ) ^ z * ‖x‖ := by
  rw [norm_smul, Real.norm_of_nonneg (le_of_lt (zpow_pos (by norm_num) _))]

theorem band_smul (z m : ℤ) (x : E) : band z ((2 : ℝ) ^ m • x) = band (z + m) x := by
  simp only [band, smul_smul, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

theorem normalizer_smul (m : ℤ) (x : E) : normalizer ((2 : ℝ) ^ m • x) = normalizer x := by
  simp only [normalizer, band_smul]
  exact (Equiv.addRight m).tsum_eq (fun z : ℤ ↦ band z x)

theorem band_eq_zero_of_scaled_norm_le (z : ℤ) (x : E)
    (h : (2 : ℝ) ^ z * ‖x‖ ≤ 1 / 2) : band z x = 0 := by
  by_contra hn
  have hb := (norm_bounds_of_cutoff_ne_zero _ hn).1
  rw [norm_dyadic_smul] at hb
  linarith

theorem band_eq_zero_of_le_scaled_norm (z : ℤ) (x : E)
    (h : 4 ≤ (2 : ℝ) ^ z * ‖x‖) : band z x = 0 := by
  by_contra hn
  have hb := (norm_bounds_of_cutoff_ne_zero _ hn).2
  rw [norm_dyadic_smul] at hb
  linarith

theorem band_eq_zero_of_not_mem_three (x : E) (hlo : 1 ≤ ‖x‖) (hhi : ‖x‖ ≤ 2)
    (z : ℤ) (hz : z ∉ Finset.Icc (-1 : ℤ) 1) : band z x = 0 := by
  have hcases : z ≤ -2 ∨ 2 ≤ z := by
    simp only [Finset.mem_Icc] at hz
    omega
  rcases hcases with hz | hz
  · apply band_eq_zero_of_scaled_norm_le
    have hp : (2 : ℝ) ^ z ≤ 1 / 4 := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hz
      norm_num at h
      exact h
    calc
      _ ≤ (1 / 4 : ℝ) * 2 := mul_le_mul hp hhi (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  · apply band_eq_zero_of_le_scaled_norm
    have hp : (4 : ℝ) ≤ (2 : ℝ) ^ z := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hz
      norm_num at h
      exact h
    calc
      _ = (4 : ℝ) * 1 := by norm_num
      _ ≤ _ := mul_le_mul hp hlo (by norm_num) (le_of_lt (zpow_pos (by norm_num) _))

theorem band_eq_zero_of_not_mem_five (x : E) (hlo : 1 / 2 ≤ ‖x‖) (hhi : ‖x‖ ≤ 4)
    (z : ℤ) (hz : z ∉ Finset.Icc (-2 : ℤ) 2) : band z x = 0 := by
  have hcases : z ≤ -3 ∨ 3 ≤ z := by
    simp only [Finset.mem_Icc] at hz
    omega
  rcases hcases with hz | hz
  · apply band_eq_zero_of_scaled_norm_le
    have hp : (2 : ℝ) ^ z ≤ 1 / 8 := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hz
      norm_num at h
      exact h
    calc
      _ ≤ (1 / 8 : ℝ) * 4 := mul_le_mul hp hhi (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  · apply band_eq_zero_of_le_scaled_norm
    have hp : (8 : ℝ) ≤ (2 : ℝ) ^ z := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hz
      norm_num at h
      exact h
    calc
      _ = (8 : ℝ) * (1 / 2) := by norm_num
      _ ≤ _ := mul_le_mul hp hlo (by norm_num) (le_of_lt (zpow_pos (by norm_num) _))

theorem normalizer_eq_sum_three (x : E) (hlo : 1 ≤ ‖x‖) (hhi : ‖x‖ ≤ 2) :
    normalizer x = ∑ z ∈ Finset.Icc (-1 : ℤ) 1, band z x :=
  tsum_eq_sum (band_eq_zero_of_not_mem_three x hlo hhi)

theorem normalizer_eq_sum_five (x : E) (hlo : 1 / 2 ≤ ‖x‖) (hhi : ‖x‖ ≤ 4) :
    normalizer x = ∑ z ∈ Finset.Icc (-2 : ℤ) 2, band z x :=
  tsum_eq_sum (band_eq_zero_of_not_mem_five x hlo hhi)

theorem normalizer_bounds_of_normalized (x : E) (hlo : 1 ≤ ‖x‖) (hhi : ‖x‖ ≤ 2) :
    1 ≤ normalizer x ∧ normalizer x ≤ 3 := by
  rw [normalizer_eq_sum_three x hlo hhi]
  constructor
  · have h0 : band 0 x = 1 := by simpa [band] using cutoff_eq_one x hlo hhi
    calc
      1 = band 0 x := h0.symm
      _ ≤ _ := Finset.single_le_sum (fun z _ ↦ band_nonneg z x) (by norm_num)
  · calc
      _ ≤ ∑ _z ∈ Finset.Icc (-1 : ℤ) 1, (1 : ℝ) := Finset.sum_le_sum (fun z _ ↦ band_le_one z x)
      _ = 3 := by norm_num [Int.toNat]

omit [HasContDiffBump E] in
theorem exists_normalizing_scale (x : E) (hx : x ≠ 0) :
    ∃ m : ℤ, 1 ≤ ‖(2 : ℝ) ^ m • x‖ ∧ ‖(2 : ℝ) ^ m • x‖ < 2 := by
  obtain ⟨n, hn0, hn1⟩ := exists_mem_Ico_zpow (norm_pos_iff.mpr hx) (by norm_num : (1 : ℝ) < 2)
  have hp : 0 < (2 : ℝ) ^ n := zpow_pos (by norm_num) _
  have he : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := by
    rw [zpow_add₀ (by norm_num)]
    norm_num
  rw [he] at hn1
  refine ⟨-n, ?_, ?_⟩ <;> rw [norm_dyadic_smul, zpow_neg]
  · calc
      1 = ((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ n := (inv_mul_cancel₀ hp.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hn0 (le_of_lt (inv_pos.mpr hp))
  · calc
      _ < ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n * 2) := mul_lt_mul_of_pos_left hn1 (inv_pos.mpr hp)
      _ = 2 := by rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

theorem normalizer_bounds (x : E) (hx : x ≠ 0) : 1 ≤ normalizer x ∧ normalizer x ≤ 3 := by
  obtain ⟨m, hm0, hm1⟩ := exists_normalizing_scale x hx
  simpa only [normalizer_smul] using normalizer_bounds_of_normalized _ hm0 hm1.le

theorem normalizer_nonneg (x : E) : 0 ≤ normalizer x := tsum_nonneg (fun z ↦ band_nonneg z x)

theorem exists_finset_support_band (x : E) : ∃ S : Finset ℤ, ∀ z ∉ S, band z x = 0 := by
  classical
  by_cases hx : x = 0
  · exact ⟨∅, fun z _ ↦ by simp [hx]⟩
  obtain ⟨m, hm0, hm1⟩ := exists_normalizing_scale x hx
  refine ⟨(Finset.Icc (-1 : ℤ) 1).image (fun z ↦ z + m), ?_⟩
  intro z hz
  have hz' : z - m ∉ Finset.Icc (-1 : ℤ) 1 := by
    intro h
    apply hz
    exact Finset.mem_image.mpr ⟨z - m, h, sub_add_cancel z m⟩
  have h := band_eq_zero_of_not_mem_three ((2 : ℝ) ^ m • x) hm0 hm1.le (z - m) hz'
  simpa only [band_smul, sub_add_cancel] using h

theorem summable_band (x : E) : Summable (fun z : ℤ ↦ band z x) := by
  obtain ⟨S, hS⟩ := exists_finset_support_band x
  exact (hasSum_sum_of_ne_finset_zero hS).summable

@[fun_prop] theorem contDiff_band (z : ℤ) : ContDiff ℝ ∞ (band (E := E) z) :=
  contDiff_cutoff.comp (contDiff_const.smul contDiff_id)

theorem contDiffAt_normalizer (x : E) (hx : x ≠ 0) : ContDiffAt ℝ ∞ normalizer x := by
  obtain ⟨m, hm0, hm1⟩ := exists_normalizing_scale x hx
  let f : E → ℝ := fun y ↦ ∑ z ∈ Finset.Icc (-2 : ℤ) 2, band z ((2 : ℝ) ^ m • y)
  have hf : ContDiff ℝ ∞ f := ContDiff.sum (fun z _ ↦
    (contDiff_band z).comp (contDiff_const.smul contDiff_id))
  have hc : Continuous (fun y : E ↦ ‖(2 : ℝ) ^ m • y‖) := by fun_prop
  have hU : ∀ᶠ y in 𝓝 x, ‖(2 : ℝ) ^ m • y‖ ∈ Ioo (1 / 2 : ℝ) 4 :=
    (hc.isOpen_preimage _ isOpen_Ioo).mem_nhds (by constructor <;> linarith)
  apply hf.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hU] with y hy
  dsimp only [f]
  rw [← normalizer_smul m y, normalizer_eq_sum_five _ hy.1.le hy.2.le]

end Mettapedia.Analysis.DyadicAnnulus
