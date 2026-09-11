import Mettapedia.Analysis.DyadicAnnulus
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# A smooth exact dyadic partition away from zero

Dividing the annular cutoff by its dyadic sum gives an exact partition of
unity on the punctured space. Each point meets only finitely many bands.
The negative bands vanish in the unit ball, so the nonnegative-indexed
family already sums to one there. Zero is deliberately excluded.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DyadicAnnulus

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

def normalizedCutoff (x : E) : ℝ := SmoothAnnulus.cutoff x / normalizer x

@[simp] theorem normalizedCutoff_zero : normalizedCutoff (0 : E) = 0 := by
  simp [normalizedCutoff]

theorem normalizedCutoff_nonneg (x : E) : 0 ≤ normalizedCutoff x :=
  div_nonneg (SmoothAnnulus.cutoff_nonneg x) (normalizer_nonneg x)

theorem normalizedCutoff_le_cutoff (x : E) : normalizedCutoff x ≤ SmoothAnnulus.cutoff x := by
  by_cases hx : x = 0
  · simp [hx]
  exact div_le_self (SmoothAnnulus.cutoff_nonneg x) (normalizer_bounds x hx).1

theorem normalizedCutoff_le_one (x : E) : normalizedCutoff x ≤ 1 :=
  (normalizedCutoff_le_cutoff x).trans (SmoothAnnulus.cutoff_le_one x)

theorem cutoff_ne_zero_of_normalizedCutoff_ne_zero (x : E) (hx : normalizedCutoff x ≠ 0) :
    SmoothAnnulus.cutoff x ≠ 0 := fun h ↦ hx (by simp [normalizedCutoff, h])

theorem norm_bounds_of_normalizedCutoff_ne_zero (x : E) (hx : normalizedCutoff x ≠ 0) :
    1 / 2 < ‖x‖ ∧ ‖x‖ < 4 :=
  SmoothAnnulus.norm_bounds_of_cutoff_ne_zero x (cutoff_ne_zero_of_normalizedCutoff_ne_zero x hx)

theorem buffer_eq_one_of_normalizedCutoff_ne_zero (x : E) (hx : normalizedCutoff x ≠ 0) :
    SmoothAnnulus.buffer x = 1 :=
  SmoothAnnulus.buffer_eq_one_of_cutoff_ne_zero x (cutoff_ne_zero_of_normalizedCutoff_ne_zero x hx)

theorem normalizedCutoff_eq_zero_of_norm_le (x : E) (hx : ‖x‖ ≤ 1 / 2) :
    normalizedCutoff x = 0 := by
  by_contra hn
  exact (not_lt_of_ge hx) (norm_bounds_of_normalizedCutoff_ne_zero x hn).1

theorem normalizedCutoff_eq_zero_of_le_norm (x : E) (hx : 4 ≤ ‖x‖) :
    normalizedCutoff x = 0 := by
  by_contra hn
  exact (not_lt_of_ge hx) (norm_bounds_of_normalizedCutoff_ne_zero x hn).2

theorem normalizedCutoff_smul (z : ℤ) (x : E) :
    normalizedCutoff ((2 : ℝ) ^ z • x) = band z x / normalizer x := by
  simp only [normalizedCutoff, normalizer_smul, band]

theorem summable_normalizedCutoff (x : E) :
    Summable (fun z : ℤ ↦ normalizedCutoff ((2 : ℝ) ^ z • x)) := by
  simpa only [normalizedCutoff_smul] using (summable_band x).div_const (normalizer x)

theorem tsum_normalizedCutoff (x : E) (hx : x ≠ 0) :
    ∑' z : ℤ, normalizedCutoff ((2 : ℝ) ^ z • x) = 1 := by
  simp only [normalizedCutoff_smul, tsum_div_const]
  exact div_self (ne_of_gt (lt_of_lt_of_le (by norm_num) (normalizer_bounds x hx).1))

theorem exists_finset_support_normalizedCutoff (x : E) :
    ∃ S : Finset ℤ, ∀ z ∉ S, normalizedCutoff ((2 : ℝ) ^ z • x) = 0 := by
  obtain ⟨S, hS⟩ := exists_finset_support_band x
  exact ⟨S, fun z hz ↦ by rw [normalizedCutoff_smul, hS z hz, zero_div]⟩

@[fun_prop] theorem contDiff_normalizedCutoff : ContDiff ℝ ∞ (normalizedCutoff (E := E)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hU : ∀ᶠ y : E in 𝓝 0, y ∈ Metric.ball 0 (1 / 2 : ℝ) :=
      Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [hU] with y hy
    have hy' : ‖y‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hy
    exact normalizedCutoff_eq_zero_of_norm_le y hy'.le
  · exact SmoothAnnulus.contDiff_cutoff.contDiffAt.div (contDiffAt_normalizer x hx)
      (ne_of_gt (lt_of_lt_of_le (by norm_num) (normalizer_bounds x hx).1))

theorem hasCompactSupport_normalizedCutoff [FiniteDimensional ℝ E] :
    HasCompactSupport (normalizedCutoff (E := E)) := by
  change HasCompactSupport (fun x : E ↦ SmoothAnnulus.cutoff x / normalizer x)
  simp_rw [div_eq_mul_inv]
  exact (SmoothAnnulus.hasCompactSupport_cutoff (E := E)).mul_right

theorem tsupport_normalizedCutoff_subset :
    tsupport (normalizedCutoff (E := E)) ⊆ Metric.closedBall 0 4 := by
  exact (tsupport_mul_subset_left (f := SmoothAnnulus.cutoff) (g := fun x : E ↦
    (normalizer x)⁻¹)).trans SmoothAnnulus.tsupport_cutoff_subset

theorem normalizedCutoff_smul_eq_zero_of_neg (x : E) (hx : ‖x‖ ≤ 1) (z : ℤ) (hz : z < 0) :
    normalizedCutoff ((2 : ℝ) ^ z • x) = 0 := by
  apply normalizedCutoff_eq_zero_of_norm_le
  rw [norm_dyadic_smul]
  have hp : (2 : ℝ) ^ z ≤ 1 / 2 := by
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show z ≤ -1 by omega)
    norm_num at h
    exact h
  calc
    _ ≤ (1 / 2 : ℝ) * 1 := mul_le_mul hp hx (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem summable_normalizedCutoff_nat (x : E) :
    Summable (fun n : ℕ ↦ normalizedCutoff ((2 : ℝ) ^ n • x)) := by
  simpa only [Function.comp_def, zpow_natCast] using (summable_normalizedCutoff x).comp_injective
    (Nat.cast_injective (R := ℤ))

theorem tsum_normalizedCutoff_nat (x : E) (hx : x ≠ 0) (hball : ‖x‖ ≤ 1) :
    ∑' n : ℕ, normalizedCutoff ((2 : ℝ) ^ n • x) = 1 := by
  have hz (n : ℕ) : normalizedCutoff ((2 : ℝ) ^ (-(↑n + 1) : ℤ) • x) = 0 :=
    normalizedCutoff_smul_eq_zero_of_neg x hball _ (by omega)
  have h := tsum_nat_add_neg_add_one (summable_normalizedCutoff x)
  simpa only [hz, add_zero, zpow_natCast, tsum_normalizedCutoff x hx] using h

theorem normalizer_eq_two_of_norm_eq_one (x : E) (hx : ‖x‖ = 1) : normalizer x = 2 := by
  rw [normalizer_eq_sum_three x (by linarith) (by linarith)]
  have hm : band (-1) x = 0 := band_eq_zero_of_scaled_norm_le _ _ (by rw [hx]; norm_num)
  have h0 : band 0 x = 1 := by
    simpa [band] using SmoothAnnulus.cutoff_eq_one x (by linarith) (by linarith)
  have h1 : band 1 x = 1 := by
    apply SmoothAnnulus.cutoff_eq_one <;> rw [norm_dyadic_smul, hx] <;> norm_num
  rw [show Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} by decide]
  norm_num [hm, h0, h1]

theorem normalizedCutoff_eq_half_of_norm_eq_one (x : E) (hx : ‖x‖ = 1) :
    normalizedCutoff x = 1 / 2 := by
  rw [normalizedCutoff, normalizer_eq_two_of_norm_eq_one x hx,
    SmoothAnnulus.cutoff_eq_one x (by linarith) (by linarith)]

end Mettapedia.Analysis.DyadicAnnulus
