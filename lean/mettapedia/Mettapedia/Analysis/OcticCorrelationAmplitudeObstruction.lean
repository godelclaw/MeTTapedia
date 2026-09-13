import Mettapedia.Analysis.OcticKernelCorrelation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Amplitude imbalance in pure correlation curvature

A frozen receiver can weight the source's second variation by its own fourth
power. Even with both endpoint amplitudes at most one and unit total local
weighted-gradient cost, the negative pure curvature is unbounded. This rules
out a pointwise one-endpoint payment; it is not an integrated field estimate
or a self-consistent Navier–Stokes counterexample.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.OcticCorrelationAmplitudeObstruction

open OcticKernelCorrelation
open scoped RealInnerProductSpace

def negativeIdentity : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ

def localWeightedGradient (a b v w : ℝ) : ℝ := |a| ^ 6 * |v| ^ 2 + |b| ^ 6 * |w| ^ 2

theorem norm_negativeIdentity : ‖negativeIdentity‖ = 1 := by
  simp [negativeIdentity]

theorem pureCurvature_family (r : ℝ) (hr : 0 < r) :
    pureCurvature negativeIdentity r⁻¹ 1 (r ^ 3) 0 = -12 * r ^ 4 := by
  simp only [pureCurvature, sourceCurvature, sourceForm, amplitudeCurvature, negativeIdentity,
    neg_apply, ContinuousLinearMap.id_apply, Real.inner_apply,
    Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos hr, abs_one, inner_zero_right]
  field_simp
  ring

theorem localWeightedGradient_family (r : ℝ) (hr : 0 < r) :
    localWeightedGradient r⁻¹ 1 (r ^ 3) 0 = 1 := by
  simp only [localWeightedGradient, abs_inv, abs_pow, abs_of_pos hr, abs_one, abs_zero]
  field_simp
  ring

theorem mixedCurvature_family (r : ℝ) :
    mixedCurvature negativeIdentity r⁻¹ 1 (r ^ 3) 0 = 0 := by
  simp [mixedCurvature, amplitudeRate]

theorem exists_unbounded_negative_pureCurvature (C : ℝ) :
    ∃ a b v w : ℝ, |a| ≤ 1 ∧ |b| ≤ 1 ∧ localWeightedGradient a b v w = 1 ∧
      mixedCurvature negativeIdentity a b v w = 0 ∧
      C < -pureCurvature negativeIdentity a b v w := by
  let r : ℝ := |C| + 1
  have hr1 : 1 ≤ r := by dsimp [r]; linarith [abs_nonneg C]
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hr2 : r ≤ r ^ 2 := by nlinarith
  have hr4 : r ^ 2 ≤ r ^ 4 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (le_of_lt hr) hr2 2
  refine ⟨r⁻¹, 1, r ^ 3, 0, ?_, by norm_num, localWeightedGradient_family r hr,
    mixedCurvature_family r, ?_⟩
  · rw [abs_inv, abs_of_pos hr]
    exact inv_le_one_of_one_le₀ hr1
  · rw [pureCurvature_family r hr]
    have hC := le_abs_self C
    dsimp [r] at hr2 hr4 ⊢
    nlinarith [abs_nonneg C]

theorem no_uniform_pointwise_pure_payment :
    ¬ ∃ C : ℝ, ∀ a b v w : ℝ, |a| ≤ 1 → |b| ≤ 1 →
      -pureCurvature negativeIdentity a b v w ≤ C * localWeightedGradient a b v w := by
  rintro ⟨C, h⟩
  obtain ⟨a, b, v, w, ha, hb, hcost, _, hbad⟩ := exists_unbounded_negative_pureCurvature C
  have hgood := h a b v w ha hb
  rw [hcost, mul_one] at hgood
  exact (not_lt_of_ge hgood) hbad

end Mettapedia.Analysis.OcticCorrelationAmplitudeObstruction
