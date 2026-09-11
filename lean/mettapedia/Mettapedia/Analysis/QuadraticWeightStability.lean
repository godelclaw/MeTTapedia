import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! # Stability of quadratic localization under an L2 perturbation -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.QuadraticWeightStability

open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (mu : Measure X) [IsFiniteMeasure mu]

theorem integral_mul_le (p q : C(X, ℂ)) (f : X → ℝ) (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) (B : ℝ) (hB : ∀ x, f x ≤ B) :
    (∫ x, ‖p x‖ ^ 2 * f x ∂mu) ≤
      2 * (∫ x, ‖q x‖ ^ 2 * f x ∂mu) + 2 * B * ∫ x, ‖p x - q x‖ ^ 2 ∂mu := by
  have hp : Integrable (fun x ↦ ‖p x‖ ^ 2 * f x) mu :=
    ((p.continuous.norm.pow 2).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hq : Integrable (fun x ↦ ‖q x‖ ^ 2 * f x) mu :=
    ((q.continuous.norm.pow 2).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd : Integrable (fun x ↦ ‖p x - q x‖ ^ 2) mu :=
    (((p.continuous.sub q.continuous).norm).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr : Integrable (fun x ↦ 2 * (‖q x‖ ^ 2 * f x) + 2 * B * ‖p x - q x‖ ^ 2) mu :=
    (hq.const_mul 2).add (hd.const_mul (2 * B))
  have h := integral_mono hp hr (fun x ↦ ?_)
  · rw [integral_add (hq.const_mul 2) (hd.const_mul (2 * B)), integral_const_mul, integral_const_mul] at h
    exact h
  · have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_le_norm_sub_add (p x) (q x)) 2
    have hs : ‖p x‖ ^ 2 ≤ 2 * ‖q x‖ ^ 2 + 2 * ‖p x - q x‖ ^ 2 := by
      nlinarith only [ht, sq_nonneg (‖p x - q x‖ - ‖q x‖)]
    have hm := mul_le_mul_of_nonneg_right hs (hn x)
    have hb := mul_le_mul_of_nonneg_left (hB x) (sq_nonneg ‖p x - q x‖)
    nlinarith only [hm, hb]

/-- Composing two approximations charges both physical squared errors.
No orthogonality between the errors is assumed. -/
theorem integral_sub_sq_le (p q r : C(X, ℂ)) :
    (∫ x, ‖p x - r x‖ ^ 2 ∂mu) ≤
      2 * (∫ x, ‖p x - q x‖ ^ 2 ∂mu) + 2 * (∫ x, ‖q x - r x‖ ^ 2 ∂mu) := by
  have h := integral_mul_le mu (p - r) (q - r) (fun _ ↦ 1) continuous_const
    (fun _ ↦ by norm_num) 1 (fun _ ↦ le_rfl)
  simp only [ContinuousMap.coe_sub, Pi.sub_apply, sub_sub_sub_cancel_right, mul_one] at h
  linarith only [h]

end Mettapedia.Analysis.QuadraticWeightStability
