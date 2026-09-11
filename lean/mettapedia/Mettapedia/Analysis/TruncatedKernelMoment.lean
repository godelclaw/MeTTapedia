import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Truncated first moments of integrable kernels

The weight `min R ‖x‖` retains the small-displacement cost but caps the
large-displacement cost. Both the mass and the full first moment bound
this integral. The cap need not be positive; nonnegativity suffices.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.TruncatedKernelMoment

open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] {μ : Measure E}

def moment (R : ℝ) (K : E → F) (μ : Measure E) : ℝ :=
  ∫ x, min R ‖x‖ * ‖K x‖ ∂μ

omit [BorelSpace E] in
theorem moment_nonneg {R : ℝ} (hR : 0 ≤ R) (K : E → F) : 0 ≤ moment R K μ :=
  integral_nonneg (fun x ↦ mul_nonneg (le_min hR (norm_nonneg x)) (norm_nonneg _))

theorem integrable_min_mul_norm {R : ℝ} (hR : 0 ≤ R) {K : E → F} (hK : Integrable K μ) :
    Integrable (fun x ↦ min R ‖x‖ * ‖K x‖) μ := by
  apply (hK.norm.const_mul R).mono'
    ((continuous_const.min continuous_norm).aestronglyMeasurable.mul hK.norm.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖min R ‖x‖ * ‖K x‖‖ ≤ R * ‖K x‖
  rw [Real.norm_of_nonneg (mul_nonneg (le_min hR (norm_nonneg x)) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)

theorem moment_le_mass {R : ℝ} (hR : 0 ≤ R) {K : E → F} (hK : Integrable K μ) :
    moment R K μ ≤ R * ∫ x, ‖K x‖ ∂μ := by
  rw [moment, ← integral_const_mul]
  exact integral_mono (integrable_min_mul_norm hR hK) (hK.norm.const_mul R)
    (fun x ↦ mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))

theorem moment_le_firstMoment {R : ℝ} (hR : 0 ≤ R) {K : E → F}
    (hK : Integrable K μ) (hfirst : Integrable (fun x ↦ ‖x‖ * ‖K x‖) μ) :
    moment R K μ ≤ ∫ x, ‖x‖ * ‖K x‖ ∂μ :=
  integral_mono (integrable_min_mul_norm hR hK) hfirst
    (fun x ↦ mul_le_mul_of_nonneg_right (min_le_right R ‖x‖) (norm_nonneg (K x)))

theorem moment_le_min {R : ℝ} (hR : 0 ≤ R) {K : E → F}
    (hK : Integrable K μ) (hfirst : Integrable (fun x ↦ ‖x‖ * ‖K x‖) μ) :
    moment R K μ ≤ min (R * ∫ x, ‖K x‖ ∂μ) (∫ x, ‖x‖ * ‖K x‖ ∂μ) :=
  le_min (moment_le_mass hR hK) (moment_le_firstMoment hR hK hfirst)

omit [BorelSpace E] in
@[simp] theorem moment_zero (K : E → F) : moment 0 K μ = 0 := by
  simp [moment]

end Mettapedia.Analysis.TruncatedKernelMoment
