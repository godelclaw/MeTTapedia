import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weighted energy bounds for Bochner integrals

Cauchy–Schwarz with an integrable nonnegative weight controls the square
of an integral by the weight mass times a weighted input energy. The
zero-mass case is included, without division by the mass.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedIntegralEnergy

open MeasureTheory Filter

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_cauchy_schwarz (w a : α → ℝ)
    (hw : Integrable w μ) (hw0 : ∀ x, 0 ≤ w x)
    (ha : AEStronglyMeasurable a μ) (ha0 : ∀ x, 0 ≤ a x)
    (hwa : Integrable (fun x ↦ w x * a x ^ 2) μ) :
    Integrable (fun x ↦ w x * a x) μ ∧
      (∫ x, w x * a x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * ∫ x, w x * a x ^ 2 ∂μ := by
  have hs : MemLp (fun x ↦ Real.sqrt (w x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hw.aestronglyMeasurable)).mpr
    simpa only [Real.sq_sqrt (hw0 _)] using hw
  have ht : MemLp (fun x ↦ Real.sqrt (w x) * a x) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      ((Real.continuous_sqrt.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul ha)).mpr
    simpa only [Pi.mul_apply, mul_pow, Real.sq_sqrt (hw0 _)] using hwa
  have he (x : α) : Real.sqrt (w x) * (Real.sqrt (w x) * a x) = w x * a x := by
    rw [← mul_assoc, Real.mul_self_sqrt (hw0 x)]
  have hi : Integrable (fun x ↦ Real.sqrt (w x) * (Real.sqrt (w x) * a x)) μ :=
    hs.integrable_mul ht
  simp only [he] at hi
  refine ⟨hi, ?_⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall (fun x ↦ Real.sqrt_nonneg (w x)))
    (Eventually.of_forall (fun x ↦ mul_nonneg (Real.sqrt_nonneg _) (ha0 x)))
    (by simpa using hs) (by simpa using ht)
  simp only [he, Real.rpow_two, mul_pow, Real.sq_sqrt (hw0 _)] at h
  have hp := pow_le_pow_left₀ (integral_nonneg (fun x ↦ mul_nonneg (hw0 x) (ha0 x))) h 2
  simpa only [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg hw0),
    Real.sq_sqrt (integral_nonneg (fun x ↦ mul_nonneg (hw0 x) (sq_nonneg _)))] using hp

theorem integrable_and_norm_integral_sq_le (w a : α → ℝ) (v : α → E)
    (hw : Integrable w μ) (hw0 : ∀ x, 0 ≤ w x)
    (ha : AEStronglyMeasurable a μ) (ha0 : ∀ x, 0 ≤ a x)
    (hwa : Integrable (fun x ↦ w x * a x ^ 2) μ)
    (hv : AEStronglyMeasurable v μ) (hbound : ∀ᵐ x ∂μ, ‖v x‖ ≤ w x * a x) :
    Integrable v μ ∧ ‖∫ x, v x ∂μ‖ ^ 2 ≤
      (∫ x, w x ∂μ) * ∫ x, w x * a x ^ 2 ∂μ := by
  obtain ⟨hi, he⟩ := weighted_cauchy_schwarz w a hw hw0 ha ha0 hwa
  exact ⟨hi.mono' hv hbound,
    (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_of_norm_le hi hbound) 2).trans he⟩

end Mettapedia.Analysis.WeightedIntegralEnergy
