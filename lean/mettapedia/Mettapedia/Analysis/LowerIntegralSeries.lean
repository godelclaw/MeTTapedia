import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Lower bounds for integrals of nonnegative series

The sum of lower integrals is bounded by the lower integral of the sum.
No measurability hypothesis is needed for this direction; no equality or
Bochner interchange is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Analysis.LowerIntegralSeries

open MeasureTheory
open scoped ENNReal

variable {α ι : Type*} [MeasurableSpace α] (μ : Measure α)

theorem sum_lintegral_le (P : Finset ι) (f : ι → α → ℝ≥0∞) :
    (∑ i ∈ P, ∫⁻ x, f i x ∂μ) ≤ ∫⁻ x, ∑ i ∈ P, f i x ∂μ := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert i P hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

theorem tsum_lintegral_le (f : ι → α → ℝ≥0∞) :
    (∑' i, ∫⁻ x, f i x ∂μ) ≤ ∫⁻ x, ∑' i, f i x ∂μ := by
  classical
  conv_lhs => rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro P
  exact (sum_lintegral_le μ P f).trans
    (lintegral_mono (fun x ↦ ENNReal.sum_le_tsum P))

end Mettapedia.Analysis.LowerIntegralSeries
