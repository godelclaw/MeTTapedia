import Mettapedia.Analysis.WeightedSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

/-! Complementary weights preserve signed complex series, including cancellation. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedSeriesTests

open WeightedSeries

example (v : ℕ → ℂ) (hv : Summable (fun i ↦ ‖v i‖)) :
    (∑' i, (1 / 2 : ℂ) • v i) + (∑' i, (1 - (1 / 2 : ℂ)) • v i) = ∑' i, v i := by
  apply tsum_smul_add_complement (fun _ ↦ (1 / 2 : ℂ)) v hv 1 1
  · intro i; norm_num
  · intro i; norm_num

/-- The generic partition allows signed weights; positivity is not assumed. -/
example (v : ℕ → ℂ) (hv : Summable (fun i ↦ ‖v i‖)) :
    (∑' i, (2 : ℂ) • v i) + (∑' i, (-1 : ℂ) • v i) = ∑' i, v i := by
  have h := tsum_smul_add_complement (fun _ : ℕ ↦ (2 : ℂ)) v hv 2 1
    (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
  norm_num at h ⊢
  exact h

end Mettapedia.Analysis.WeightedSeriesTests

#print axioms Mettapedia.Analysis.WeightedSeries.summable_smul_of_norm_le
#print axioms Mettapedia.Analysis.WeightedSeries.tsum_smul_add_complement
