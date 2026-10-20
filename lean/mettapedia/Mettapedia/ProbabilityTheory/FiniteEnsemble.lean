import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Multiset.Sum
import Mathlib.Tactic

/-!
# Finite ensemble means and error transport

The numerical mean is zero for an empty multiset. Interpreting it as a pooled
probability requires a nonempty ensemble. Component error budgets pass to the
mean, with a separate term when a nonlinear estimator is applied after pooling.
-/

open scoped ENNReal

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.FiniteEnsemble

variable {α : Type*}

/-- Arithmetic mean with multiplicities retained; the empty mean uses the numerical zero convention. -/
noncomputable def mean (models : Multiset α) (value : α → ℝ) : ℝ :=
  (models.map value).sum / models.card

/-- Pointwise absolute-error budgets add across a finite multiset. -/
theorem sum_error_le (models : Multiset α) (actual estimate budget : α → ℝ)
    (bounded : ∀ model ∈ models, |actual model - estimate model| ≤ budget model) :
    |(models.map actual).sum - (models.map estimate).sum| ≤ (models.map budget).sum := by
  revert bounded
  induction models using Multiset.induction_on with
  | empty => simp
  | @cons model rest ih =>
    intro bounded
    have head := bounded model (Multiset.mem_cons_self _ _)
    have tail := ih (fun model member => bounded model (Multiset.mem_cons_of_mem member))
    simp only [Multiset.map_cons, Multiset.sum_cons]
    calc
      _ = |(actual model - estimate model) + ((rest.map actual).sum - (rest.map estimate).sum)| := by
        congr 1
        ring
      _ ≤ |actual model - estimate model| + |(rest.map actual).sum - (rest.map estimate).sum| := abs_add_le _ _
      _ ≤ _ := add_le_add head tail

/-- Averaging does not increase the average component error budget. -/
theorem mean_error_le (models : Multiset α) (actual estimate budget : α → ℝ)
    (bounded : ∀ model ∈ models, |actual model - estimate model| ≤ budget model) :
    |mean models actual - mean models estimate| ≤ mean models budget := by
  unfold mean
  rw [← sub_div, abs_div, abs_of_nonneg (show 0 ≤ (models.card : ℝ) from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (sum_error_le models actual estimate budget bounded) (Nat.cast_nonneg _)

/-- Separate component errors from the effect of estimating after pooling. -/
theorem mean_error_with_aggregation (models : Multiset α) (actual estimate budget : α → ℝ)
    (pooledEstimate : ℝ)
    (bounded : ∀ model ∈ models, |actual model - estimate model| ≤ budget model) :
    |mean models actual - pooledEstimate| ≤
      mean models budget + |mean models estimate - pooledEstimate| :=
  (abs_sub_le _ (mean models estimate) _).trans
    (add_le_add (mean_error_le models actual estimate budget bounded) le_rfl)

/-- Finite extended-nonnegative sums commute with the real-valued readout. -/
theorem finite_sum_toReal (values : Multiset ℝ≥0∞) (finite : ∀ value ∈ values, value ≠ ⊤) :
    values.sum ≠ ⊤ ∧ values.sum.toReal = (values.map ENNReal.toReal).sum := by
  revert finite
  induction values using Multiset.induction_on with
  | empty => simp
  | @cons value rest ih =>
    intro finite
    have head := finite value (Multiset.mem_cons_self _ _)
    have tail := ih (fun value member => finite value (Multiset.mem_cons_of_mem member))
    simp only [Multiset.sum_cons, Multiset.map_cons]
    exact ⟨ENNReal.add_ne_top.mpr ⟨head, tail.1⟩,
      by rw [ENNReal.toReal_add head tail.1, tail.2]⟩

end Mettapedia.ProbabilityTheory.FiniteEnsemble
