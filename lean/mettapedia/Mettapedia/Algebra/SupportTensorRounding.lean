import Mettapedia.Algebra.SupportTensor
import Mettapedia.GSLT.Distinction.Probabilistic.FinitePredictionRounding

/-!
# Rounding transport for support-aware tensor rows

Reuse the finite-prediction ordered-fold error theorem over the actual rows
extracted from a support tensor. No stochastic/nonnegativity hypothesis is
needed for this mathematical bridge. Its operation-error assumptions remain
explicit; it does not assert that binary64 operations satisfy uniform bounds
on all real inputs, nor does it admit an unchecked native provider.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SupportTensorRounding

open Mettapedia.GSLT.Distinction.Probabilistic.FinitePredictionRounding
open SupportTensor
open scoped BigOperators

variable {m n : Nat}

def roundedMatvec (operations : AbsoluteRoundingOps)
    (matrix : Value (Fin m × Fin n) ℝ) (vector : Fin n → ℝ) : Fin m → ℝ :=
  fun row => roundedRow operations (toSparseRows matrix row) vector 0

/-- An error budget counts stored occurrences, including explicit zeroes. -/
def rowBudget (operations : AbsoluteRoundingOps)
    (matrix : Value (Fin m × Fin n) ℝ) (row : Fin m) : ℝ :=
  rowErrorBudget operations (toSparseRows matrix row).length

theorem roundedMatvec_row_error (operations : AbsoluteRoundingOps)
    (matrix : Value (Fin m × Fin n) ℝ) (vector : Fin n → ℝ) (row : Fin m) :
    |roundedMatvec operations matrix vector row - (matrixFill matrix).mulVec vector row| ≤
      rowBudget operations matrix row := by
  have exactRow := congrFun (sparseRows_apply matrix vector) row
  change SparseLinearMap.rowRun (toSparseRows matrix row) vector 0 = _ at exactRow
  rw [← exactRow]
  simpa only [roundedMatvec, rowBudget, sub_self, abs_zero, zero_add] using
    roundedRow_error operations (toSparseRows matrix row) vector 0 0

theorem row_entries_le_columns (matrix : Value (Fin m × Fin n) ℝ) (row : Fin m) :
    (toSparseRows matrix row).length ≤ n := by
  simpa only [toSparseRows, entries, List.length_finRange] using
    List.length_filterMap_le (f := fun col => (matrix (row, col)).map (col, ·))
      (l := List.finRange n)

theorem rowBudget_le_dense (operations : AbsoluteRoundingOps)
    (matrix : Value (Fin m × Fin n) ℝ) (row : Fin m) :
    rowBudget operations matrix row ≤ rowErrorBudget operations n := by
  apply mul_le_mul_of_nonneg_right
    (by exact_mod_cast row_entries_le_columns matrix row)
    (add_nonneg operations.multiplyError_nonneg operations.addError_nonneg)

theorem roundedMatvec_l1_error (operations : AbsoluteRoundingOps)
    (matrix : Value (Fin m × Fin n) ℝ) (vector : Fin n → ℝ) :
    vectorL1 (roundedMatvec operations matrix vector) ((matrixFill matrix).mulVec vector) ≤
      ∑ row, rowBudget operations matrix row := by
  exact Finset.sum_le_sum fun row _ => roundedMatvec_row_error operations matrix vector row

theorem roundedMatvec_l1_dense_bound (operations : AbsoluteRoundingOps)
    (matrix : Value (Fin m × Fin n) ℝ) (vector : Fin n → ℝ) :
    vectorL1 (roundedMatvec operations matrix vector) ((matrixFill matrix).mulVec vector) ≤
      m * rowErrorBudget operations n := by
  apply (roundedMatvec_l1_error operations matrix vector).trans
  calc
    (∑ row, rowBudget operations matrix row) ≤ ∑ _row : Fin m, rowErrorBudget operations n :=
      Finset.sum_le_sum fun row _ => rowBudget_le_dense operations matrix row
    _ = m * rowErrorBudget operations n := by simp

end Mettapedia.Algebra.SupportTensorRounding
