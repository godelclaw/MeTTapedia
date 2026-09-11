import Mettapedia.Analysis.NormalizationStability
import Mettapedia.Analysis.FiniteFiberLinearMap
import Mettapedia.Analysis.FiniteGroupedConvolutionEnergy
import Mathlib.Analysis.Normed.Group.Real

/-! Regression tests for zero-safe normalization and coincident source shifts. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

example : ‖NormedSpace.normalize (1 : ℝ) - NormedSpace.normalize 0‖ * ‖(1 : ℝ)‖ = 1 := by
  norm_num [NormedSpace.normalize]

example : ‖NormedSpace.normalize (1 : ℝ) - NormedSpace.normalize (-1 / 100 : ℝ)‖ = 2 := by
  norm_num [NormedSpace.normalize, Real.norm_eq_abs]

/-- Coincident shifts interfere before squaring; their energy is four, not two. -/
example :
    (∑ q ∈ ({0} : Finset ℤ),
      ‖∑ ik ∈ (Finset.univ : Finset (Fin 2)) ×ˢ ({0} : Finset ℤ) with (0 : ℤ) + ik.2 = q,
        (1 : ℝ)‖ ^ 2) = 4 := by
  simp only [Finset.sum_filter, Finset.sum_product, Finset.sum_singleton, Fin.sum_univ_two,
    zero_add, ite_true]
  norm_num

#print axioms Mettapedia.Analysis.norm_normalize_le_one
#print axioms Mettapedia.Analysis.norm_normalize_sub_mul_norm_le
#print axioms Mettapedia.Analysis.sum_apply_fiberwise
#print axioms Mettapedia.Analysis.FiniteGroupedConvolutionEnergy.sum_fiber_weight_le
#print axioms Mettapedia.Analysis.FiniteGroupedConvolutionEnergy.sum_norm_sq_le
