import Mettapedia.Analysis.ContinuousFieldMinkowski

/-! Norm normalization, finite-component aggregation, and signed cancellation. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Mettapedia.Analysis.ContinuousFieldMinkowski
open scoped NNReal

/-- The two component norms combine quadratically, not by their sum. -/
example : ‖(bundle (fun i : Fin 2 ↦ ContinuousMap.const Unit (![3, 4] i : ℝ))).toLp
    2 (Measure.dirac ()) ℝ‖ = 5 := by
  rw [norm_bundle_toL2]
  norm_num [Fin.sum_univ_two, ContinuousMap.const_apply, Real.sqrt_eq_iff_eq_sq]

/-- A non-probability spatial measure contributes the square root of its mass. -/
example : ‖(ContinuousMap.const Unit (2 : ℝ)).toLp
    2 ((9 : ℝ≥0) • Measure.dirac ()) ℝ‖ = 6 := by
  rw [norm_toL2]
  norm_num [integral_smul_measure, Real.sqrt_eq_iff_eq_sq]

example : ‖(bundle (fun i : Fin 0 ↦ ContinuousMap.const Unit (i.val : ℝ))).toLp
    2 (Measure.dirac ()) ℝ‖ = 0 := by
  simp [norm_bundle_toL2]

/-- Opposite responses can cancel in the field integral even when the norm budget is positive. -/
example :
    Real.sqrt (∫ _x : Unit, ‖∫ a : Bool, (if a then (1 : ℝ) else -1)
      ∂(Measure.dirac true + Measure.dirac false)‖ ^ 2 ∂Measure.dirac ()) = 0 ∧
    (∫ a : Bool, Real.sqrt (∫ _x : Unit, ‖if a then (1 : ℝ) else -1‖ ^ 2
      ∂Measure.dirac ()) ∂(Measure.dirac true + Measure.dirac false)) = 2 := by
  norm_num [integral_add_measure, Measure.real, Measure.add_apply]

#print axioms norm_toL2_sq
#print axioms norm_toL2
#print axioms integral_spatial_norm_le
#print axioms integral_finite_spatial_norm_le
#print axioms norm_bundle_toL2
#print axioms hasSum_finite_spatial_norm_le
