import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalGaussianPressureBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureSmoothingBalance

/-! Physical-error regressions and dependency audit for Gaussian pressure budgets. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianPressureBudgetAudit

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeQuadraticFourierSupport
open FourierPressureCommutator FourierResolventSmoothing WeightedPressureL2Replacement
open Mettapedia.Analysis.FiniteResolventEnergy Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (c : Unit → FourierCoeff (Fin 3)) :
    approximationError (fun i ↦ fourierPolynomial (c i)) c = 0 := by
  simp [approximationError]

/-- Omitting a unit spatial amplitude incurs unit error, not zero error. -/
example : approximationError (fun _ : Unit ↦ (1 : C(T3, ℂ))) (fun _ ↦ 0) = 1 := by
  simp [approximationError, fourierPolynomial]

/-- Composing two opposed unit errors attains the factor two in the general bound. -/
example : (∫ _x : T3, ‖(1 : ℂ) - (-1)‖ ^ 2) =
    2 * (∫ _x : T3, ‖(1 : ℂ) - 0‖ ^ 2) + 2 * (∫ _x : T3, ‖(0 : ℂ) - (-1)‖ ^ 2) := by
  norm_num

/-- The aggregate error sees the actual nonreal unit mode after smoothing. -/
example :
    let c := Finsupp.single (![1, 0, 0] : Wavevector) Complex.I
    approximationError (fun _ : Unit ↦ fourierPolynomial c) (fun _ ↦ smoothCutoff 1 c) = 1 / 4 := by
  dsimp only
  unfold approximationError
  simp only [Fintype.sum_unique]
  rw [show (fun x : T3 ↦
      ‖fourierPolynomial (smoothCutoff 1 (Finsupp.single ![1, 0, 0] Complex.I)) x -
        fourierPolynomial (Finsupp.single ![1, 0, 0] Complex.I) x‖ ^ 2) =
      (fun x : T3 ↦ ‖fourierPolynomial (Finsupp.single ![1, 0, 0] Complex.I) x -
        fourierPolynomial (smoothCutoff 1 (Finsupp.single ![1, 0, 0] Complex.I)) x‖ ^ 2) by
      funext x; rw [norm_sub_rev]]
  rw [integral_error_sq_eq 1 (by norm_num)]
  unfold scalarEnergy
  simp only [smoothCutoff_apply]
  simp_rw [norm_sub_smooth_sq]
  norm_num [multiplier, realFrequency, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

/-- Unit potential and pressure size balance at epsilon six, not at zero. -/
example : (72 / 6 + 2 * 6 : ℝ) = 24 ∧ (72 / 1 + 2 * 1 : ℝ) > 24 := by
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.GaussianPressureBudgetAudit

#print axioms Mettapedia.Analysis.QuadraticWeightStability.integral_sub_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedPressureL2Replacement.approximationError_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedPressureL2Replacement.integral_spatial_patch_le_fourier
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedPressureL2Replacement.integral_weighted_tilt_le_fourier
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedPressureL2Replacement.trace_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedPressureL2Replacement.sum_tracePatchEnergy_le_spatial
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedPressureL2Replacement.integral_weighted_tilt_le_with_tail
#print axioms Mettapedia.FluidDynamics.NavierStokes.SmoothedPressureL2Budget.approximationError_smooth_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.SmoothedPressureL2Budget.derivativeCost_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SmoothedPressureL2Budget.replacementCost_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SmoothedPressureL2Budget.integral_weighted_tilt_le_smoothed
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianFourierBudget.exists_local_gaussian_fourier_family
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianFourierBudget.exists_local_gaussian_fourier_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressureBudget.exists_local_gaussian_pressure_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureSmoothingBalance.pressureSizeSq_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureSmoothingBalance.derivativeCost_eq_balanced_add_square
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureSmoothingBalance.balancedDerivativeCost_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureSmoothingBalance.balancingParameter_pos
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureSmoothingBalance.derivativeCost_balancingParameter
