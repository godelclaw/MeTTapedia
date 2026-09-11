import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootOperatorBudget

/-! Constant weights, empty-family defaults, and genuine convergence of the operator residual. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorAudit

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail
open GaussianRootOperatorBudget PressureLocalizationField

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (f g : C(T3, C3)) (q : T6) (B : C3 →L[ℂ] C3 →L[ℂ] C3) :
    localizationField f g 1 1 q B = 0 := by
  ext x
  simp [localizationField]

example (N : ℝ) (hN : 0 < N) (t gamma : ℝ) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (tau : ℝ) :
    rootLocalizationActionNorm N hN t gamma chi modes u ∅ tau = 0 := by
  simp [rootLocalizationActionNorm]

/-- A nonempty actual patch family gives norm summability, not just a default value of `tsum`. -/
example (N : ℝ) (hN : 0 < N) (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) :
    Summable (fun n : ℕ ↦ rootLocalizationActionNorm N hN
      (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_operator_budget_for_fullVorticity
  exact (h N hN gamma hg chi modes u hu centers hc tau).1

/-- The pointwise output series really converges with only the first Fourier moment. -/
example (N : ℝ) (hN : 0 < N) (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (x : T3) (i : ↑centers) :
    Summable (fun n : ℕ ↦ rootLocalizationAction N hN
      (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau x i) :=
  (hasSum_rootLocalizationAction N hN gamma hg chi modes u hu centers hc tau x i).summable

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationField.continuous_localizationField
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationField.norm_localizationField_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationField.aestronglyMeasurable_localizationField
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationField.integrable_localizationField
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationField.integral_localizationField_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationField.finite_localization_spatial_norm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicLocalization.hasSum_localizationAction
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicLocalization.finite_sumLocalization_spatial_norm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorBudget.rootLocalizationActionNorm_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorBudget.rootLocalizationAction_eq_integral
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorBudget.rootLocalizationActionNorm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorBudget.exists_uniform_operator_budget_for_fullVorticity
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorBudget.hasSum_rootLocalizationAction
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorBudget.rootLocalizationSumAction_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorBudget.rootLocalizationSumAction_spatial_norm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorBudget.exists_uniform_sum_operator_budget_for_fullVorticity
