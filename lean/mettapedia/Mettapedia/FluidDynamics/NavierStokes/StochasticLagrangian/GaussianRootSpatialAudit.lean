import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootSpatialBudget

/-! Weak-derivative corners, empty-family controls, and the constructed spatial budget. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialAudit

open MeasureTheory
open PeriodicFourierTriad PancakeCurlOutputTail PancakeFourierMaterialPaths
open PeriodicFourierGradientEnergy PeriodicFourierWeakDerivative PeriodicTranslationEnergy
open GaussianSquaredRootLocalization GaussianSquaredRootTranslation GaussianRootSpatialBudget

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Norm corners are allowed: there is no continuously differentiable field premise. -/
example (q : Wavevector) (a : T3) :
    let f := fun x : T3 ↦ ‖UnitAddTorus.mFourier q x - 1‖
    (∫ x : T3, (f x - f (x - a)) ^ 2) ≤ 3 * ‖a‖ ^ 2 * ∫ x : T3, gradientSquare f x := by
  apply integral_sub_translate_sq_le
  · exact ((UnitAddTorus.mFourier q).continuous.sub continuous_const).norm
  · exact lipschitzWith_one_norm.locallyLipschitz.comp
      ((locallyLipschitz_character q).sub (LocallyLipschitz.const 1))

example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (x : T3) :
    squaredPatchDifference gamma chi modes u centers tau x x = 0 := by simp [squaredPatchDifference]

/-- The empty-family default is explicitly separate from the nonempty constructed-cover theorem. -/
example (N : ℝ) (hN : 0 < N) (t gamma : ℝ) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (tau : ℝ) (q : T6) :
    rootLocalizationSpatialNorm N hN t gamma chi modes u ∅ tau q = 0 := by
  simp [rootLocalizationSpatialNorm]

/-- Actual data and an actual nonempty patch family give summability without an envelope hypothesis. -/
example (N : ℝ) (hN : 0 < N) (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) :
    Summable (fun n : ℕ ↦ ∫ q : T6, rootLocalizationSpatialNorm N hN
      (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau q) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_spatial_budget_for_fullVorticity
  exact (h N hN gamma hg chi modes u hu centers hc tau).2.1

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicTranslationEnergy.integral_translate_sub_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicTranslationEnergy.integral_sub_translate_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicTranslationEnergy.sum_integral_sub_translate_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootTranslation.squaredRootGradientSquare_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootTranslation.integrable_squaredRootGradientSquare
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootTranslation.continuous_squaredPatchDifference_translate
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootTranslation.integral_squaredPatchDifference_translate_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootTranslation.ae_squaredRootGradientSquare_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialBudget.rootLocalizationSpatialNorm_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialBudget.continuous_rootLocalizationIntegrand
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialBudget.integrable_sum_norm_rootLocalizationIntegrand_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialBudget.measurable_rootLocalizationSpatialNorm
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialBudget.ae_rootLocalizationSpatialNorm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialBudget.integrable_rootLocalizationSpatialNorm_and_integral_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialBudget.exists_uniform_spatial_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialBudget.exists_uniform_spatial_budget_for_fullVorticity
