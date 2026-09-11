import Mettapedia.Analysis.RadialPowerTests
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootWeightedIncrement

set_option autoImplicit false
noncomputable section

open MeasureTheory Mettapedia.Analysis.RadialPower
open Mettapedia.FluidDynamics.NavierStokes
open PeriodicWeightedIncrement GaussianRootWeightedIncrement
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeHigherDerivativeMoments
open PancakeFilteredStrainDynamics LocalLowDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (f : T3 → R3) (y z : T3) : incrementDensity f y z = incrementDensity f z y := by
  unfold incrementDensity
  rw [norm_sub_rev (f z) (f y)]
  ring

example (w : R3) (y z : T3) : incrementDensity (fun _ ↦ w) y z = 0 := by
  simp [incrementDensity]

example (f : T3 → R3) (y z : T3) (hy : f y = 0) : incrementDensity f y z = 0 := by
  simp [incrementDensity, hy]

example (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : Fin 3 → ℝ ↦ f (PancakeFourierMaterialPaths.torusPoint r)))
    (a b : T3) :
    (∫ x : T3, incrementDensity f (x - a) (x - b)) ≤
      48 * ‖a - b‖ ^ 2 * ∫ x : T3, weightedGradientDensity f x :=
  integral_incrementDensity_translate_le f hf hfL a b

example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (tau : ℝ) (j : Fin 3) (y : T3) :
    vorticityIncrementCost gamma chi modes u tau j y y = 0 := by
  rw [vorticityIncrementCost_eq]
  simp [incrementDensity]

example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau epsilon : ℝ) (j : Fin 3) (y z : T3) :
    GaussianRootIncrementBudget.incrementBudget gamma chi modes u centers tau epsilon j y z -
      remainderBudget gamma chi modes u centers tau epsilon j y z =
      vorticityIncrementCost gamma chi modes u tau j y z := by
  rw [incrementBudget_eq_remainder_add_cost]
  ring

#print axioms Mettapedia.Analysis.RadialPower.norm_sub_sq_identity
#print axioms Mettapedia.Analysis.RadialPower.product_weighted_norm_sub_sq_le
#print axioms Mettapedia.Analysis.RadialPower.norm_radialPower_three_sub_le
#print axioms Mettapedia.Analysis.RadialPower.locallyLipschitz_radialPower_three
#print axioms Mettapedia.Analysis.RadialPower.hasFDerivAt_radialPower_three_zero
#print axioms Mettapedia.Analysis.RadialPower.differentiable_radialPower_three
#print axioms Mettapedia.Analysis.RadialPower.norm_derivative_radialPower_three_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicWeightedIncrement.gradientDensity_eq_sum
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicWeightedIncrement.integrable_weightedGradientDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicWeightedIncrement.integral_norm_sub_translate_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicWeightedIncrement.ae_gradientDensity_radialPower_three_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicWeightedIncrement.integral_incrementDensity_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicWeightedIncrement.integral_incrementDensity_translate_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicWeightedIncrement.integrable_envelope_incrementDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicWeightedIncrement.integral_envelope_incrementDensity_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeightedIncrement.coordinateRate_fullVorticity
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeightedIncrement.weightedGradientDensity_fullVorticity
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeightedIncrement.exists_uniform_vorticity_increment_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeightedIncrement.vorticityIncrementCost_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeightedIncrement.incrementBudget_eq_remainder_add_cost
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeightedIncrement.vorticityIncrementCost_le_radial_increment
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeightedIncrement.integrable_coefficient_mul_continuous
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeightedIncrement.integral_vorticityIncrementCost_le_of_coefficient_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeightedIncrement.integral_incrementBudget_le_remainder_add_weightedPalinstrophy
