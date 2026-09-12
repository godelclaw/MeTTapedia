import Mettapedia.Analysis.PeriodicRieszNearMomentTests
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalNearSourceBudget

/-! Audit of the actual near increment payment and adjustable-threshold source bound. -/

open Mettapedia.FluidDynamics.NavierStokes

example (N : ℕ) (u : PeriodicFourierTriad.FourierVelocity) :
    VorticityNearIncrement.nearIncrement 0 N u = 0 := by
  simp [VorticityNearIncrement.nearIncrement]

example (L : ℝ) (N : ℕ) (u : PeriodicFourierTriad.FourierVelocity) :
    VorticitySeparatedSource.nearSource 0 L N u = 0 := by
  have h (x y : UnitAddTorus (Fin 3)) : ¬‖x - y‖ < 0 := not_lt.mpr (norm_nonneg _)
  simp only [VorticitySeparatedSource.nearSource, h, if_false, MeasureTheory.integral_zero, mul_zero]

example (nu L : ℝ) (hnu : 0 < nu) (hL : 0 < L) :
    0 < LocalNearSourceBudget.thresholdRadius nu L :=
  LocalNearSourceBudget.thresholdRadius_pos nu L hnu hL

#print axioms VorticityNearIncrement.nearIncrement_nonneg
#print axioms VorticityNearIncrement.nearIncrement_le
#print axioms VorticityNearIncrement.absorptionRadius_pos
#print axioms VorticityNearIncrement.nearIncrement_pays
#print axioms VorticityNearIncrement.integrable_nearKernel
#print axioms VorticityNearIncrement.pairedStretch_nearKernel
#print axioms VorticityNearIncrement.retainedStretch_nearKernel
#print axioms VorticityNearIncrement.integrable_nearPairedDensity
#print axioms VorticityNearIncrement.integrable_nearRetainedDensity
#print axioms VorticityNearIncrement.integrable_nearRadialCost
#print axioms VorticityNearIncrement.nearRadialIntegral_eq
#print axioms VorticityNearIncrement.abs_nearPairedSource_sub_retained_le
#print axioms VorticityNearIncrement.nearPairedSource_le_half_dissipation_add_retained
#print axioms LocalNearSourceBudget.abs_nearSource_sub_le
#print axioms LocalNearSourceBudget.thresholdRadius_pos
#print axioms LocalNearSourceBudget.exists_uniform_source_bound_at_threshold
#print axioms LocalNearSourceBudget.exists_uniform_source_growth_budget
