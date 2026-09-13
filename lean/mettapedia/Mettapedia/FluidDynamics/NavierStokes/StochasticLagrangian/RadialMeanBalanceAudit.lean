import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialSourceIntegral

/-! # Foundational and boundary checks for the radial signed mean balance -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RadialMeanBalanceAudit

open MeasureTheory Mettapedia.Analysis
open UnitTorusProductTransport LocalRadialMeanRegularity

theorem coincident_density (n N : ℕ) (u : PeriodicFourierTriad.FourierVelocity)
    (x : UnitAddTorus (Fin 3 ⊕ Fin 3)) (hx : leftPoint x = rightPoint x) :
    density n N u x = 0 := by
  simp [density, hx, SignedCrossKernel.pairedStretch]

/-- A calculus check, not a Navier–Stokes example: zero rate does not remove initial source. -/
theorem endpoint_term_is_necessary :
    (∫ _t in (0 : ℝ)..1, (1 : ℝ)) ≠ (∫ t in (0 : ℝ)..1, (1 - t) * (0 : ℝ)) := by
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.RadialMeanBalanceAudit

#print axioms Mettapedia.Analysis.UnitTorusSchwartzLattice.continuous_periodize
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.continuous_tensor
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanRegularity.explicitRate_eq_imageSum
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanRegularity.integral_density_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanRegularity.continuous_extendedDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanRegularity.locallyLipschitz_extendedDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanRegularity.frozenMaterialRate_extension_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanRegularity.frozenMaterialRate_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanBalance.absolutelyContinuousOnInterval_mean
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanBalance.ae_hasDerivAt_mean
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanBalance.absolutelyContinuousOnInterval_source
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanBalance.ae_hasDerivAt_source
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanBalance.integral_source_eq_initial_add_weighted_rate
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRadialSource.norm_source_six_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityRadialSource.norm_source_six_le_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialSourceIntegral.intervalIntegrable_source
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialSourceIntegral.tendsto_integral_source
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialSourceIntegral.tendsto_integral_weighted_meanRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialSourceIntegral.integral_stretching_le_of_weighted_rate_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialSourceIntegral.energy_add_half_dissipation_le_of_weighted_rate_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.RadialMeanBalanceAudit.coincident_density
#print axioms Mettapedia.FluidDynamics.NavierStokes.RadialMeanBalanceAudit.endpoint_term_is_necessary
