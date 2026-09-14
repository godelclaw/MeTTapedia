import NavierStokes.R3.HeatKernelCommutator
import NavierStokes.ViscousPropagator
import NavierStokes.PeriodicViscosityUniqueness
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCoherentPairEstimate

/-!
# Direct upstream dependency audit

These declarations are imported from the pinned upstream package. Their
proofs are not copied or reimplemented. The audit does not assert that the
hypotheses of these estimates have been established for arbitrary-data
unforced Navier–Stokes solutions.
-/

#print axioms NavierStokesR3.Comparison.riesz_commutator_eq_heatKernel
#print axioms NavierStokesR3.Comparison.riesz_commutator_pair_bound
#print axioms NavierStokesR3.Comparison.cancelledTimeKernel_integral_swap
#print axioms NavierStokes.ViscousPropagator.high_harmonic_propagator_estimate
#print axioms NavierStokes.PeriodicViscosityUniqueness.classical_uniqueness_on_Icc
#print axioms Mettapedia.FluidDynamics.NavierStokes.PancakeCoherentPairEstimate.sigmaSq_coherent_le
