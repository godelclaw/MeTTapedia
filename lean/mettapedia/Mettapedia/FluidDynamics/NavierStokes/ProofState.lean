import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyBKMBridge
import Mettapedia.FluidDynamics.NavierStokes.FeffermanCompatibilityFrontier
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesDEGroundedCanary
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionKernel
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzStokesKernel
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzStokesRankOneObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzPastDissipation
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzNonzeroSupport
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzNoUniformDissipation
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzZeroRestartObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzAntiProfileCanaryObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLocalizedStreamFunction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzRankOneShearObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzSymmetricShearObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesNilpotentShearObstruction
import Mettapedia.FluidDynamics.NavierStokes.Scaling.CriticalNormCanaries
import Mettapedia.FluidDynamics.NavierStokes.Scaling.AveragedEquationCanaries
import Mettapedia.FluidDynamics.NavierStokes.Scaling.AveragedMomentumCanaries
import Mettapedia.FluidDynamics.NavierStokes.Scaling.ReynoldsStressClosureCanaries
import Mettapedia.FluidDynamics.NavierStokes.Scaling.EnergyInequalityTransportCanaries
import Mettapedia.FluidDynamics.NavierStokes.Scaling.CriticalScalingTransportCanaries
import Mettapedia.FluidDynamics.NavierStokes.Scaling.RegularityPromotionCanaries
import Mettapedia.FluidDynamics.NavierStokes.Scaling.ReynoldsStressObstruction
import Mettapedia.FluidDynamics.NavierStokes.Scaling.EnergyInequalityObstruction
import Mettapedia.FluidDynamics.NavierStokes.Scaling.CriticalScalingObstruction
import Mettapedia.FluidDynamics.NavierStokes.Scaling.AveragedEquationObstruction

/-!
# Navier-Stokes Proof State

This module records the current Navier-Stokes route state as checked Lean data.
It is an audit surface for the active formalization lane, not a solution of the
Millennium problem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open Set
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

/-- Coarse status tags for central Navier-Stokes route nodes. -/
inductive NavierProofStatus where
  | surveyed
  | checked
  | refuted
  | needsBackground
  | scalingUncleared
  | retiredPlaceholder
  | openGoal
deriving DecidableEq, Repr

/-- Snapshot of the active Navier-Stokes Lean lane. -/
structure NavierLaneSurvey where
  sourceFiles : Nat
  sourceLines : Nat
  internalImportEdges : Nat
  regressionFiles : Nat
  filesOverThousandLines : Nat
  filesOverSevenHundredFiftyLines : Nat
  leavesWithoutInternalImports : Nat
deriving Repr

/-- Current dependency-map counts for `FluidDynamics/NavierStokes`. -/
def currentNavierLaneSurvey : NavierLaneSurvey where
  sourceFiles := 508
  sourceLines := 114812
  internalImportEdges := 1296
  regressionFiles := 141
  filesOverThousandLines := 3
  filesOverSevenHundredFiftyLines := 3
  leavesWithoutInternalImports := 2

/-- Simple PLN-style truth bookkeeping: support and confidence percentages. -/
structure SimpleTruthValue where
  supportPercent : Nat
  confidencePercent : Nat
deriving Repr

/-- A compact route-node record for the current Navier-Stokes formalization. -/
structure NavierProofNode where
  id : String
  status : NavierProofStatus
  truthValue : SimpleTruthValue
  evidence : String
  blocker : String
deriving Repr

/-- The active entrypoint is a live theorem surface, not the regression archive. -/
def navierLiveSurfaceNode : NavierProofNode where
  id := "navier.live-surface"
  status := .checked
  truthValue := ⟨100, 94⟩
  evidence := "Mettapedia.FluidDynamics.NavierStokes imports Live and this proof-state surface."
  blocker := "Regression archives remain separate from the live entrypoint."

/-- The over-broad concrete target is kept as a shape check, not the intended endpoint. -/
def navierConcreteTargetNode : NavierProofNode where
  id := "navier.explicit-concrete-target"
  status := .refuted
  truthValue := ⟨100, 96⟩
  evidence := "not_ExplicitConcreteNavierStokesMillenniumTarget and finite-energy repairs split the surface."
  blocker := "Whole-space candidates without finite initial kinetic energy are outside the repaired target."

/-- The repaired target correctly exposes finite initial energy as an input obligation. -/
def navierFiniteEnergyTargetNode : NavierProofNode where
  id := "navier.finite-energy-target"
  status := .checked
  truthValue := ⟨100, 91⟩
  evidence := "ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget includes finiteInitialKineticEnergy."
  blocker := "Global regularity still requires genuine analytic continuation for all finite-energy data."

/-- The energy/BKM bridge rejects nonzero constant velocities before continuation. -/
def navierEnergyBKMConstantVelocityNode : NavierProofNode where
  id := "navier.energy-bkm.constant-velocity"
  status := .refuted
  truthValue := ⟨100, 97⟩
  evidence := "not_exists_energyBKMBridge_kineticIntegrabilityOnSlab_constantInitialVelocity"
  blocker := "A nonzero constant initial field fails the slab kinetic-integrability input at time zero."

/-- The same finite-energy gate rejects the nontrivial heat-shear route family. -/
def navierEnergyBKMHeatShearNode : NavierProofNode where
  id := "navier.energy-bkm.heat-shear"
  status := .refuted
  truthValue := ⟨100, 96⟩
  evidence := "not_exists_energyBKMBridge_kineticIntegrabilityOnSlab_heatShearInitialVelocity"
  blocker := "Nontrivial heat-shear initial data fail the slab kinetic-integrability input at time zero."

/-- The Fefferman-style backward route still needs a real lift from vorticity tendrils. -/
def navierFeffermanLiftNode : NavierProofNode where
  id := "navier.fefferman-lift"
  status := .retiredPlaceholder
  truthValue := ⟨100, 99⟩
  evidence := "The audited FeffermanGlobalRegularityClause family is parameterized by FeffermanPredicateKit rather than the concrete R^3 PDE; one seeded model instantiates SmoothVelocity and MomentumEquation as True. These predicate-kit route nodes are retained only as missing-lift checklists and establish nothing about the real Navier-Stokes equation."
  blocker := "Do not count any FeffermanPredicateKit global-regularity clause as PDE progress unless it is replaced by a witness for mkFullyConcreteNavierStokesSurface."

/-- The actual `ℝ × ℝ^3` equation surface has a committed positive canary. -/
def navierDEGroundedZeroCanaryNode : NavierProofNode where
  id := "navier.de-grounded-zero-canary"
  status := .checked
  truthValue := ⟨100, 98⟩
  evidence := "concreteNSZeroCanary_and_scaling_packet proves a fully concrete zero velocity/pressure witness for mkFullyConcreteNavierStokesSurface, its guarded coordinate energy identity, uniform momentum scaling exponent 3, L2 supercritical power exponent -1, L3 critical exponent 0, and L4 subcritical exponent 1."
  blocker := "This canary proves the theorem surface is non-vacuous; it is not a global regularity theorem for arbitrary finite-energy data."

/-- A general slice-Schwartz solution now carries the real energy identity. -/
def navierSchwartzEnergyIdentityNode : NavierProofNode where
  id := "navier.energy.schwartz-solution-identity"
  status := .checked
  truthValue := ⟨78, 84⟩
  evidence := "coordinateEnergyDissipationIdentity_of_schwartzConcreteSolution proves, for arbitrary energy-admissible slice-Schwartz velocity/pressure fields satisfying SatisfiesMomentumEquation and IsIncompressible on mkFullyConcreteNavierStokesSurface, the pressure-work cancellation, convection-work cancellation, coordinate viscous Laplacian identity, and d/dt normalized kinetic energy = -coordinateEnergyDissipationRate. PLN STV <s=.78,c=.84>, ITV [.6552,.8152], PROGRESS 34%."
  blocker := "This decides the Schwartz-solution energy identity subnode, not global regularity. Extending it to every smooth finite-energy solution still requires closing the derivative-under-the-integral and decay/approximation seam beyond the slice-Schwartz energy-admissible class."

/-- The nonzero slice-Schwartz kernel is checked, but it is not yet an
unconditional positive canary. -/
def navierNonzeroSchwartzEnergyKernelNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-kernel"
  status := .checked
  truthValue := ⟨73, 86⟩
  evidence := "SchwartzEnergyIdentityKernel, NonzeroSchwartzConcreteNavierStokesSolution.energyIdentityKernel, twoModeSchwartzPressureSlice_nonzeroSchwartzConcreteSolution_of_momentumEquation, and twoModeSchwartzPressureSlice_nonzero_energyIdentityKernel_of_momentumEquation package the pressure and convection cancellations, viscous formula, meaningful identity, and nonzero witness for any bounded divergence-free two-mode Schwartz ansatz with Schwartz pressure slices satisfying the literal pointwise momentum equation. PLN STV <s=.73,c=.86>, ITV [.6278,.7678], PROGRESS 40%."
  blocker := "This is nonzero-preserving and PDE-grounded but still conditional on an inhabited pressure-slice momentum closure. The remaining canary obligation is an explicit nonzero divergence-free Schwartz profile pair and Schwartz pressure slices satisfying that closure."

/-- Line-invariant shear shortcuts are now blocked for nonzero slice-Schwartz
solutions. -/
def navierNonzeroSchwartzLineInvariantObstructionNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-line-invariant-obstruction"
  status := .checked
  truthValue := ⟨85, 90⟩
  evidence := "velocity_eq_zero_of_velocitySlice_translationInvariantAlong, not_exists_nonzeroSchwartzConcreteSolution_all_velocitySlices_translationInvariantAlong, and every_nonzeroSchwartzConcreteSolution_has_non_lineInvariant_slice prove that any slice invariant along a nonzero direction is zero, so no nonzero slice-Schwartz concrete solution can keep all velocity slices line-invariant. PLN STV <s=.85,c=.90>, ITV [.765,.865], PROGRESS 48%."
  blocker := "This rules out the line-invariant shear shortcut class. The remaining positive canary must use genuinely non-line-invariant Schwartz profiles and close the pressure-slice momentum equation."

/-- The exact heat-shear PDE family is nonzero but excluded from the
slice-Schwartz solution lane. -/
def navierNonzeroSchwartzHeatShearBoundaryNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-heat-shear-boundary"
  status := .checked
  truthValue := ⟨90, 91⟩
  evidence := "heatShearVelocityField_exact_nonzero_and_not_schwartzConcreteSolution proves that every nondegenerate heat-shear field is nonzero, divergence-free, and solves the zero-pressure Navier-Stokes equation at its own viscosity, but cannot inhabit the slice-Schwartz concrete-solution interface because its time-zero Schwartz slice would have to equal the nondecaying heat-shear initial datum. The wrong-viscosity variants also fail the pressure-residual curl gate. PLN STV <s=.90,c=.91>, ITV [.819,.909], PROGRESS 71%."
  blocker := "This rules out the classical exact shear-flow shortcut as a positive canary. The remaining canary must have decaying time-zero slices, break line invariance, be genuinely time-dependent, and carry pressure slices satisfying the full momentum equation, or be replaced by a broader obstruction for that closure class."

/-- Rank-one fixed-direction Schwartz profiles cannot use zero convection as a
nonzero exact-solution shortcut. -/
def navierNonzeroSchwartzRankOneShearObstructionNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-rank-one-shear-obstruction"
  status := .checked
  truthValue := ⟨84, 89⟩
  evidence := "spatialConvection_timeIndependent_rankOneSchwartzVelocity, rankOneSchwartzVelocity_eq_zero_of_spatialConvection_zero_at, and not_exists_nonzero_rankOneSchwartzVelocity_with_zero_spatialConvection prove that a fixed-direction profile u(x)=phi(x)v with nonzero v has zero pointwise convection only when the Schwartz scalar phi, hence u, is zero. velocity_eq_zero_of_velocitySlice_eq_rankOne_zeroConvection_at and not_exists_nonzeroSchwartzConcreteSolution_forall_rankOne_zeroConvection lift the obstruction into the concrete solution interface slice-by-slice. PLN STV <s=.84,c=.89>, ITV [.7476,.8576], PROGRESS 62%."
  blocker := "This blocks the rank-one zero-convection Stokes-flow shortcut even when packaged as slice-Schwartz concrete solution data. The remaining positive canary must close a genuinely non-rank-one pressure-slice momentum equation or prove a broader obstruction."

/-- Symmetric finite-mode shear is a nonzero pressure-closed algebraic canary,
but it is excluded from the slice-Schwartz lane. -/
def navierNonzeroSchwartzSymmetricShearObstructionNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-symmetric-shear-obstruction"
  status := .checked
  truthValue := ⟨88, 88⟩
  evidence := "finiteModeSymmetricShear_exact_nonzero_and_not_schwartzSlice proves that for every nonzero amplitude the symmetric off-diagonal finite-mode shear is nonzero, divergence-free, and pressure-closed by affine-quadratic pressure, while not_exists_schwartzInitialVelocity_eq_finiteModeSymmetricShearPolynomialMode_of_alpha_ne_zero excludes its time-one linear-growth slice from the Schwartz initial-velocity lane. PLN STV <s=.88,c=.88>, ITV [.7744,.8944], PROGRESS 53%."
  blocker := "This closes the next non-line-invariant finite-mode shortcut. The remaining positive canary must use localized non-polynomial Schwartz profiles, or prove a stronger obstruction for every explicit pressure-slice closure route."

/-- Nilpotent linear shear exposes a viscosity-independent pressure-residual
curl obstruction. -/
def navierNonzeroSchwartzNilpotentShearPressureObstructionNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-nilpotent-shear-pressure-obstruction"
  status := .checked
  truthValue := ⟨91, 92⟩
  evidence := "nilpotentLinearShearVelocityField is divergence-free and has zero spatial Laplacian, but spatialConvection_nilpotentLinearShearVelocityField leaves the horizontal mode x_2 e_0; spatialVorticity_momentumPressureResidual_nilpotentLinearShearVelocityField proves the resulting pressure residual has constant curl e_1*(-1). spatialVorticity_momentumPressureResidual_congr_at and spatialVorticity_momentumPressureResidual_of_frozen_nilpotentLinearShearSlice prove the same curl obstruction for any candidate sharing the nilpotent velocity slice and zero instantaneous time-derivative slice at one time. The not_exists_smoothPressure_*, not_exists_schwartzConcreteSolution_*, not_exists_nonzeroSchwartzConcreteSolution_*, and frozen-slice no-go theorems rule out smooth-pressure closure and both slice-Schwartz solution interfaces at every viscosity. PLN STV <s=.91,c=.92>, ITV [.8372,.9172], PROGRESS 60%."
  blocker := "This is a pressure-closure obstruction for linear and frozen-slice shortcut classes, not a slice-Schwartz canary. The remaining positive canary must either localize a non-polynomial Schwartz profile while making the pressure residual curl-free, or prove a broader obstruction for that localized closure class."

/-- A localized stream-function construction supplies nonzero divergence-free
Schwartz initial data for the next pressure-closure search. -/
def navierNonzeroSchwartzLocalizedStreamSeedNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-localized-stream-seed"
  status := .checked
  truthValue := ⟨72, 88⟩
  evidence := "initialSpatialDivergence_streamFunctionVelocity proves that every scalar Schwartz stream function phi gives divergence-free Schwartz initial velocity (partial_1 phi, -partial_0 phi, 0), and nsLocalizedStreamDivergenceFreeInitialVelocity_nonzero proves the compactly supported x_1*bump stream function gives a concrete nonzero inhabited S_sigma datum. PLN STV <s=.72,c=.88>, ITV [.6336,.7536], PROGRESS 58%."
  blocker := "This closes the nonzero divergence-free Schwartz seed gap only. The open canary still requires an exact smooth velocity evolution and Schwartz pressure slices satisfying the Navier-Stokes momentum equation."

/-- Equal-amplitude anti-profile cancellation is now blocked as a nonzero
canary false positive. -/
def navierNonzeroSchwartzAntiProfileCanaryObstructionNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-antiprofile-canary-obstruction"
  status := .checked
  truthValue := ⟨84, 90⟩
  evidence := "localizedStreamAntiProfile_nonzeroProfiles_divergenceFree_closure_but_zeroVelocity proves that the localized stream seed and its anti-profile are nonzero divergence-free Schwartz profiles with a zero-pressure pressure-slice residual closure, while their reconstructed equal-amplitude two-mode velocity is identically zero; not_exists_nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity proves this cancelled velocity cannot inhabit the nonzero slice-Schwartz concrete solution interface. PLN STV <s=.84,c=.90>, ITV [.756,.856], PROGRESS 63%."
  blocker := "This closes a profile-level nonzero false positive. The remaining canary must prove nonzero reconstructed velocity together with exact smooth evolution, divergence, bounded energy, and Schwartz pressure slices."

/-- The full anti-profile amplitude boundary is now a reusable generator
guardrail. -/
def navierNonzeroSchwartzAntiProfileAmplitudeBoundaryNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-antiprofile-amplitude-boundary"
  status := .checked
  truthValue := ⟨87, 91⟩
  evidence := "antiProfileSchwartzVelocity_nonzero_iff_exists_amplitude_ne proves that, for any nonzero Schwartz profile f, the anti-profile reconstruction a(t)f + b(t)(-f) is nonzero exactly when the scalar amplitudes differ somewhere; localizedStreamAntiProfile_velocity_nonzero_iff_exists_amplitude_ne specializes this to the localized stream seed, not_exists_nonzeroSchwartzConcreteSolution_equalAmplitudeAntiProfileVelocity excludes the equal-amplitude boundary from the nonzero interface, and nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_forces_amplitude_ne gives the necessary unequal-amplitude condition for any nonzero solution using that reconstruction. PLN STV <s=.87,c=.91>, ITV [.7917,.8817], PROGRESS 64%."
  blocker := "This gives the exact anti-profile nonzero boundary, not a pressure-slice momentum closure. The remaining canary must still prove that an unequal-amplitude localized stream/anti-stream or another non-polynomial Schwartz profile satisfies the full Navier-Stokes equation with Schwartz pressure slices."

/-- Stationary slice-Schwartz candidates now face a checked energy gate. -/
def navierNonzeroSchwartzStationaryDissipationGateNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-stationary-dissipation-gate"
  status := .checked
  truthValue := ⟨89, 91⟩
  evidence := "velocity_eq_zero_of_coordinateEnstrophyAt_eq_zero proves that zero corrected coordinate enstrophy on a Schwartz velocity slice forces the slice to vanish; coordinateEnergyDissipationRate_eq_zero_of_velocity_timeIndependent and velocity_eq_zero_of_velocity_timeIndependent_of_pos_viscosity then prove every positive-viscosity time-independent slice-Schwartz concrete solution is identically zero; not_exists_nonzeroSchwartzConcreteSolution_velocity_timeIndependent_of_pos_viscosity gives the nonzero-interface obstruction. PLN STV <s=.89,c=.91>, ITV [.8099,.8999], PROGRESS 66%."
  blocker := "This rules out positive-viscosity stationary nonzero slice-Schwartz canaries. The remaining positive canary must be genuinely time-dependent and close the full pressure-slice momentum equation."

/-- Nonzero positive-viscosity solutions force a strictly nontrivial energy
identity at some witness time. -/
def navierNonzeroSchwartzStrictDissipationKernelNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-strict-dissipation-kernel"
  status := .checked
  truthValue := ⟨88, 90⟩
  evidence := "coordinateEnstrophyAt_pos_of_velocity_ne_zero and coordinateEnergyDissipationRate_pos_of_velocity_ne_zero prove that any nonzero Schwartz velocity slice has positive corrected enstrophy and, at positive viscosity, positive corrected dissipation; exists_strict_coordinateEnergyDissipationIdentity_of_pos_viscosity packages this with the exact energy identity, giving a witness time where d/dt normalized kinetic energy is strictly negative. PLN STV <s=.88,c=.90>, ITV [.792,.892], PROGRESS 67%."
  blocker := "This makes the nonzero energy identity strictly nontrivial for any positive-viscosity inhabitant, but it still assumes the nonzero slice-Schwartz concrete solution interface is inhabited. The remaining canary obligation is an explicit time-dependent inhabitant or a broader pressure-closure obstruction."

/-- Positive-viscosity nonzero canaries cannot be energy-flat. -/
def navierNonzeroSchwartzNoFlatEnergyObstructionNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-no-flat-energy-obstruction"
  status := .checked
  truthValue := ⟨90, 90⟩
  evidence := "velocity_eq_zero_of_forall_normalizedKineticEnergy_hasDerivAt_zero_of_pos_viscosity and velocity_eq_zero_of_exists_const_normalizedKineticEnergy_of_pos_viscosity prove ordinary-interface zero-rigidity: at positive viscosity, zero normalized-energy derivative at every time, or constant normalized kinetic energy, forces the velocity to vanish pointwise. The nonzero-subtype no-flat-energy theorems follow as canary obstructions. PLN STV <s=.90,c=.90>, ITV [.810,.910], PROGRESS 69%."
  blocker := "This rules out flat-energy and constant-energy positive-viscosity shortcut canaries at the ordinary solution-interface level, but it does not provide an explicit pressure-slice momentum closure."

/-- Positive-viscosity nonzero canaries cannot hide a nonzero witness at a
local energy extremum. -/
def navierNonzeroSchwartzLocalExtremumEnergyObstructionNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-local-extremum-obstruction"
  status := .checked
  truthValue := ⟨91, 90⟩
  evidence := "velocity_eq_zero_of_isLocalMin_normalizedKineticEnergy_of_pos_viscosity and velocity_eq_zero_of_isLocalMax_normalizedKineticEnergy_of_pos_viscosity prove that any positive-viscosity slice-Schwartz concrete solution has zero velocity on a time slice where normalized kinetic energy has a local minimum or maximum. The nonzero-interface theorems rule out nonzero witnesses at such local extrema. PLN STV <s=.91,c=.90>, ITV [.819,.919], PROGRESS 73%."
  blocker := "This blocks periodic, recurrent, and local-extremum energy shortcuts at any nonzero witness time. It still does not construct the required positive-viscosity pressure-slice closure."

/-- Positive-viscosity nonzero time slices force strictly negative normalized
energy derivative. -/
def navierNonzeroSchwartzPointwiseStrictDerivativeNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-pointwise-strict-derivative"
  status := .checked
  truthValue := ⟨92, 90⟩
  evidence := "coordinateEnergyDissipationRate_pos_of_exists_velocity_ne_zero and normalizedKineticEnergy_derivative_lt_zero_of_exists_velocity_ne_zero prove that, at positive viscosity, any time slice with a nonzero velocity value has strictly positive corrected dissipation, and every derivative witness for normalized kinetic energy at that time is strictly negative. The nonzero-interface no-go excludes any nonzero witness time with a nonnegative energy derivative. PLN STV <s=.92,c=.90>, ITV [.828,.928], PROGRESS 74%."
  blocker := "This turns the energy identity into a pointwise-in-time canary constraint. It still does not construct the required positive-viscosity pressure-slice closure."

/-- Positive-viscosity nonzero canaries cannot hide a witness on a local
normalized-energy plateau. -/
def navierNonzeroSchwartzLocalPlateauObstructionNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-local-plateau-obstruction"
  status := .checked
  truthValue := ⟨92, 89⟩
  evidence := "velocity_eq_zero_of_eventually_eq_normalizedKineticEnergy_of_pos_viscosity proves that a locally constant normalized-energy neighborhood at positive viscosity forces the velocity slice to vanish. The nonzero-interface and global no-go forms rule out any nonzero witness time on such a plateau. PLN STV <s=.92,c=.89>, ITV [.8188,.9288], PROGRESS 75%."
  blocker := "This blocks plateau and local equilibrium shortcuts at any nonzero witness time. It still does not construct the required positive-viscosity pressure-slice closure."

/-- Positive-viscosity nonzero canaries must immediately dissipate to the
right of any nonzero witness time. -/
def navierNonzeroSchwartzImmediateRightDropNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-immediate-right-drop"
  status := .checked
  truthValue := ⟨93, 89⟩
  evidence := "eventually_right_lt_of_hasDerivAt_lt_zero and normalizedKineticEnergy_eventually_right_lt_of_exists_velocity_ne_zero prove that any positive-viscosity nonzero witness time has normalized kinetic energy eventually strictly lower on the right. The nonzero-interface and global no-go forms rule out witness times with eventually right-nondecreasing normalized energy. PLN STV <s=.93,c=.89>, ITV [.8277,.9377], PROGRESS 76%."
  blocker := "This turns the pointwise derivative gate into an immediate one-sided energy-drop requirement. It still does not construct the required positive-viscosity pressure-slice closure."

/-- Positive-viscosity nonzero canaries must expose actual right-drop samples
arbitrarily close to any nonzero witness time. -/
def navierNonzeroSchwartzRightDropSampleNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-right-drop-sample"
  status := .checked
  truthValue := ⟨94, 89⟩
  evidence := "exists_right_drop_sample_of_eventually_right_lt, exists_normalizedKineticEnergy_right_drop_sample_of_exists_velocity_ne_zero, and exists_normalizedKineticEnergy_right_drop_sample_at_nonzero_of_pos_viscosity prove that every positive-viscosity nonzero witness time has, inside every positive right interval, an actual later sample with strictly smaller normalized kinetic energy. PLN STV <s=.94,c=.89>, ITV [.8366,.9466], PROGRESS 77%."
  blocker := "This converts the one-sided energy drop into a generator-testable sampled witness requirement. It still does not construct the required positive-viscosity pressure-slice closure."

/-- Positive-viscosity nonzero canaries must strictly lose normalized energy
at every later endpoint after a nonzero witness time. -/
def navierNonzeroSchwartzStrictFutureDropNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-strict-future-drop"
  status := .checked
  truthValue := ⟨95, 89⟩
  evidence := "normalizedKineticEnergy_strict_lt_of_exists_velocity_ne_zero_left and normalizedKineticEnergy_strict_lt_after_nonzero_of_pos_viscosity combine the sampled right-drop gate with global antitonicity to prove that every later endpoint after a positive-viscosity nonzero witness time has strictly smaller normalized kinetic energy. The global no-go theorem rules out endpoint-nondecreasing recurrence after such a witness. PLN STV <s=.95,c=.89>, ITV [.8455,.9555], PROGRESS 78%."
  blocker := "This upgrades the local sampled-drop gate into a reusable future-endpoint filter for candidate generators. It still does not construct the required positive-viscosity pressure-slice closure."

/-- Positive-viscosity nonzero canaries cannot have periodic energy or
periodic velocity. -/
def navierNonzeroSchwartzNoEnergyRecurrenceNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-no-energy-recurrence"
  status := .checked
  truthValue := ⟨95, 89⟩
  evidence := "normalizedKineticEnergy_eq_of_velocity_slice_eq, normalizedKineticEnergy_ne_periodic_endpoint_at_nonzero_of_pos_viscosity, not_forall_normalizedKineticEnergy_periodic_of_pos_viscosity, and not_forall_velocity_periodic_of_pos_viscosity prove that a positive-viscosity nonzero slice-Schwartz solution cannot return normalized kinetic energy, or the velocity field itself, after any positive period. PLN STV <s=.95,c=.89>, ITV [.8455,.9555], PROGRESS 79%."
  blocker := "This rules out periodic and recurrent positive-viscosity shortcut canaries, but it still does not construct the required positive-viscosity pressure-slice closure."

/-- Pressure residual curl is now a reusable exact-closure gate. -/
def navierSchwartzPressureResidualCurlGateNode : NavierProofNode where
  id := "navier.energy.schwartz-pressure-residual-curl-gate"
  status := .checked
  truthValue := ⟨87, 89⟩
  evidence := "momentumPressureResidual_spatialVorticity_zero proves that every ordinary slice-Schwartz concrete solution has curl-free pressure residual νΔu - ∂tu - (u.grad)u, and not_exists_schwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero proves that any velocity whose residual curl is nonzero somewhere cannot inhabit the interface. The regression undamped_unit_heat_shear_not_schwartz_solution_velocity_regression applies this gate to an explicit heat-shear false positive. PLN STV <s=.87,c=.89>, ITV [.7743,.8843], PROGRESS 70%."
  blocker := "This is a sharp pressure-closure filter for candidate velocities. It does not construct the required nonzero localized Schwartz pressure-slice closure."

/-- The two-mode generator now exposes the exact residual-curl obligation at
the slice-Schwartz solution interface. -/
def navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-finite-mode-residual-curl-boundary"
  status := .checked
  truthValue := ⟨89, 90⟩
  evidence := "SchwartzMomentumClosureKernel and SchwartzConcreteSolutionKernel factor the momentum equation, divergence, pressure-residual equality, and residual-curl-zero condition out of any slice-Schwartz concrete solution. oneOneTwoModeSchwartzVelocity_lapSum_residualVorticity_zero_of_schwartzConcreteSolution and the not_exists_* residual-vorticity theorems specialize this to the constant-amplitude two-mode generator: once the inviscid convection closure is supplied, the viscous Laplacian residual must be curl-free everywhere or no pressure slices can make the velocity inhabit the ordinary or nonzero slice-Schwartz concrete interface. PLN STV <s=.89,c=.90>, ITV [.801,.901], PROGRESS 72%."
  blocker := "This turns the two-mode pressure-closure search into a concrete curl-free residual obligation. It still does not provide explicit nonzero profiles satisfying the inviscid closure, curl-free viscous residual, and pressure-slice equation."

/-- Stationary inviscid one-profile data now have a direct nonzero
slice-Schwartz constructor once the pressure closure is supplied. -/
def navierNonzeroSchwartzStationaryInviscidConstructorNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-stationary-inviscid-constructor"
  status := .checked
  truthValue := ⟨76, 88⟩
  evidence := "stationaryInviscidSchwartzPressureSlice_nonzeroSchwartzConcreteSolution and stationaryInviscidSchwartzPressureSlice_nonzero_concreteSolutionKernel prove that any nonzero divergence-free Schwartz initial velocity with a Schwartz pressure slice satisfying the stationary inviscid pointwise closure inhabits NonzeroSchwartzConcreteNavierStokesSolution at viscosity 0 and carries SchwartzConcreteSolutionKernel. PLN STV <s=.76,c=.88>, ITV [.6688,.7888], PROGRESS 73%."
  blocker := "This exposes the exact stationary localized Euler-style pressure-closure seam. It is still conditional on an explicit closure witness and works at viscosity 0, so it does not satisfy the positive-viscosity nonzero canary obligation."

/-- The exact Stokes-flow subroute is now separated as a reusable kernel. -/
def navierNonzeroSchwartzStokesKernelNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-stokes-kernel"
  status := .checked
  truthValue := ⟨82, 88⟩
  evidence := "SchwartzStokesFlowKernel packages any slice-Schwartz concrete solution whose convection and pressure-gradient terms vanish into the exact Stokes equation partial_t u = nu*Delta u plus the inherited concrete solution kernel. NonzeroSchwartzConcreteNavierStokesSolution.stokesFlow_strictDissipation_packet proves that every positive-viscosity nonzero inhabitant of this subroute has a strict negative normalized-energy derivative at some time, and stokesFlow_not_forall_velocity_periodic_of_pos_viscosity plus not_exists_nonzeroSchwartzStokesFlow_velocity_periodic_of_pos_viscosity rule out positive-period recurrent Stokes shortcuts. PLN STV <s=.82,c=.88>, ITV [.7216,.8416], PROGRESS 82%."
  blocker := "This is still conditional on an inhabited positive-viscosity nonzero Stokes-flow solution. The remaining canary obligation is to construct such a bounded whole-real-time Schwartz heat/Stokes evolution, or prove the bounded-eternal Stokes subroute is empty."

/-- Exact Stokes-flow canaries must break fixed-direction rank-one shear form. -/
def navierNonzeroSchwartzStokesRankOneObstructionNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-stokes-rankone-obstruction"
  status := .checked
  truthValue := ⟨85, 88⟩
  evidence := "stokesFlow_not_forall_velocitySlice_rankOne_of_fixed_direction lifts the rank-one zero-convection obstruction into the exact Stokes-flow subroute: a nonzero Stokes candidate cannot have every velocity slice in one fixed nonzero rank-one Schwartz direction. stokesFlow_exists_velocitySlice_not_rankOne_of_fixed_direction gives the positive escape form, and stokesFlow_strictDissipation_and_non_rankOne_slice_packet combines that escape with the strict positive-viscosity dissipation packet. PLN STV <s=.85,c=.88>, ITV [.7480,.8680], PROGRESS 85%."
  blocker := "This closes the fixed-direction rank-one Stokes/shear shortcut. It still leaves genuinely non-rank-one pressure/time-evolution closure, or a full bounded whole-real-time Stokes-subroute emptiness theorem, as the remaining positive-canary seam."

/-- Zero kinetic energy on a Schwartz slice blocks later restart. -/
def navierNonzeroSchwartzZeroRestartNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-zero-restart-obstruction"
  status := .checked
  truthValue := ⟨84, 88⟩
  evidence := "SchwartzZeroRestartKernel factors kinetic-energy zero-rigidity and the no-future-restart gate out of every slice-Schwartz concrete solution: kineticEnergyAt_eq_zero_of_velocity_eq_zero_at, velocity_eq_zero_of_kineticEnergyAt_eq_zero, and velocity_eq_zero_at_later_of_velocity_eq_zero_at_of_nonneg_viscosity prove that at nonnegative viscosity a pointwise zero slice cannot be followed by a later nonzero slice. exists_velocity_ne_zero_at_or_before_nonzero_of_nonneg_viscosity and exists_nonzero_witness_with_nonzero_at_all_prior_times give the positive past-nonzero form, while not_exists_nonzeroSchwartzConcreteSolution_zero_slice_before_nonzero_of_nonneg_viscosity and the Stokes-flow specialization block zero-to-nonzero restart shortcuts in the general and zero-convection/zero-pressure-gradient subroutes. PLN STV <s=.84,c=.88>, ITV [.7392,.8592], PROGRESS 84%."
  blocker := "This removes zero-restart shortcuts and turns zero slices into absorbing future states for the current energy interface. It still does not construct the required positive-viscosity nonzero slice-Schwartz inhabitant or prove the entire bounded-eternal Stokes/pressure-closure subroute empty."

/-- Positive-viscosity nonzero solutions have a whole past ray of strict
dissipation before some nonzero witness. -/
def navierNonzeroSchwartzPastDissipationNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-past-dissipation-ray"
  status := .checked
  truthValue := ⟨86, 88⟩
  evidence := "exists_nonzero_witness_with_strict_dissipation_at_all_prior_times combines the zero-restart gate with strict positive-viscosity dissipation: before a chosen nonzero witness, every earlier slice is nonzero somewhere, has positive corrected dissipation, and satisfies the exact energy identity with a strictly negative derivative. exists_nonzero_witness_with_strict_past_energy_drop proves normalized kinetic energy strictly drops across every nontrivial forward interval ending no later than that witness, and stokesFlow_past_strictDissipation_packet specializes the ray to exact Stokes-flow candidates. PLN STV <s=.86,c=.88>, ITV [.7568,.8768], PROGRESS 86%."
  blocker := "This gives a reusable half-line obstruction for positive-viscosity canaries. It still does not construct an exact nonzero slice-Schwartz inhabitant or prove that every bounded eternal Stokes/pressure-closure candidate is impossible."

/-- Later nonzero endpoints force all earlier support and strict past energy
ordering. -/
def navierNonzeroSchwartzEndpointSupportNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-endpoint-support"
  status := .checked
  truthValue := ⟨88, 89⟩
  evidence := "SchwartzNonzeroTimeSupportKernel factors the endpoint-parametric support consequence out of the slice-Schwartz interface: exists_velocity_ne_zero_at_or_before_nonzero_endpoint_of_nonneg_viscosity proves any later nonzero endpoint forces every earlier slice to be nonzero somewhere, normalizedKineticEnergy_strict_lt_before_nonzero_endpoint_of_pos_viscosity proves strict normalized-energy drop on every earlier nontrivial interval before that endpoint, and not_exists_nonzeroSchwartzConcreteSolution_energy_nondecrease_before_nonzero_endpoint_of_pos_viscosity rejects nondecreasing-energy subintervals before a later nonzero endpoint. PLN STV <s=.88,c=.89>, ITV [.7832,.8932], PROGRESS 87%."
  blocker := "This upgrades the past-dissipation ray from an existential witness to a reusable endpoint API, but it still does not construct the required positive-viscosity nonzero solution or prove the bounded-eternal Stokes subroute empty. A quantitative lower-bound or spectral-gap input is still needed for a full Stokes emptiness obstruction."

/-- Bounded eternal slice-Schwartz solutions cannot carry a uniform positive
past dissipation gap. -/
def navierNonzeroSchwartzNoUniformPastDissipationNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-no-uniform-past-dissipation"
  status := .checked
  truthValue := ⟨91, 89⟩
  evidence := "not_forall_past_coordinateEnergyDissipationRate_ge proves that bounded whole-time slice-Schwartz concrete solutions cannot keep corrected coordinate dissipation uniformly above any positive constant on an entire past ray. exists_past_nonzero_with_small_positive_coordinateEnergyDissipationRate proves that, at positive viscosity before a later nonzero endpoint, every positive threshold has an earlier nonzero slice with strictly positive but smaller corrected dissipation. not_forall_past_coordinateEnergyDissipationRate_ge_mul_normalizedKineticEnergy and not_exists_nonzeroSchwartzConcreteSolution_past_spectral_floor rule out positive whole-past Poincare/spectral floors of the form lambda times normalized energy below corrected dissipation, and stokesFlow_noUniformPastDissipation_packet plus stokesFlow_noPastSpectralFloor_packet specialize the obstruction to exact Stokes-flow candidates. PLN STV <s=.91,c=.89>, ITV [.8099,.9199], PROGRESS 89%."
  blocker := "This rules out uniform positive past dissipation and Poincare/spectral-floor certificates for bounded eternal positive-viscosity canaries, including the Stokes subroute. It still does not construct the required nonzero inhabitant or prove the full bounded-eternal Stokes/pressure-closure subroute empty without a stronger structural lower-bound hypothesis."

/-- The explicit nonzero slice-Schwartz canary remains open until the
finite-mode closure hypotheses are inhabited by concrete profiles. -/
def navierNonzeroSchwartzCanaryNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-canary"
  status := .openGoal
  truthValue := ⟨80, 87⟩
  evidence := "The checked nonzero kernel removes the old zero-flow loophole from the energy-identity surface; the line-invariant, exact heat-shear boundary, rank-one zero-convection, symmetric-shear, nilpotent-shear pressure-residual, frozen nilpotent-slice, anti-profile cancellation, exact anti-profile amplitude-boundary, positive-viscosity stationary, strict-dissipation-kernel, flat-energy zero-rigidity, local-extremum energy, pointwise strict-derivative, local energy plateau, immediate right-drop, sampled right-drop, strict future-drop, energy-recurrence, generic pressure-residual-curl, finite-mode residual-curl, stationary-inviscid constructor, Stokes-flow kernel, Stokes rank-one obstruction, generalized zero-restart gates, past-dissipation ray, endpoint nonzero-support kernel, no-uniform-past-dissipation obstruction, and no-past-spectral-floor obstruction remove, constrain, or expose twenty-eight shortcut classes at stronger interfaces; and the localized stream-function seed gives a concrete nonzero divergence-free Schwartz datum. No unconditional positive-viscosity nonzero exact slice-Schwartz solution inhabitant is committed yet. PLN STV <s=.80,c=.87>, ITV [.6960,.8260], PROGRESS 88%."
  blocker := "Close or refute the pressure-slice closure and time evolution for the explicit localized stream-function seed or a comparable non-polynomial Schwartz profile; do not count a conditional constructor, seed-only datum, classical heat-shear exact solution that fails Schwartz decay, rank-one zero-convection obstruction, nilpotent-shear pressure-residual obstruction, frozen nilpotent-slice obstruction, profile-level nonzero anti-profile cancellation, an amplitude-boundary guardrail, a positive-viscosity stationary obstruction, a strict-dissipation theorem conditional on the nonzero interface, a flat-energy zero-rigidity obstruction, a local-extremum energy obstruction, a pointwise strict-derivative gate, a local energy plateau obstruction, an immediate right-drop gate, a sampled right-drop gate, a strict future-drop gate, an energy-recurrence obstruction, a residual-curl pressure-closure rejection, a finite-mode residual-curl boundary, a stationary inviscid closure constructor, a conditional Stokes-flow kernel, a Stokes rank-one obstruction, a zero-restart obstruction, a past-dissipation ray theorem, an endpoint support-order theorem, a no-uniform-past-dissipation theorem, a no-past-spectral-floor theorem, or algebraic finite-mode boundary case as the requested positive canary."

/-- Supercritical scaling remains a route obstacle, not a closed theorem here. -/
def navierSupercriticalScalingNode : NavierProofNode where
  id := "navier.supercritical-scaling"
  status := .scalingUncleared
  truthValue := ⟨0, 98⟩
  evidence := "currentNavierEnergyBKMRoute_scaling_and_world_interface_packet, currentNavierEnergyBKMRoute_averagedEquationCompatibility_obligation_packet, currentNavierEnergyBKMRoute_averagedEquationFrontier_packet, and currentNavierEnergyBKMRoute_regularityPromotionGate_refuted record that the finite-energy/BKM route is blocked at the critical-norm and supercritical-upgrade gates; averaged-equation compatibility has four missing obligations and no represented witness; the route supplies only the finite-energy L2 diagnostic and misses all required critical, supercritical, and averaged-equation challenge-world interfaces. The finite-energy L2 diagnostic is supercritical against the L3 critical index."
  blocker := "Do not promote this route to global regularity unless the critical-norm and supercritical-upgrade blocks are replaced by checked clearance theorems, the averaged-equation obligation packet is represented, and the required challenge-world interfaces are supplied."

/-- Finite critical-norm canaries keep invalid replacements out of the route. -/
def navierCriticalNormCanariesNode : NavierProofNode where
  id := "navier.scaling.critical-norm-canaries"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "navierCriticalNormCanaries_guardrails and navierCurrentEnergyBKMRouteCriticalNormCanary_obstruction record that L3 or L4 diagnostics with both critical-world interfaces clear the finite gate, while finite-energy L2 alone, L3 without the norm-control witness, and L2 with interfaces do not."
  blocker := "The current finite-energy/BKM route still supplies only the L2 diagnostic and lacks critical-world interfaces, so these canaries do not clear the analytic global-regularity route."

/-- Averaged-equation compatibility now exposes its exact missing-obligation frontier. -/
def navierAveragedEquationFrontierNode : NavierProofNode where
  id := "navier.averaged-equation-frontier"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "currentNavierEnergyBKMRoute_averagedEquationFrontier_packet records the positive fully represented bookkeeping case and the current finite-energy/BKM route's four missing obligations: averaged momentum equation, Reynolds-stress closure, energy-inequality compatibility, and critical-scaling compatibility."
  blocker := "Represent or refute one of the four averaged-equation obligations before using averaged-equation evidence in a global regularity route."

/-- Averaged-equation canaries keep obligation evidence separate from interfaces. -/
def navierAveragedEquationInterfaceCanariesNode : NavierProofNode where
  id := "navier.averaged-equation-interface-canaries"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "navierAveragedEquationCanaries_guardrails and navierCurrentEnergyBKMRouteAveragedEquationCanary_obstruction record that all obligations plus all averaged-equation interfaces clear the finite gate, while obligation-only evidence, interface-only evidence, witness interfaces without the averaged-equation world family, and averaged-momentum-only evidence do not."
  blocker := "A route using averaged-equation evidence must still supply represented witnesses for all four averaged-equation obligations and all averaged-equation challenge-world interfaces before any global regularity promotion."

/-- The averaged-momentum equation obstruction is now a first-class route node. -/
def navierAveragedMomentumObstructionNode : NavierProofNode where
  id := "navier.averaged-momentum-obstruction"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "currentNavierEnergyBKMRoute_averagedMomentumEquation_obstruction records that the current finite-energy/BKM route neither represents averagedMomentumEquation nor supplies its required averagedMomentumWitness challenge-world interface."
  blocker := "A route using averaged-equation evidence must either supply a checked averaged-momentum equation witness or replace this finite-energy/BKM route with a sharper obstruction/refutation."

/-- Finite averaged-momentum canaries reject label-only balance substitutes. -/
def navierAveragedMomentumCanariesNode : NavierProofNode where
  id := "navier.averaged-momentum-canaries"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "navierAveragedMomentumCanaries_guardrails and navierCurrentEnergyBKMRouteAveragedMomentumCanary_obstruction record that componentwise residual balance plus the averaged-equation world family and averaged-momentum witness clear the finite gate, while witness-label mismatch, scalar balance, missing world-family evidence, pointwise flags, and finite-energy L2 bookkeeping do not."
  blocker := "The current finite-energy/BKM route still supplies only the L2 diagnostic and lacks both the averaged-equation world family and averaged-momentum witness."

/-- The Reynolds-stress closure obstruction is now a first-class route node. -/
def navierReynoldsStressClosureObstructionNode : NavierProofNode where
  id := "navier.reynolds-stress-closure-obstruction"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "currentNavierEnergyBKMRoute_reynoldsStressClosure_obstruction records that the current finite-energy/BKM route neither represents reynoldsStressClosure nor supplies its required reynoldsStressClosureWitness challenge-world interface."
  blocker := "A route using averaged-equation evidence must either supply a checked Reynolds-stress closure witness or replace this finite-energy/BKM route before any global regularity promotion."

/-- Finite Reynolds-stress closure canaries reject label-only closure substitutes. -/
def navierReynoldsStressClosureCanariesNode : NavierProofNode where
  id := "navier.reynolds-stress-closure-canaries"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "navierReynoldsStressClosureCanaries_guardrails and navierCurrentEnergyBKMRouteReynoldsStressClosureCanary_obstruction record that a closure witness plus componentwise residual matching clears the finite gate, while witness-label mismatch, scalar trace, symmetry without a witness, and zero-flow flags do not."
  blocker := "The current finite-energy/BKM route still lacks a represented Reynolds-stress closure witness, so these finite canaries do not clear the averaged-equation route."

/-- The energy-inequality compatibility obstruction is now a first-class route node. -/
def navierEnergyInequalityCompatibilityObstructionNode : NavierProofNode where
  id := "navier.energy-inequality-compatibility-obstruction"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "currentNavierEnergyBKMRoute_energyInequalityCompatibility_obstruction records that the current finite-energy/BKM route neither represents energyInequalityCompatibility nor supplies its required energyInequalityTransport challenge-world interface."
  blocker := "A route using averaged-equation evidence must either supply a checked energy-inequality transport witness or replace this finite-energy/BKM route before any global regularity promotion."

/-- Finite energy-inequality transport canaries reject endpoint-only substitutes. -/
def navierEnergyInequalityTransportCanariesNode : NavierProofNode where
  id := "navier.energy-inequality-transport-canaries"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "navierEnergyInequalityTransportCanaries_guardrails and navierCurrentEnergyBKMRouteEnergyInequalityTransportCanary_obstruction record that a transport witness plus a full finite energy budget clears the finite gate, while witness-label budget violations, endpoint-only evidence, finite-energy L2 bookkeeping, and local-inequality flags do not."
  blocker := "The current finite-energy/BKM route still supplies only the L2 diagnostic and lacks an energy-inequality transport witness, so these finite canaries do not clear the averaged-equation route."

/-- The critical-scaling compatibility obstruction is now a first-class route node. -/
def navierCriticalScalingCompatibilityObstructionNode : NavierProofNode where
  id := "navier.critical-scaling-compatibility-obstruction"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "currentNavierEnergyBKMRoute_criticalScalingCompatibility_obstruction records that the current finite-energy/BKM route neither represents criticalScalingCompatibility nor supplies its required criticalScalingTransport challenge-world interface."
  blocker := "A route using averaged-equation evidence must either supply a checked critical-scaling transport witness or replace this finite-energy/BKM route before any global regularity promotion."

/-- Finite critical-scaling transport canaries reject weaker transport substitutes. -/
def navierCriticalScalingTransportCanariesNode : NavierProofNode where
  id := "navier.critical-scaling-transport-canaries"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "navierCriticalScalingTransportCanaries_guardrails and navierCurrentEnergyBKMRouteCriticalScalingTransportCanary_obstruction record that preserved L3 or L4 diagnostics with a critical-scaling transport witness clear the finite gate, while L2 labels, missing transport witnesses, energy-transport-only evidence, critical-to-supercritical transport, and nonpreserving L4-to-L3 transport do not."
  blocker := "The current finite-energy/BKM route still supplies only the L2 diagnostic and lacks a critical-scaling transport witness, so these finite canaries do not clear the averaged-equation route."

/-- The four averaged-equation obstructions are consolidated as one route packet. -/
def navierAveragedEquationAllObstructionsNode : NavierProofNode where
  id := "navier.averaged-equation-all-obstructions"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "currentNavierEnergyBKMRoute_allAveragedEquationObstructions consolidates the averaged-equation obligation packet, frontier packet, and all four missing obligation/interface obstructions."
  blocker := "A route using averaged-equation evidence must replace this packet with checked witnesses for averaged momentum, Reynolds-stress closure, energy-inequality transport, and critical-scaling transport."

/-- The finite-energy/BKM route fails the combined global-regularity promotion gate. -/
def navierRegularityPromotionGateNode : NavierProofNode where
  id := "navier.regularity-promotion-gate"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "currentNavierEnergyBKMRoute_regularityPromotionGate_refuted records that the finite-energy/BKM route fails all three promotion layers: scaling verdicts, challenge-world interfaces, and averaged-equation compatibility. It also records that the finite-energy L2 diagnostic is supercritical and does not clear critical promotion."
  blocker := "A replacement global route must clear scaling verdicts, supply critical/supercritical/averaged challenge-world interfaces, and represent averaged-equation compatibility before any regularity endpoint is advertised."

/-- Finite regularity-promotion canaries reject layer-only promotion substitutes. -/
def navierRegularityPromotionLayerCanariesNode : NavierProofNode where
  id := "navier.regularity-promotion-layer-canaries"
  status := .scalingUncleared
  truthValue := ⟨0, 99⟩
  evidence := "navierRegularityPromotionLayerOmissions_guardrails records that all three layers clear in the full toy gate, while scaling-only, world-interface-only, averaged-equation-only, and every two-layer omission shape fail the finite regularity-promotion gate."
  blocker := "Do not replace the three-layer regularity-promotion gate by any single layer or pair of layers."

/-- Central Navier-Stokes route nodes currently tracked by the live lane. -/
def currentNavierProofNodes : List NavierProofNode :=
  [ navierLiveSurfaceNode
  , navierConcreteTargetNode
  , navierFiniteEnergyTargetNode
  , navierEnergyBKMConstantVelocityNode
  , navierEnergyBKMHeatShearNode
  , navierFeffermanLiftNode
  , navierDEGroundedZeroCanaryNode
  , navierSchwartzEnergyIdentityNode
  , navierNonzeroSchwartzEnergyKernelNode
  , navierNonzeroSchwartzLineInvariantObstructionNode
  , navierNonzeroSchwartzHeatShearBoundaryNode
  , navierNonzeroSchwartzRankOneShearObstructionNode
  , navierNonzeroSchwartzSymmetricShearObstructionNode
  , navierNonzeroSchwartzNilpotentShearPressureObstructionNode
  , navierNonzeroSchwartzLocalizedStreamSeedNode
  , navierNonzeroSchwartzAntiProfileCanaryObstructionNode
  , navierNonzeroSchwartzAntiProfileAmplitudeBoundaryNode
  , navierNonzeroSchwartzStationaryDissipationGateNode
  , navierNonzeroSchwartzStrictDissipationKernelNode
  , navierNonzeroSchwartzNoFlatEnergyObstructionNode
  , navierNonzeroSchwartzLocalExtremumEnergyObstructionNode
  , navierNonzeroSchwartzPointwiseStrictDerivativeNode
  , navierNonzeroSchwartzLocalPlateauObstructionNode
  , navierNonzeroSchwartzImmediateRightDropNode
  , navierNonzeroSchwartzRightDropSampleNode
  , navierNonzeroSchwartzStrictFutureDropNode
  , navierNonzeroSchwartzNoEnergyRecurrenceNode
  , navierSchwartzPressureResidualCurlGateNode
  , navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode
  , navierNonzeroSchwartzStationaryInviscidConstructorNode
  , navierNonzeroSchwartzStokesKernelNode
  , navierNonzeroSchwartzStokesRankOneObstructionNode
  , navierNonzeroSchwartzZeroRestartNode
  , navierNonzeroSchwartzPastDissipationNode
  , navierNonzeroSchwartzEndpointSupportNode
  , navierNonzeroSchwartzNoUniformPastDissipationNode
  , navierNonzeroSchwartzCanaryNode
  , navierSupercriticalScalingNode
  , navierCriticalNormCanariesNode
  , navierAveragedEquationFrontierNode
  , navierAveragedEquationInterfaceCanariesNode
  , navierAveragedMomentumObstructionNode
  , navierAveragedMomentumCanariesNode
  , navierReynoldsStressClosureObstructionNode
  , navierReynoldsStressClosureCanariesNode
  , navierEnergyInequalityCompatibilityObstructionNode
  , navierEnergyInequalityTransportCanariesNode
  , navierCriticalScalingCompatibilityObstructionNode
  , navierCriticalScalingTransportCanariesNode
  , navierAveragedEquationAllObstructionsNode
  , navierRegularityPromotionGateNode
  , navierRegularityPromotionLayerCanariesNode
  ]

theorem currentNavierProofNodes_nonempty : currentNavierProofNodes ≠ [] := by
  simp [currentNavierProofNodes]

theorem navierEnergyBKMConstantVelocityNode_refuted :
    navierEnergyBKMConstantVelocityNode.status = .refuted := by
  rfl

theorem navierEnergyBKMHeatShearNode_refuted :
    navierEnergyBKMHeatShearNode.status = .refuted := by
  rfl

theorem navierSupercriticalScalingNode_uncleared :
    navierSupercriticalScalingNode.status = .scalingUncleared := by
  rfl

theorem navierFeffermanLiftNode_retiredPlaceholder :
    navierFeffermanLiftNode.status = .retiredPlaceholder := by
  rfl

theorem navierDEGroundedZeroCanaryNode_checked :
    navierDEGroundedZeroCanaryNode.status = .checked := by
  rfl

theorem navierSchwartzEnergyIdentityNode_checked :
    navierSchwartzEnergyIdentityNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzEnergyKernelNode_checked :
    navierNonzeroSchwartzEnergyKernelNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzLineInvariantObstructionNode_checked :
    navierNonzeroSchwartzLineInvariantObstructionNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzHeatShearBoundaryNode_checked :
    navierNonzeroSchwartzHeatShearBoundaryNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzRankOneShearObstructionNode_checked :
    navierNonzeroSchwartzRankOneShearObstructionNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzSymmetricShearObstructionNode_checked :
    navierNonzeroSchwartzSymmetricShearObstructionNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzNilpotentShearPressureObstructionNode_checked :
    navierNonzeroSchwartzNilpotentShearPressureObstructionNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzLocalizedStreamSeedNode_checked :
    navierNonzeroSchwartzLocalizedStreamSeedNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzAntiProfileCanaryObstructionNode_checked :
    navierNonzeroSchwartzAntiProfileCanaryObstructionNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzAntiProfileAmplitudeBoundaryNode_checked :
    navierNonzeroSchwartzAntiProfileAmplitudeBoundaryNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzStationaryDissipationGateNode_checked :
    navierNonzeroSchwartzStationaryDissipationGateNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzStrictDissipationKernelNode_checked :
    navierNonzeroSchwartzStrictDissipationKernelNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzNoFlatEnergyObstructionNode_checked :
    navierNonzeroSchwartzNoFlatEnergyObstructionNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzLocalExtremumEnergyObstructionNode_checked :
    navierNonzeroSchwartzLocalExtremumEnergyObstructionNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzPointwiseStrictDerivativeNode_checked :
    navierNonzeroSchwartzPointwiseStrictDerivativeNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzLocalPlateauObstructionNode_checked :
    navierNonzeroSchwartzLocalPlateauObstructionNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzImmediateRightDropNode_checked :
    navierNonzeroSchwartzImmediateRightDropNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzRightDropSampleNode_checked :
    navierNonzeroSchwartzRightDropSampleNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzStrictFutureDropNode_checked :
    navierNonzeroSchwartzStrictFutureDropNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzNoEnergyRecurrenceNode_checked :
    navierNonzeroSchwartzNoEnergyRecurrenceNode.status = .checked := by
  rfl

theorem navierSchwartzPressureResidualCurlGateNode_checked :
    navierSchwartzPressureResidualCurlGateNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode_checked :
    navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzStationaryInviscidConstructorNode_checked :
    navierNonzeroSchwartzStationaryInviscidConstructorNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzStokesKernelNode_checked :
    navierNonzeroSchwartzStokesKernelNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzStokesRankOneObstructionNode_checked :
    navierNonzeroSchwartzStokesRankOneObstructionNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzZeroRestartNode_checked :
    navierNonzeroSchwartzZeroRestartNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzPastDissipationNode_checked :
    navierNonzeroSchwartzPastDissipationNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzEndpointSupportNode_checked :
    navierNonzeroSchwartzEndpointSupportNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzNoUniformPastDissipationNode_checked :
    navierNonzeroSchwartzNoUniformPastDissipationNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzCanaryNode_open :
    navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  rfl

theorem currentNavierDEGroundedZeroCanary_node :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        concreteNSZeroProblemData ∧
      (∀ term : ConcreteNSMomentumTerm, term.scalingExponent = 3) ∧
      velocityLpPowerScalingExponent 2 = -1 ∧
      velocityLpPowerScalingExponent 3 = 0 ∧
      velocityLpPowerScalingExponent 4 = 1 ∧
      navierDEGroundedZeroCanaryNode.status = .checked := by
  exact
    ⟨concreteNSZeroCanary_and_scaling_packet.1,
      concreteNSZeroCanary_and_scaling_packet.2.1,
      concreteNSZeroCanary_and_scaling_packet.2.2.1,
      concreteNSZeroCanary_and_scaling_packet.2.2.2.1,
      concreteNSZeroCanary_and_scaling_packet.2.2.2.2,
      navierDEGroundedZeroCanaryNode_checked⟩

theorem currentNavierSchwartzEnergyIdentity_node
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν) :
    (∀ t, ∫ x, pressureEnergyPairing S.velocity S.pressure t x ∂volume = 0) ∧
      (∀ t, ∫ x, convectionEnergyPairing S.velocity t x ∂volume = 0) ∧
      CoordinateViscousEnergyPairingFormula S.velocity ∧
      (∀ t,
        HasDerivAt (normalizedKineticEnergy S.velocity)
          (-(coordinateEnergyDissipationRate S.velocity ν t)) t) ∧
      navierSchwartzEnergyIdentityNode.status = .checked := by
  exact
    ⟨S.pressureEnergyCancellation,
      S.convectionEnergyCancellation,
      S.coordinateViscousEnergyPairingFormula,
      S.coordinateEnergyDissipationIdentity,
      navierSchwartzEnergyIdentityNode_checked⟩

theorem currentNavierNonzeroSchwartzEnergyKernel_node
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν) :
    (∃ t x, S.velocity t x ≠ 0) ∧
      SchwartzEnergyIdentityKernel ν S.velocity S.pressure ∧
      navierNonzeroSchwartzEnergyKernelNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨S.nonzero_velocity,
      S.energyIdentityKernel,
      navierNonzeroSchwartzEnergyKernelNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzLineInvariantObstruction_node
    {ν : ℝ} {v : NSSpace} (hv : v ≠ 0) :
    (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∀ t : NSTime,
        TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x)) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ t : NSTime,
          ¬ TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x)) ∧
      navierNonzeroSchwartzLineInvariantObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨not_exists_nonzeroSchwartzConcreteSolution_all_velocitySlices_translationInvariantAlong hv,
      fun S => every_nonzeroSchwartzConcreteSolution_has_non_lineInvariant_slice S hv,
      navierNonzeroSchwartzLineInvariantObstructionNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzHeatShearBoundary_node
    (ν : ℝ) {a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    (∃ t : NSTime, ∃ x : NSSpace, heatShearVelocityField ν a k t x ≠ 0) ∧
      (∀ t x, spatialDivergence (heatShearVelocityField ν a k) t x = 0) ∧
      (∀ t x,
        timeVelocityDerivative (heatShearVelocityField ν a k) t x +
            spatialConvection (heatShearVelocityField ν a k) t x +
            spatialPressureGradient (0 : NSPressureField) t x =
          ν • spatialLaplacian (heatShearVelocityField ν a k) t x) ∧
      (¬ ∃ S : SchwartzConcreteNavierStokesSolution ν,
        S.velocity = heatShearVelocityField ν a k) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        S.velocity = heatShearVelocityField ν a k) ∧
      (∀ μ : ℝ, μ ≠ ν →
        ¬ ∃ S : SchwartzConcreteNavierStokesSolution μ,
          S.velocity = heatShearVelocityField ν a k) ∧
      (∀ μ : ℝ, μ ≠ ν →
        ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution μ,
          S.velocity = heatShearVelocityField ν a k) ∧
      navierNonzeroSchwartzHeatShearBoundaryNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  rcases heatShearVelocityField_exact_nonzero_and_not_schwartzConcreteSolution
      ν ha hk with
    ⟨hnonzero, hdiv, heq, hnot, hnotNonzero⟩
  exact
    ⟨hnonzero, hdiv, heq, hnot, hnotNonzero,
      fun μ hμν =>
        not_exists_schwartzConcreteSolution_velocity_heatShearVelocityField_wrongViscosity
          hμν ha hk,
      fun μ hμν =>
        not_exists_nonzeroSchwartzConcreteSolution_velocity_heatShearVelocityField_wrongViscosity
          hμν ha hk,
      navierNonzeroSchwartzHeatShearBoundaryNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzRankOneShearObstruction_node
    {v : NSSpace} (hv : v ≠ 0) {t : NSTime} :
    (¬ ∃ φ : NSSchwartzScalar,
      (rankOneSchwartzVelocity φ v : NSInitialVelocity) ≠ 0 ∧
        ∀ x : NSSpace,
          spatialConvection
              (timeIndependentVelocity (rankOneSchwartzVelocity φ v : NSInitialVelocity))
              t x = 0) ∧
      navierNonzeroSchwartzRankOneShearObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨not_exists_nonzero_rankOneSchwartzVelocity_with_zero_spatialConvection hv,
      navierNonzeroSchwartzRankOneShearObstructionNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzRankOneShearSolutionLift_node
    {ν : ℝ} {v : NSSpace} (hv : v ≠ 0) :
    (∀ S : SchwartzConcreteNavierStokesSolution ν,
      ∀ t : NSTime,
        ∀ φ : NSSchwartzScalar,
          S.velocitySlice t = rankOneSchwartzVelocity φ v →
            (∀ x : NSSpace, spatialConvection S.velocity t x = 0) →
              ∀ x : NSSpace, S.velocity t x = 0) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ¬ ∀ t : NSTime,
          ∃ φ : NSSchwartzScalar,
            S.velocitySlice t = rankOneSchwartzVelocity φ v ∧
              ∀ x : NSSpace, spatialConvection S.velocity t x = 0) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∀ t : NSTime,
          ∃ φ : NSSchwartzScalar,
            S.velocitySlice t = rankOneSchwartzVelocity φ v ∧
              ∀ x : NSSpace, spatialConvection S.velocity t x = 0) ∧
      navierNonzeroSchwartzRankOneShearObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S t φ hslice hconv =>
        S.velocity_eq_zero_of_velocitySlice_eq_rankOne_zeroConvection_at
          φ hv hslice hconv,
      fun S =>
        S.not_forall_velocitySlice_rankOne_zeroConvection_of_fixed_direction hv,
      not_exists_nonzeroSchwartzConcreteSolution_forall_rankOne_zeroConvection hv,
      navierNonzeroSchwartzRankOneShearObstructionNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzSymmetricShearObstruction_node
    (ν ε : ℝ) {α : ℝ} (hα : α ≠ 0) :
    ((∃ b : ℝ → FiniteModeState FiniteModeAffineQuadraticPressureIndex,
      ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y =>
          finiteModePolynomialVectorFieldEval
            (finiteModeSymmetricShearPolynomialMode α i) y)
        finiteModeIdentityCoefficientCurve ∧
        p = finiteModeReconstructedPressure finiteModeAffineQuadraticPressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeSymmetricShearPolynomialMode α i) y)
              finiteModeAffineQuadraticPressureMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve b ∧
          (∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
          ∀ t x, spatialDivergence u t x = 0) ∧
      (∃ t x,
        finiteModeReconstructedVelocity
            (fun i y =>
              finiteModePolynomialVectorFieldEval
                (finiteModeSymmetricShearPolynomialMode α i) y)
            finiteModeIdentityCoefficientCurve t x ≠ 0) ∧
      ¬ ∃ u₀ : NSSchwartzInitialVelocity,
        (u₀ : NSInitialVelocity) =
          fun x : NSSpace =>
            finiteModeReconstructedVelocity
              (fun i y =>
                finiteModePolynomialVectorFieldEval
                  (finiteModeSymmetricShearPolynomialMode α i) y)
              finiteModeIdentityCoefficientCurve 1 x) ∧
      navierNonzeroSchwartzSymmetricShearObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨finiteModeSymmetricShear_exact_nonzero_and_not_schwartzSlice ν ε hα,
      navierNonzeroSchwartzSymmetricShearObstructionNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzNilpotentShearPressureObstruction_node
    (ν : ℝ) :
    (∀ t x, spatialDivergence nilpotentLinearShearVelocityField t x = 0) ∧
      (∀ t x, spatialLaplacian nilpotentLinearShearVelocityField t x = 0) ∧
      (∀ t x,
        spatialConvection nilpotentLinearShearVelocityField t x =
          EuclideanSpace.single nsCoord0 (x nsCoord2)) ∧
      (∀ t x,
        spatialVorticity (momentumPressureResidual ν nilpotentLinearShearVelocityField) t x =
          EuclideanSpace.single nsCoord1 (-1 : ℝ)) ∧
      (¬ ∃ p : NSPressureField,
        smoothSpaceTimePressure p ∧
          ∀ t x,
            timeVelocityDerivative nilpotentLinearShearVelocityField t x +
                spatialConvection nilpotentLinearShearVelocityField t x +
                spatialPressureGradient p t x =
              ν • spatialLaplacian nilpotentLinearShearVelocityField t x) ∧
      (¬ ∃ S : SchwartzConcreteNavierStokesSolution ν,
        S.velocity = nilpotentLinearShearVelocityField) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        S.velocity = nilpotentLinearShearVelocityField) ∧
      (∀ {u : NSVelocityField} {t : NSTime} (x : NSSpace),
        (∀ y : NSSpace, u t y = nilpotentLinearShearVelocityField t y) →
          (∀ y : NSSpace, timeVelocityDerivative u t y = 0) →
            spatialVorticity (momentumPressureResidual ν u) t x =
              EuclideanSpace.single nsCoord1 (-1 : ℝ)) ∧
      (∀ t : NSTime,
        ¬ ∃ S : SchwartzConcreteNavierStokesSolution ν,
          (∀ y : NSSpace, S.velocity t y = nilpotentLinearShearVelocityField t y) ∧
            (∀ y : NSSpace, timeVelocityDerivative S.velocity t y = 0)) ∧
      (∀ t : NSTime,
        ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
          (∀ y : NSSpace, S.velocity t y = nilpotentLinearShearVelocityField t y) ∧
            (∀ y : NSSpace, timeVelocityDerivative S.velocity t y = 0)) ∧
      navierNonzeroSchwartzNilpotentShearPressureObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨spatialDivergence_nilpotentLinearShearVelocityField,
      spatialLaplacian_nilpotentLinearShearVelocityField,
      spatialConvection_nilpotentLinearShearVelocityField,
      spatialVorticity_momentumPressureResidual_nilpotentLinearShearVelocityField ν,
      not_exists_smoothPressure_momentumEquation_nilpotentLinearShearVelocityField ν,
      not_exists_schwartzConcreteSolution_velocity_nilpotentLinearShearVelocityField ν,
      not_exists_nonzeroSchwartzConcreteSolution_velocity_nilpotentLinearShearVelocityField ν,
      fun {_u} {_t} x hslice htime =>
        spatialVorticity_momentumPressureResidual_of_frozen_nilpotentLinearShearSlice
          (ν := ν) x hslice htime,
      not_exists_schwartzConcreteSolution_frozen_nilpotentLinearShearSlice ν,
      not_exists_nonzeroSchwartzConcreteSolution_frozen_nilpotentLinearShearSlice ν,
      navierNonzeroSchwartzNilpotentShearPressureObstructionNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzLocalizedStreamSeed_node :
    (∀ φ : NSSchwartzScalar, ∀ x : NSSpace,
      initialSpatialDivergence (streamFunctionVelocity φ : NSInitialVelocity) x = 0) ∧
      (∃ u₀ : NSSchwartzDivergenceFreeInitialVelocity, ∃ x : NSSpace, u₀.1 x ≠ 0) ∧
      navierNonzeroSchwartzLocalizedStreamSeedNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨initialSpatialDivergence_streamFunctionVelocity,
      ⟨nsLocalizedStreamDivergenceFreeInitialVelocity,
        nsLocalizedStreamDivergenceFreeInitialVelocity_nonzero⟩,
      navierNonzeroSchwartzLocalizedStreamSeedNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzAntiProfileCanaryObstruction_node
    (ν : ℝ) :
    LocalizedStreamAntiProfileCanaryObstructionPacket ν ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        S.velocity =
          twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1)
            nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile) ∧
      navierNonzeroSchwartzAntiProfileCanaryObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨localizedStreamAntiProfile_nonzeroProfiles_divergenceFree_closure_but_zeroVelocity ν,
      not_exists_nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity,
      navierNonzeroSchwartzAntiProfileCanaryObstructionNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzAntiProfileAmplitudeBoundary_node :
    (∀ a b : NSTime → ℝ,
      ((∃ t x,
        twoModeSchwartzVelocity a b
            nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile
            t x ≠ 0) ↔
        ∃ t, a t ≠ b t)) ∧
      (∀ (ν : ℝ) (a : NSTime → ℝ),
        ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
          S.velocity =
            twoModeSchwartzVelocity a a
              nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile) ∧
      (∀ {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
        (a b : NSTime → ℝ),
        S.velocity =
            twoModeSchwartzVelocity a b
              nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile →
          ∃ t, a t ≠ b t) ∧
      navierNonzeroSchwartzAntiProfileAmplitudeBoundaryNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨localizedStreamAntiProfile_velocity_nonzero_iff_exists_amplitude_ne,
      fun ν a => by
        simpa [nsLocalizedStreamAntiProfile] using
          not_exists_nonzeroSchwartzConcreteSolution_equalAmplitudeAntiProfileVelocity
            (ν := ν) a nsLocalizedStreamDivergenceFreeInitialVelocity.1,
      fun S a b hS =>
        nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_forces_amplitude_ne
          S a b hS,
      navierNonzeroSchwartzAntiProfileAmplitudeBoundaryNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzStationaryDissipationGate_node
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    (∀ S : SchwartzConcreteNavierStokesSolution ν, ∀ t : NSTime,
      coordinateEnstrophyAt S.velocity t = 0 →
        ∀ x : NSSpace, S.velocity t x = 0) ∧
      (∀ S : SchwartzConcreteNavierStokesSolution ν,
      S.velocity = timeIndependentVelocity u₀ →
        ∀ t : NSTime, coordinateEnergyDissipationRate S.velocity ν t = 0) ∧
      (∀ _hν : 0 < ν,
        ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
          S.velocity = timeIndependentVelocity u₀) ∧
      ((∃ t : NSTime,
        coordinateEnergyDissipationRate (timeIndependentVelocity u₀) ν t ≠ 0) →
        ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
          S.velocity = timeIndependentVelocity u₀) ∧
      navierNonzeroSchwartzStationaryDissipationGateNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S t henst =>
        S.velocity_eq_zero_of_coordinateEnstrophyAt_eq_zero henst,
      fun S hvelocity t =>
        S.coordinateEnergyDissipationRate_eq_zero_of_velocity_timeIndependent hvelocity t,
      fun hν =>
        not_exists_nonzeroSchwartzConcreteSolution_velocity_timeIndependent_of_pos_viscosity
          hν,
      fun hdiss =>
        not_exists_nonzeroSchwartzConcreteSolution_velocity_timeIndependent_of_coordinateEnergyDissipationRate_ne_zero
          hdiss,
      navierNonzeroSchwartzStationaryDissipationGateNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzStrictDissipationKernel_node
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν) :
    (∃ t : NSTime, 0 < coordinateEnergyDissipationRate S.velocity ν t) ∧
      (∃ t : NSTime,
        0 < coordinateEnergyDissipationRate S.velocity ν t ∧
          HasDerivAt (normalizedKineticEnergy S.velocity)
            (-(coordinateEnergyDissipationRate S.velocity ν t)) t ∧
          -(coordinateEnergyDissipationRate S.velocity ν t) < 0) ∧
      navierNonzeroSchwartzStrictDissipationKernelNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨S.exists_coordinateEnergyDissipationRate_pos_of_pos_viscosity hν,
      S.exists_strict_coordinateEnergyDissipationIdentity_of_pos_viscosity hν,
      navierNonzeroSchwartzStrictDissipationKernelNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzNoFlatEnergyObstruction_node
    {ν : ℝ} (hν : 0 < ν) :
    (∀ S : SchwartzConcreteNavierStokesSolution ν,
      (∀ t : NSTime, HasDerivAt (normalizedKineticEnergy S.velocity) 0 t) →
        ∀ t x, S.velocity t x = 0) ∧
      (∀ S : SchwartzConcreteNavierStokesSolution ν,
        (∃ E : ℝ, normalizedKineticEnergy S.velocity = fun _ : NSTime => E) →
          ∀ t x, S.velocity t x = 0) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∀ t : NSTime, HasDerivAt (normalizedKineticEnergy S.velocity) 0 t) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ E : ℝ, normalizedKineticEnergy S.velocity = fun _ : NSTime => E) ∧
      navierNonzeroSchwartzNoFlatEnergyObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S hzero =>
        S.velocity_eq_zero_of_forall_normalizedKineticEnergy_hasDerivAt_zero_of_pos_viscosity
          hν hzero,
      fun S hconst =>
        S.velocity_eq_zero_of_exists_const_normalizedKineticEnergy_of_pos_viscosity
          hν hconst,
      not_exists_nonzeroSchwartzConcreteSolution_forall_normalizedKineticEnergy_hasDerivAt_zero
        hν,
      not_exists_nonzeroSchwartzConcreteSolution_const_normalizedKineticEnergy_of_pos_viscosity
        hν,
      navierNonzeroSchwartzNoFlatEnergyObstructionNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzLocalExtremumEnergyObstruction_node
    {ν : ℝ} (hν : 0 < ν) :
    (∀ S : SchwartzConcreteNavierStokesSolution ν, ∀ t : NSTime,
      IsLocalMin (normalizedKineticEnergy S.velocity) t →
        ∀ x, S.velocity t x = 0) ∧
      (∀ S : SchwartzConcreteNavierStokesSolution ν, ∀ t : NSTime,
        IsLocalMax (normalizedKineticEnergy S.velocity) t →
          ∀ x, S.velocity t x = 0) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∀ t x,
          S.velocity t x ≠ 0 →
            ¬ IsLocalMin (normalizedKineticEnergy S.velocity) t) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∀ t x,
          S.velocity t x ≠ 0 →
            ¬ IsLocalMax (normalizedKineticEnergy S.velocity) t) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ t x,
          S.velocity t x ≠ 0 ∧
            IsLocalMin (normalizedKineticEnergy S.velocity) t) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ t x,
          S.velocity t x ≠ 0 ∧
            IsLocalMax (normalizedKineticEnergy S.velocity) t) ∧
      navierNonzeroSchwartzLocalExtremumEnergyObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S t hmin =>
        S.velocity_eq_zero_of_isLocalMin_normalizedKineticEnergy_of_pos_viscosity
          hν hmin,
      fun S t hmax =>
        S.velocity_eq_zero_of_isLocalMax_normalizedKineticEnergy_of_pos_viscosity
          hν hmax,
      fun S t x hne =>
        S.not_isLocalMin_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
          hν hne,
      fun S t x hne =>
        S.not_isLocalMax_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
          hν hne,
      not_exists_nonzeroSchwartzConcreteSolution_nonzero_localMin_energy_of_pos_viscosity
        hν,
      not_exists_nonzeroSchwartzConcreteSolution_nonzero_localMax_energy_of_pos_viscosity
        hν,
      navierNonzeroSchwartzLocalExtremumEnergyObstructionNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzPointwiseStrictDerivative_node
    {ν : ℝ} (hν : 0 < ν) :
    (∀ S : SchwartzConcreteNavierStokesSolution ν, ∀ t : NSTime,
      (∃ x : NSSpace, S.velocity t x ≠ 0) →
        0 < coordinateEnergyDissipationRate S.velocity ν t) ∧
      (∀ S : SchwartzConcreteNavierStokesSolution ν, ∀ t d : ℝ,
        (∃ x : NSSpace, S.velocity t x ≠ 0) →
          HasDerivAt (normalizedKineticEnergy S.velocity) d t →
            d < 0) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν, ∀ t d : ℝ,
        (∃ x : NSSpace, S.velocity t x ≠ 0) →
          HasDerivAt (normalizedKineticEnergy S.velocity) d t →
            d < 0) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ t x d,
          S.velocity t x ≠ 0 ∧
            HasDerivAt (normalizedKineticEnergy S.velocity) d t ∧
              0 ≤ d) ∧
      navierNonzeroSchwartzPointwiseStrictDerivativeNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S t hne =>
        S.coordinateEnergyDissipationRate_pos_of_exists_velocity_ne_zero
          hν hne,
      fun S t d hne hderiv =>
        S.normalizedKineticEnergy_derivative_lt_zero_of_exists_velocity_ne_zero
          hν hne hderiv,
      fun S t d hne hderiv =>
        S.normalizedKineticEnergy_derivative_lt_zero_of_exists_velocity_ne_zero
          hν hne hderiv,
      not_exists_nonzeroSchwartzConcreteSolution_nonzero_nonneg_energy_derivative_of_pos_viscosity
        hν,
      navierNonzeroSchwartzPointwiseStrictDerivativeNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzLocalPlateauObstruction_node
    {ν : ℝ} (hν : 0 < ν) :
    (∀ S : SchwartzConcreteNavierStokesSolution ν, ∀ t : NSTime,
      (∀ᶠ s in nhds t,
        normalizedKineticEnergy S.velocity s =
          normalizedKineticEnergy S.velocity t) →
        ∀ x, S.velocity t x = 0) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∀ t x,
          S.velocity t x ≠ 0 →
            ¬ ∀ᶠ s in nhds t,
              normalizedKineticEnergy S.velocity s =
                normalizedKineticEnergy S.velocity t) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ t x,
          S.velocity t x ≠ 0 ∧
            (∀ᶠ s in nhds t,
              normalizedKineticEnergy S.velocity s =
                normalizedKineticEnergy S.velocity t)) ∧
      navierNonzeroSchwartzLocalPlateauObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S t hplateau =>
        S.velocity_eq_zero_of_eventually_eq_normalizedKineticEnergy_of_pos_viscosity
          hν hplateau,
      fun S t x hne =>
        S.not_eventually_eq_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
          hν hne,
      not_exists_nonzeroSchwartzConcreteSolution_nonzero_energy_plateau_of_pos_viscosity
        hν,
      navierNonzeroSchwartzLocalPlateauObstructionNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzImmediateRightDrop_node
    {ν : ℝ} (hν : 0 < ν) :
    (∀ S : SchwartzConcreteNavierStokesSolution ν, ∀ t : NSTime,
      (∃ x : NSSpace, S.velocity t x ≠ 0) →
        ∀ᶠ s in 𝓝[>] t,
          normalizedKineticEnergy S.velocity s <
            normalizedKineticEnergy S.velocity t) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∀ t x,
          S.velocity t x ≠ 0 →
            ¬ ∀ᶠ s in 𝓝[>] t,
              normalizedKineticEnergy S.velocity t ≤
                normalizedKineticEnergy S.velocity s) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ t x,
          S.velocity t x ≠ 0 ∧
            (∀ᶠ s in 𝓝[>] t,
              normalizedKineticEnergy S.velocity t ≤
                normalizedKineticEnergy S.velocity s)) ∧
      navierNonzeroSchwartzImmediateRightDropNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S t hne =>
        S.normalizedKineticEnergy_eventually_right_lt_of_exists_velocity_ne_zero
          hν hne,
      fun S t x hne =>
        S.not_eventually_right_normalizedKineticEnergy_nondecreasing_at_nonzero_of_pos_viscosity
          hν hne,
      not_exists_nonzeroSchwartzConcreteSolution_nonzero_eventually_right_energy_nondecreasing_of_pos_viscosity
        hν,
         navierNonzeroSchwartzImmediateRightDropNode_checked,
         navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzRightDropSample_node
    {ν : ℝ} (hν : 0 < ν) :
    (∀ S : SchwartzConcreteNavierStokesSolution ν, ∀ t ε : NSTime,
      (∃ x : NSSpace, S.velocity t x ≠ 0) →
        0 < ε →
          ∃ s, t < s ∧ s < t + ε ∧
            normalizedKineticEnergy S.velocity s <
              normalizedKineticEnergy S.velocity t) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∀ t ε x,
          S.velocity t x ≠ 0 →
            0 < ε →
              ∃ s, t < s ∧ s < t + ε ∧
                normalizedKineticEnergy S.velocity s <
                  normalizedKineticEnergy S.velocity t) ∧
      navierNonzeroSchwartzRightDropSampleNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S t ε hne hε =>
        S.exists_normalizedKineticEnergy_right_drop_sample_of_exists_velocity_ne_zero
          hν hne hε,
      fun S t ε x hne hε =>
        S.exists_normalizedKineticEnergy_right_drop_sample_at_nonzero_of_pos_viscosity
          hν hne hε,
      navierNonzeroSchwartzRightDropSampleNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzStrictFutureDrop_node
    {ν : ℝ} (hν : 0 < ν) :
    (∀ S : SchwartzConcreteNavierStokesSolution ν, ∀ t₀ t₁ : NSTime,
      (∃ x : NSSpace, S.velocity t₀ x ≠ 0) →
        t₀ < t₁ →
          normalizedKineticEnergy S.velocity t₁ <
            normalizedKineticEnergy S.velocity t₀) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∀ t₀ t₁ x,
          S.velocity t₀ x ≠ 0 →
            t₀ < t₁ →
              normalizedKineticEnergy S.velocity t₁ <
                normalizedKineticEnergy S.velocity t₀) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ t₀ t₁ x,
          S.velocity t₀ x ≠ 0 ∧
            t₀ < t₁ ∧
              normalizedKineticEnergy S.velocity t₀ ≤
                normalizedKineticEnergy S.velocity t₁) ∧
      navierNonzeroSchwartzStrictFutureDropNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S t₀ t₁ hne ht =>
        S.normalizedKineticEnergy_strict_lt_of_exists_velocity_ne_zero_left
          hν hne ht,
      fun S t₀ t₁ x hne ht =>
        S.normalizedKineticEnergy_strict_lt_after_nonzero_of_pos_viscosity
          hν hne ht,
      not_exists_nonzeroSchwartzConcreteSolution_nonzero_later_energy_nondecreasing_of_pos_viscosity
        hν,
      navierNonzeroSchwartzStrictFutureDropNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzNoEnergyRecurrence_node
    {ν : ℝ} (hν : 0 < ν) :
    (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∀ t P x,
        S.velocity t x ≠ 0 →
          0 < P →
            normalizedKineticEnergy S.velocity (t + P) ≠
              normalizedKineticEnergy S.velocity t) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∀ P,
          0 < P →
            ¬ ∀ t : NSTime,
              normalizedKineticEnergy S.velocity (t + P) =
                normalizedKineticEnergy S.velocity t) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∀ P,
          0 < P →
            ¬ ∀ t : NSTime, ∀ x : NSSpace,
              S.velocity (t + P) x = S.velocity t x) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ P : NSTime,
          0 < P ∧
            ∀ t : NSTime,
              normalizedKineticEnergy S.velocity (t + P) =
                normalizedKineticEnergy S.velocity t) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ P : NSTime,
          0 < P ∧
            ∀ t : NSTime, ∀ x : NSSpace,
              S.velocity (t + P) x = S.velocity t x) ∧
      navierNonzeroSchwartzNoEnergyRecurrenceNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S t P x hne hP =>
        S.normalizedKineticEnergy_ne_periodic_endpoint_at_nonzero_of_pos_viscosity
          hν hne hP,
      fun S P hP =>
        S.not_forall_normalizedKineticEnergy_periodic_of_pos_viscosity
          hν hP,
      fun S P hP =>
        S.not_forall_velocity_periodic_of_pos_viscosity hν hP,
      not_exists_nonzeroSchwartzConcreteSolution_energy_periodic_of_pos_viscosity
        hν,
      not_exists_nonzeroSchwartzConcreteSolution_velocity_periodic_of_pos_viscosity
        hν,
      navierNonzeroSchwartzNoEnergyRecurrenceNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierSchwartzPressureResidualCurlGate_node
    {ν : ℝ} (u : NSVelocityField) :
    (∀ S : SchwartzConcreteNavierStokesSolution ν,
      ∀ t x, spatialVorticity (momentumPressureResidual ν S.velocity) t x = 0) ∧
      ((∃ t : NSTime, ∃ x : NSSpace,
          spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) →
        ¬ ∃ S : SchwartzConcreteNavierStokesSolution ν, S.velocity = u) ∧
      ((∃ t : NSTime, ∃ x : NSSpace,
          spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) →
        ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν, S.velocity = u) ∧
      navierSchwartzPressureResidualCurlGateNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S => S.momentumPressureResidual_spatialVorticity_zero,
      fun hcurl =>
        not_exists_schwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
          hcurl,
      fun hcurl =>
        not_exists_nonzeroSchwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
          hcurl,
      navierSchwartzPressureResidualCurlGateNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzFiniteModeResidualCurlBoundary_node
    {ν : ℝ} (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∀ S : SchwartzConcreteNavierStokesSolution ν,
      SchwartzConcreteSolutionKernel ν S.velocity S.pressure) ∧
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∃ t x, S.velocity t x ≠ 0) ∧
          SchwartzConcreteSolutionKernel ν S.velocity S.pressure) ∧
      (∀ S : SchwartzConcreteNavierStokesSolution ν,
        S.velocity =
          twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g →
          ∀ t x,
            spatialVorticity
              (fun s y =>
                (ν : ℝ) •
                  (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) s y +
                    spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) s y))
              t x =
              0) ∧
      ((∃ t x,
        spatialVorticity
          (fun s y =>
            (ν : ℝ) •
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) s y +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) s y)) t x ≠
          0) →
        ¬ ∃ S : SchwartzConcreteNavierStokesSolution ν,
          S.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) ∧
      ((∃ t x,
        spatialVorticity
          (fun s y =>
            (ν : ℝ) •
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) s y +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) s y)) t x ≠
          0) →
        ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
          S.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) ∧
      navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨fun S => S.concreteSolutionKernel,
      fun S => S.nonzero_and_concreteSolutionKernel,
      fun S hvelocity =>
        oneOneTwoModeSchwartzVelocity_lapSum_residualVorticity_zero_of_schwartzConcreteSolution
          S f g hvelocity hclosure,
      fun hcurl =>
        not_exists_schwartzConcreteSolution_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero
          f g hclosure hcurl,
      fun hcurl =>
        not_exists_nonzeroSchwartzConcreteSolution_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero
          f g hclosure hcurl,
      navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzStationaryInviscidConstructor_node
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (q : 𝓢(NSSpace, ℝ))
    (hnonzero : ∃ x : NSSpace, u₀.1 x ≠ 0)
    (hstationary : ∀ t x,
      spatialConvection (timeIndependentVelocity (u₀.1 : NSInitialVelocity)) t x +
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x =
        0) :
    (∃ S : NonzeroSchwartzConcreteNavierStokesSolution 0,
      S.velocity = timeIndependentVelocity (u₀.1 : NSInitialVelocity) ∧
        S.pressure = (fun _ : NSTime => fun y : NSSpace => q y) ∧
        SchwartzConcreteSolutionKernel 0 S.velocity S.pressure) ∧
      (∃ t x, timeIndependentVelocity (u₀.1 : NSInitialVelocity) t x ≠ 0) ∧
      navierNonzeroSchwartzStationaryInviscidConstructorNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  let S :=
    stationaryInviscidSchwartzPressureSlice_nonzeroSchwartzConcreteSolution
      u₀ q hnonzero hstationary
  exact
    ⟨⟨S, rfl, rfl, S.concreteSolutionKernel⟩,
      (stationaryInviscidSchwartzPressureSlice_nonzero_concreteSolutionKernel
        u₀ q hnonzero hstationary).1,
      navierNonzeroSchwartzStationaryInviscidConstructorNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzStokesKernel_node
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      (∃ t : NSTime,
        0 < coordinateEnergyDissipationRate S.velocity ν t ∧
          HasDerivAt (normalizedKineticEnergy S.velocity)
            (-(coordinateEnergyDissipationRate S.velocity ν t)) t ∧
          -(coordinateEnergyDissipationRate S.velocity ν t) < 0) ∧
      (∀ {P : NSTime}, 0 < P →
        ¬ ∀ t : NSTime, ∀ x : NSSpace,
          S.velocity (t + P) x = S.velocity t x) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
          ∃ P : NSTime,
            0 < P ∧
              ∀ t : NSTime, ∀ x : NSSpace,
                W.velocity (t + P) x = W.velocity t x) ∧
      navierNonzeroSchwartzStokesKernelNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨S.nonzeroStokesFlowKernel hconv hpressure,
      S.exists_strict_coordinateEnergyDissipationIdentity_of_pos_viscosity hν,
      fun {_P} hP =>
        S.stokesFlow_not_forall_velocity_periodic_of_pos_viscosity
          hν hconv hpressure hP,
      not_exists_nonzeroSchwartzStokesFlow_velocity_periodic_of_pos_viscosity hν,
      navierNonzeroSchwartzStokesKernelNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzStokesRankOneObstruction_node
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {v : NSSpace} (hv : v ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      (∃ t : NSTime,
        0 < coordinateEnergyDissipationRate S.velocity ν t ∧
          HasDerivAt (normalizedKineticEnergy S.velocity)
            (-(coordinateEnergyDissipationRate S.velocity ν t)) t ∧
          -(coordinateEnergyDissipationRate S.velocity ν t) < 0) ∧
      (∃ t : NSTime,
        ∀ φ : NSSchwartzScalar,
          S.velocitySlice t ≠ rankOneSchwartzVelocity φ v) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
          ∀ t : NSTime,
            ∃ φ : NSSchwartzScalar,
              W.velocitySlice t = rankOneSchwartzVelocity φ v) ∧
      navierNonzeroSchwartzStokesRankOneObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  rcases
      S.stokesFlow_strictDissipation_and_non_rankOne_slice_packet
        hν hconv hpressure hv with
    ⟨hkernel, hstrict, hnonrank⟩
  exact
    ⟨hkernel,
      hstrict,
      hnonrank,
      not_exists_nonzeroSchwartzStokesFlow_forall_rankOne_fixed_direction hv,
      navierNonzeroSchwartzStokesRankOneObstructionNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzPastDissipation_node
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν) :
    (∃ t₁ x₁,
      S.velocity t₁ x₁ ≠ 0 ∧
        ∀ t₀ : NSTime, t₀ ≤ t₁ →
          (∃ x₀ : NSSpace, S.velocity t₀ x₀ ≠ 0) ∧
            0 < coordinateEnergyDissipationRate S.velocity ν t₀ ∧
            HasDerivAt (normalizedKineticEnergy S.velocity)
              (-(coordinateEnergyDissipationRate S.velocity ν t₀)) t₀ ∧
            -(coordinateEnergyDissipationRate S.velocity ν t₀) < 0) ∧
      (∃ t₁ x₁,
        S.velocity t₁ x₁ ≠ 0 ∧
          ∀ s t : NSTime, s < t → t ≤ t₁ →
            normalizedKineticEnergy S.velocity t <
              normalizedKineticEnergy S.velocity s) ∧
      navierNonzeroSchwartzPastDissipationNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨S.exists_nonzero_witness_with_strict_dissipation_at_all_prior_times hν,
      S.exists_nonzero_witness_with_strict_past_energy_drop hν,
      navierNonzeroSchwartzPastDissipationNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzEndpointSupport_node
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {s t T : NSTime} (hst : s < t) (htT : t ≤ T)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    SchwartzNonzeroTimeSupportKernel ν S.velocity S.pressure ∧
      (∃ xs : NSSpace, S.velocity s xs ≠ 0) ∧
      (∃ xt : NSSpace, S.velocity t xt ≠ 0) ∧
      normalizedKineticEnergy S.velocity t <
        normalizedKineticEnergy S.velocity s ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ s t T : NSTime,
          s < t ∧ t ≤ T ∧
            (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
              normalizedKineticEnergy W.velocity s ≤
                normalizedKineticEnergy W.velocity t) ∧
      navierNonzeroSchwartzEndpointSupportNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  have hnes :
      ∃ xs : NSSpace, S.velocity s xs ≠ 0 :=
    S.exists_velocity_ne_zero_before_endpoint_of_nonneg_viscosity
      hν.le (le_trans (le_of_lt hst) htT) hneT
  have hnet :
      ∃ xt : NSSpace, S.velocity t xt ≠ 0 :=
    S.exists_velocity_ne_zero_before_endpoint_of_nonneg_viscosity
      hν.le htT hneT
  exact
    ⟨S.nonzeroTimeSupportKernel,
      hnes,
      hnet,
      S.normalizedKineticEnergy_strict_lt_before_nonzero_endpoint_of_pos_viscosity
        hν hst htT hneT,
      not_exists_nonzeroSchwartzConcreteSolution_energy_nondecrease_before_nonzero_endpoint_of_pos_viscosity
        hν,
      navierNonzeroSchwartzEndpointSupportNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzNoUniformPastDissipation_node
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {κ T : NSTime} (hκ : 0 < κ)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    (¬ ∀ t : NSTime, t ≤ T →
      κ ≤ coordinateEnergyDissipationRate S.velocity ν t) ∧
      (¬ ∀ t : NSTime, t ≤ T →
        κ * normalizedKineticEnergy S.velocity t ≤
          coordinateEnergyDissipationRate S.velocity ν t) ∧
      (∃ t : NSTime,
        t ≤ T ∧
          (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
            0 < coordinateEnergyDissipationRate S.velocity ν t ∧
              coordinateEnergyDissipationRate S.velocity ν t < κ) ∧
      NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      (∃ T xT,
        S.velocity T xT ≠ 0 ∧
          ∀ κ : NSTime, 0 < κ →
            ∃ t : NSTime,
              t ≤ T ∧
                (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                  0 < coordinateEnergyDissipationRate S.velocity ν t ∧
                    coordinateEnergyDissipationRate S.velocity ν t < κ) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ T : NSTime,
          ∀ t : NSTime, t ≤ T →
            κ ≤ coordinateEnergyDissipationRate W.velocity ν t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ T : NSTime,
          (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
            ∀ t : NSTime, t ≤ T →
              κ * normalizedKineticEnergy W.velocity t ≤
                coordinateEnergyDissipationRate W.velocity ν t) ∧
      navierNonzeroSchwartzNoUniformPastDissipationNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  rcases S.stokesFlow_noUniformPastDissipation_packet hν hconv hpressure with
    ⟨hstokes, hsmallPacket⟩
  exact
    ⟨S.toSchwartzConcreteNavierStokesSolution
        |>.not_forall_past_coordinateEnergyDissipationRate_ge hκ,
      S.toSchwartzConcreteNavierStokesSolution
        |>.not_forall_past_coordinateEnergyDissipationRate_ge_mul_normalizedKineticEnergy
          hν.le hκ hneT,
      S.toSchwartzConcreteNavierStokesSolution
        |>.exists_past_nonzero_with_small_positive_coordinateEnergyDissipationRate
          hν hneT hκ,
      hstokes,
      hsmallPacket,
      not_exists_nonzeroSchwartzConcreteSolution_uniform_past_dissipation_gap hκ,
      not_exists_nonzeroSchwartzConcreteSolution_past_spectral_floor hν.le hκ,
      navierNonzeroSchwartzNoUniformPastDissipationNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzZeroRestart_node
    {ν : ℝ} (hν : 0 ≤ ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁)
    (hzero : ∀ x, S.velocity t₀ x = 0) :
    SchwartzZeroRestartKernel ν S.velocity S.pressure ∧
      NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      (∀ x, S.velocity t₁ x = 0) ∧
      (∀ x, ¬ S.velocity t₁ x ≠ 0) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ s₀ s₁ : NSTime,
          s₀ ≤ s₁ ∧
            (∀ x, W.velocity s₀ x = 0) ∧
            ∃ x, W.velocity s₁ x ≠ 0) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
          ∃ s₀ s₁ : NSTime,
            s₀ ≤ s₁ ∧
              (∀ x, W.velocity s₀ x = 0) ∧
              ∃ x, W.velocity s₁ x ≠ 0) ∧
      navierNonzeroSchwartzZeroRestartNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨S.zeroRestartKernel,
      S.nonzeroStokesFlowKernel hconv hpressure,
      SchwartzConcreteNavierStokesSolution.velocity_eq_zero_at_later_of_velocity_eq_zero_at_of_nonneg_viscosity
        S.toSchwartzConcreteNavierStokesSolution hν ht hzero,
      fun x =>
        S.not_velocity_ne_zero_at_or_after_zero_slice_of_nonneg_viscosity
          hν ht hzero x,
      not_exists_nonzeroSchwartzConcreteSolution_zero_slice_before_nonzero_of_nonneg_viscosity hν,
      not_exists_nonzeroSchwartzStokesFlow_zero_slice_before_nonzero_of_nonneg_viscosity hν,
      navierNonzeroSchwartzZeroRestartNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem navierCriticalNormCanariesNode_uncleared :
    navierCriticalNormCanariesNode.status = .scalingUncleared := by
  rfl

theorem navierAveragedEquationFrontierNode_uncleared :
    navierAveragedEquationFrontierNode.status = .scalingUncleared := by
  rfl

theorem navierAveragedEquationInterfaceCanariesNode_uncleared :
    navierAveragedEquationInterfaceCanariesNode.status = .scalingUncleared := by
  rfl

theorem navierAveragedMomentumObstructionNode_uncleared :
    navierAveragedMomentumObstructionNode.status = .scalingUncleared := by
  rfl

theorem navierAveragedMomentumCanariesNode_uncleared :
    navierAveragedMomentumCanariesNode.status = .scalingUncleared := by
  rfl

theorem navierReynoldsStressClosureObstructionNode_uncleared :
    navierReynoldsStressClosureObstructionNode.status = .scalingUncleared := by
  rfl

theorem navierReynoldsStressClosureCanariesNode_uncleared :
    navierReynoldsStressClosureCanariesNode.status = .scalingUncleared := by
  rfl

theorem navierEnergyInequalityCompatibilityObstructionNode_uncleared :
    navierEnergyInequalityCompatibilityObstructionNode.status = .scalingUncleared := by
  rfl

theorem navierEnergyInequalityTransportCanariesNode_uncleared :
    navierEnergyInequalityTransportCanariesNode.status = .scalingUncleared := by
  rfl

theorem navierCriticalScalingCompatibilityObstructionNode_uncleared :
    navierCriticalScalingCompatibilityObstructionNode.status = .scalingUncleared := by
  rfl

theorem navierCriticalScalingTransportCanariesNode_uncleared :
    navierCriticalScalingTransportCanariesNode.status = .scalingUncleared := by
  rfl

theorem navierAveragedEquationAllObstructionsNode_uncleared :
    navierAveragedEquationAllObstructionsNode.status = .scalingUncleared := by
  rfl

theorem navierRegularityPromotionGateNode_uncleared :
    navierRegularityPromotionGateNode.status = .scalingUncleared := by
  rfl

theorem navierRegularityPromotionLayerCanariesNode_uncleared :
    navierRegularityPromotionLayerCanariesNode.status = .scalingUncleared := by
  rfl

theorem currentNavierCriticalNormCanaries_node :
    (navierCriticalL3FullInterfaceCanaryAudit.clearsCriticalNormGate =
        true ∧
      navierSubcriticalL4FullInterfaceCanaryAudit.clearsCriticalNormGate =
        true ∧
      navierFiniteEnergyL2OnlyCanaryAudit.clearsCriticalNormGate =
        false ∧
      navierCriticalL3MissingWitnessCanaryAudit.diagnosticClearsCriticalPromotion =
        true ∧
      navierCriticalL3MissingWitnessCanaryAudit.clearsCriticalNormGate =
        false ∧
      navierSupercriticalL2WithInterfacesCanaryAudit.criticalWorldInterfacesClear =
        true ∧
      navierSupercriticalL2WithInterfacesCanaryAudit.clearsCriticalNormGate =
        false) ∧
      navierCurrentEnergyBKMRouteCriticalNormCanaryAudit.clearsCriticalNormGate =
        false ∧
      navierCriticalNormCanariesNode.status = .scalingUncleared := by
  exact
    ⟨navierCriticalNormCanaries_guardrails,
      navierCurrentEnergyBKMRouteCriticalNormCanary_obstruction.2.2.2.2,
      navierCriticalNormCanariesNode_uncleared⟩

theorem currentNavierAveragedEquationInterfaceCanaries_node :
    (navierAveragedEquationFullInterfaceCanaryAudit.clearsAveragedEquationGate =
        true ∧
      navierAveragedEquationObligationsOnlyCanaryAudit.representedAllRequiredObligations =
        true ∧
      navierAveragedEquationObligationsOnlyCanaryAudit.clearsAveragedEquationGate =
        false ∧
      navierAveragedEquationInterfacesOnlyCanaryAudit.challengeWorldInterfacesClear =
        true ∧
      navierAveragedEquationInterfacesOnlyCanaryAudit.clearsAveragedEquationGate =
        false ∧
      navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.missingChallengeWorldInterfaces =
        [ .averagedEquationWorldFamily ] ∧
      navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.clearsAveragedEquationGate =
        false ∧
      navierAveragedMomentumOnlyCanaryAudit.clearsAveragedEquationGate =
        false) ∧
      navierCurrentEnergyBKMRouteAveragedEquationCanaryAudit.clearsAveragedEquationGate =
        false ∧
      navierAveragedEquationInterfaceCanariesNode.status = .scalingUncleared := by
  exact
    ⟨navierAveragedEquationCanaries_guardrails,
      navierCurrentEnergyBKMRouteAveragedEquationCanary_obstruction.2.2.2.2,
      navierAveragedEquationInterfaceCanariesNode_uncleared⟩

theorem currentNavierEnergyBKMRouteReynoldsStressClosureObstruction_node :
    NavierAveragedEquationObligation.reynoldsStressClosure ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations ∧
      ¬ NavierAveragedEquationObligation.reynoldsStressClosure ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented ∧
      NavierAveragedEquationObligation.reynoldsStressClosure.requiredWorldInterface =
        .reynoldsStressClosureWitness ∧
      NavierScalingWorldInterface.reynoldsStressClosureWitness ∈
        currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility ∧
      ¬ NavierScalingWorldInterface.reynoldsStressClosureWitness ∈
        currentNavierEnergyBKMRouteWorldInterfaces.supplied := by
  exact currentNavierEnergyBKMRoute_reynoldsStressClosure_obstruction

theorem currentNavierAveragedMomentumCanaries_node :
    (navierAveragedMomentumExactResidualCanaryAudit.clearsAveragedMomentumGate =
        true ∧
      navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.suppliesAveragedMomentumWitness =
        true ∧
      navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.componentwiseResidualMatches =
        false ∧
      navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.clearsAveragedMomentumGate =
        false ∧
      navierAveragedMomentumScalarOnlyCanaryAudit.scalarBalanceMatches =
        true ∧
      navierAveragedMomentumScalarOnlyCanaryAudit.clearsAveragedMomentumGate =
        false ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.componentwiseResidualMatches =
        true ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.suppliesAveragedEquationWorldFamily =
        false ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.clearsAveragedMomentumGate =
        false ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.pointwiseMomentumEquationChecked =
        true ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.suppliesAveragedMomentumWitness =
        false ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.clearsAveragedMomentumGate =
        false) ∧
      navierCurrentEnergyBKMRouteAveragedMomentumCanaryAudit.clearsAveragedMomentumGate =
        false ∧
      navierAveragedMomentumCanariesNode.status = .scalingUncleared := by
  exact
    ⟨⟨navierAveragedMomentumCanaries_guardrails.1,
        navierAveragedMomentumCanaries_guardrails.2.1,
        navierAveragedMomentumCanaries_guardrails.2.2.1,
        navierAveragedMomentumCanaries_guardrails.2.2.2.1,
        navierAveragedMomentumCanaries_guardrails.2.2.2.2.1,
        navierAveragedMomentumCanaries_guardrails.2.2.2.2.2.2.1,
        navierAveragedMomentumCanaries_guardrails.2.2.2.2.2.2.2.1,
        navierAveragedMomentumCanaries_guardrails.2.2.2.2.2.2.2.2.1,
        navierAveragedMomentumCanaries_guardrails.2.2.2.2.2.2.2.2.2.1,
        navierAveragedMomentumCanaries_guardrails.2.2.2.2.2.2.2.2.2.2.1,
        navierAveragedMomentumCanaries_guardrails.2.2.2.2.2.2.2.2.2.2.2.1,
        navierAveragedMomentumCanaries_guardrails.2.2.2.2.2.2.2.2.2.2.2.2⟩,
      navierCurrentEnergyBKMRouteAveragedMomentumCanary_obstruction.2.2.2.2.1,
      navierAveragedMomentumCanariesNode_uncleared⟩

theorem currentNavierReynoldsStressClosureCanaries_node :
    (navierReynoldsStressExactResidualCanaryAudit.clearsClosureGate =
        true ∧
      navierReynoldsStressWitnessMismatchedResidualCanaryAudit.suppliesReynoldsStressClosureWitness =
        true ∧
      navierReynoldsStressWitnessMismatchedResidualCanaryAudit.residualMatches =
        false ∧
      navierReynoldsStressWitnessMismatchedResidualCanaryAudit.clearsClosureGate =
        false ∧
      navierReynoldsStressTraceScalarOnlyCanaryAudit.traceScalarMatches =
        true ∧
      navierReynoldsStressTraceScalarOnlyCanaryAudit.clearsClosureGate =
        false ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.residualMatches =
        true ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.suppliesReynoldsStressClosureWitness =
        false ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.clearsClosureGate =
        false ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.averagedVelocityZero =
        true ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.pointwiseMomentumResidualZero =
        true ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.residualMatches =
        false ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.clearsClosureGate =
        false) ∧
      navierCurrentEnergyBKMRouteReynoldsStressClosureCanaryAudit.clearsClosureGate =
        false ∧
      navierReynoldsStressClosureCanariesNode.status = .scalingUncleared := by
  exact
    ⟨navierReynoldsStressClosureCanaries_guardrails,
      navierCurrentEnergyBKMRouteReynoldsStressClosureCanary_obstruction.2.2.1,
      navierReynoldsStressClosureCanariesNode_uncleared⟩

theorem currentNavierEnergyBKMRouteEnergyInequalityCompatibilityObstruction_node :
    NavierAveragedEquationObligation.energyInequalityCompatibility ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations ∧
      ¬ NavierAveragedEquationObligation.energyInequalityCompatibility ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented ∧
      NavierAveragedEquationObligation.energyInequalityCompatibility.requiredWorldInterface =
        .energyInequalityTransport ∧
      NavierScalingWorldInterface.energyInequalityTransport ∈
        currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility ∧
      ¬ NavierScalingWorldInterface.energyInequalityTransport ∈
        currentNavierEnergyBKMRouteWorldInterfaces.supplied := by
  exact currentNavierEnergyBKMRoute_energyInequalityCompatibility_obstruction

theorem currentNavierEnergyInequalityTransportCanaries_node :
    (navierEnergyInequalityExactBudgetCanaryAudit.clearsEnergyInequalityTransportGate =
        true ∧
      navierEnergyInequalityAllowanceBudgetCanaryAudit.endpointEnergyNonincreasing =
        false ∧
      navierEnergyInequalityAllowanceBudgetCanaryAudit.clearsEnergyInequalityTransportGate =
        true ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.suppliesEnergyInequalityTransport =
        true ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.clearsEnergyInequalityTransportGate =
        false ∧
      navierEnergyInequalityEndpointOnlyCanaryAudit.endpointEnergyNonincreasing =
        true ∧
      navierEnergyInequalityEndpointOnlyCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityEndpointOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.energyBudgetHolds =
        true ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.suppliesEnergyInequalityTransport =
        false ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.localEnergyInequalityChecked =
        true ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false) ∧
      navierCurrentEnergyBKMRouteEnergyInequalityTransportCanaryAudit.clearsEnergyInequalityTransportGate =
        false ∧
      navierEnergyInequalityTransportCanariesNode.status = .scalingUncleared := by
  exact
    ⟨navierEnergyInequalityTransportCanaries_guardrails,
      navierCurrentEnergyBKMRouteEnergyInequalityTransportCanary_obstruction.2.2.2.1,
      navierEnergyInequalityTransportCanariesNode_uncleared⟩

theorem currentNavierEnergyBKMRouteCriticalScalingCompatibilityObstruction_node :
    NavierAveragedEquationObligation.criticalScalingCompatibility ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations ∧
      ¬ NavierAveragedEquationObligation.criticalScalingCompatibility ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented ∧
      NavierAveragedEquationObligation.criticalScalingCompatibility.requiredWorldInterface =
        .criticalScalingTransport ∧
      NavierScalingWorldInterface.criticalScalingTransport ∈
        currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility ∧
      ¬ NavierScalingWorldInterface.criticalScalingTransport ∈
        currentNavierEnergyBKMRouteWorldInterfaces.supplied := by
  exact currentNavierEnergyBKMRoute_criticalScalingCompatibility_obstruction

theorem currentNavierCriticalScalingTransportCanaries_node :
    (navierCriticalScalingTransportL3PreservedCanaryAudit.clearsCriticalScalingTransportGate =
        true ∧
      navierCriticalScalingTransportL4PreservedCanaryAudit.clearsCriticalScalingTransportGate =
        true ∧
      navierCriticalScalingTransportFiniteL2LabelCanaryAudit.suppliesCriticalScalingTransport =
        true ∧
      navierCriticalScalingTransportFiniteL2LabelCanaryAudit.sourceRegime =
        .supercritical ∧
      navierCriticalScalingTransportFiniteL2LabelCanaryAudit.clearsCriticalScalingTransportGate =
        false ∧
      navierCriticalScalingTransportL3MissingWitnessCanaryAudit.suppliesCriticalScalingTransport =
        false ∧
      navierCriticalScalingTransportL3MissingWitnessCanaryAudit.clearsCriticalScalingTransportGate =
        false ∧
      navierCriticalScalingTransportEnergyOnlyCanaryAudit.suppliesEnergyInequalityTransport =
        true ∧
      navierCriticalScalingTransportEnergyOnlyCanaryAudit.clearsCriticalScalingTransportGate =
        false ∧
      navierCriticalScalingTransportCriticalToSupercriticalCanaryAudit.transportedRegime =
        .supercritical ∧
      navierCriticalScalingTransportCriticalToSupercriticalCanaryAudit.clearsCriticalScalingTransportGate =
        false ∧
      navierCriticalScalingTransportL4ToL3NotPreservedCanaryAudit.transportPreservesScalingNumerator =
        false ∧
      navierCriticalScalingTransportL4ToL3NotPreservedCanaryAudit.clearsCriticalScalingTransportGate =
        false) ∧
      navierCurrentEnergyBKMRouteCriticalScalingTransportCanaryAudit.clearsCriticalScalingTransportGate =
        false ∧
      navierCriticalScalingTransportCanariesNode.status = .scalingUncleared := by
  exact
    ⟨navierCriticalScalingTransportCanaries_guardrails,
      rfl,
      navierCriticalScalingTransportCanariesNode_uncleared⟩

theorem currentNavierEnergyBKMRouteAllAveragedEquationObstructions_node :
    currentNavierEnergyBKMRouteAllAveragedEquationObstructionPacket := by
  exact currentNavierEnergyBKMRoute_allAveragedEquationObstructions

theorem currentNavierRegularityPromotionLayerCanaries_node :
    (navierRegularityPromotionAllLayersCanaryAudit.clearsRegularityPromotionGate =
        true ∧
      navierRegularityPromotionScalingOnlyCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionWorldsOnlyCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionAveragedEquationOnlyCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionScalingWorldsNoAveragedEquationCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionScalingAveragedEquationNoWorldsCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionWorldsAveragedEquationNoScalingCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierCurrentEnergyBKMRouteRegularityPromotionCanaryAudit.clearsRegularityPromotionGate =
        false) ∧
      navierRegularityPromotionLayerCanariesNode.status = .scalingUncleared := by
  exact
    ⟨navierRegularityPromotionLayerOmissions_guardrails,
      navierRegularityPromotionLayerCanariesNode_uncleared⟩

end NavierStokes
end FluidDynamics
end Mettapedia
