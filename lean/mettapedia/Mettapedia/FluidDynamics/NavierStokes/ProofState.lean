import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyBKMBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityStretching
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityEquation
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityGrowth
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMResidualCurlExpansion
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMLogSobolevControl
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMAnalyticReduction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMHighNormContinuation
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMResidualCurlDifferentialIdentities
import Mettapedia.FluidDynamics.NavierStokes.FeffermanCompatibilityFrontier
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesDEGroundedCanary
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionKernel
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzStokesKernel
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzStokesRankOneObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzPastDissipation
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzNonzeroSupport
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzNoUniformDissipation
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzStokesFiniteProfileObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzPressureClosureCertificate
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzZeroRestartObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzAntiProfileCanaryObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLocalizedStreamFunction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzRankOneShearObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzSymmetricShearObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesNilpotentShearObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLocalizedNilpotentStreamObstruction
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
  sourceFiles := 531
  sourceLines := 121239
  internalImportEdges := 1352
  regressionFiles := 153
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

/-- The BKM route now has the local pointwise control of the vorticity
stretching term. -/
def navierBKMVorticityStretchingNode : NavierProofNode where
  id := "navier.bkm.vorticity-stretching"
  status := .checked
  truthValue := ⟨83, 88⟩
  evidence := "vorticityStretchingTerm defines the concrete pointwise term (omega . grad)u as spatialFDeriv u applied to spatialVorticity u. norm_vorticityStretchingTerm_le proves ||(omega . grad)u|| <= ||grad u||op * ||omega||, abs_vorticityStretchingPower_le proves the pointwise enstrophy-production bound |<omega,(omega . grad)u>| <= ||grad u||op * ||omega|| * ||omega||, and the envelope/uniform corollaries lift these bounds to slabwise gradient and vorticity controls. Validation lab ns-bkm-vorticity-stretching-lab-20260629.json passed on Taylor-Green and random solenoidal periodic fields. PLN STV <s=.83,c=.88>, ITV [.7304,.8504], PROGRESS 43%."
  blocker := "This genuinely handles the local stretching estimate, but it is not the full BKM continuation criterion. Remaining analytic dependencies are the exact vorticity equation on the concrete smooth-solution surface, log-Sobolev/Biot-Savart control of ||grad u||_infty by the time-integrable vorticity envelope plus high norm, the H^s/enstrophy differential inequality, and the continuation/Gronwall closure."

/-- Finite-time BKM witnesses now expose the pressure-free curl form of the
vorticity equation. -/
def navierBKMVorticityResidualEquationNode : NavierProofNode where
  id := "navier.bkm.vorticity-residual-curl-equation"
  status := .checked
  truthValue := ⟨85, 88⟩
  evidence := "vorticityResidualCurlEquationOn names the pressure-free curl equation spatialVorticity(momentumPressureResidual nu u)=0 on a slab. ExplicitFiniteTimeRegularityWitness.vorticityResidualCurlEquationOn proves every finite-time witness satisfies it, and finiteTimeWitness_BKMData_vorticityResidualCurl_packet packages it with BKM envelope data. Validation lab ns-bkm-vorticity-equation-lab-20260629.json passed Taylor-Green vorticity-equation and random solenoidal curl-convection identity checks. PLN STV <s=.85,c=.88>, ITV [.748,.868], PROGRESS 45%."
  blocker := "This is the exact pressure-free curl surface supplied by the concrete momentum equation. Expanding it into the standard transport/diffusion/stretching form now factors through residualCurlExpansionDefect; proving that defect vanishes for smooth incompressible fields remains inside BKMAnalyticContinuationLemma."

/-- The residual-curl expansion is reduced to one named vector-calculus defect. -/
def navierBKMResidualCurlExpansionNode : NavierProofNode where
  id := "navier.bkm.residual-curl-expansion-defect"
  status := .checked
  truthValue := ⟨87, 88⟩
  evidence := "residualCurlExpansionDefect names curl(nu Delta u - partial_t u - (u.grad)u) plus the standard vorticity-equation residual partial_t omega + (u.grad)omega - nu Delta omega - (omega.grad)u. concreteVorticityEquationOn_of_residualCurlExpansionClosedOn proves that residual-curl zero plus vanishing defect gives concreteVorticityEquationOn, and ExplicitFiniteTimeRegularityWitness.concreteVorticityEquationOn_of_residualCurlExpansionDefectVanishes shows finite-time witnesses would supply the standard vorticity equation once BKMResidualCurlExpansionDefectVanishes is proved. Validation lab ns-bkm-residual-curl-expansion-lab-20260629.json passed Taylor-Green and random solenoidal periodic checks. PLN STV <s=.87,c=.88>, ITV [.7656,.8656], PROGRESS 50%."
  blocker := "The exact remaining vector-calculus identity is BKMResidualCurlExpansionDefectVanishes: for every smooth velocity that is divergence-free on the slab, residualCurlExpansionDefect vanishes on the slab. This requires curl/time-derivative commutation, curl/Laplacian commutation, and the incompressible curl-convection identity."

/-- The residual-curl expansion target is decomposed into four exact
differential identities. -/
def navierBKMResidualCurlDifferentialIdentitiesNode : NavierProofNode where
  id := "navier.bkm.residual-curl-differential-identities"
  status := .checked
  truthValue := ⟨88, 88⟩
  evidence := "residualCurlLinearityDefect, vorticityTimeCommutationDefect, vorticityLaplacianCommutationDefect, and vorticityConvectionExpansionDefect name the exact pointwise identities needed to expand residual curl into the standard vorticity equation. residualCurlLinearityDefect_eq_zero_of_differentiableAt proves the residual-field curl-linearity defect vanishes from spatial differentiability of the Laplacian, time-derivative, and convection fields. spatialLaplacianField_differentiableAt_of_smooth, timeVelocityDerivativeField_differentiableAt_of_smooth, and spatialConvectionField_differentiableAt_of_smooth derive all three differentiability pieces from smoothSpaceTimeVelocity, and residualCurlLinearityClosedOn_of_smooth closes slabwise curl-linearity from smoothness alone. smoothSpaceTimeVelocity_isSymmSndFDerivAt and smoothSpaceTimeVelocity_fderiv_fderiv_swap provide the checked second-derivative symmetry bridge for mixed partials. spatialDerivativeComponent_time_derivative_eq_timeVelocityDerivativeField proves scalar spatial/time derivative commutation, timeVorticityDerivative_eq_spatialVorticity_timeVelocityDerivativeField lifts it to the concrete curl, and vorticityTimeCommutationClosedOn_of_smooth closes curl/time commutation on every slab from smoothSpaceTimeVelocity. The smoothness bridges for spatialDerivativeComponent, spatialVorticity, timeVorticityDerivative, and spatialVorticity(timeVelocityDerivativeField) remain available for the next commutation identities. residualCurlCommutationExpansionClosedOn packages the remaining commutation/expansion identities, residualCurlExpansionClosedOn_of_smooth_commutationExpansion closes the expansion defect on a slab from that package, and BKMResidualCurlDifferentialIdentitiesClosed_of_commutationExpansion reduces the global decomposed target to BKMResidualCurlCommutationExpansionClosed. Validation lab ns-bkm-residual-curl-defect-decomposition-lab-20260629.json passed 5/5 Taylor-Green and random solenoidal checks. PLN STV <s=.88,c=.88>, ITV [.7744,.8944], PROGRESS 72%."
  blocker := "The residual-curl linearity and curl/time commutation subidentities are checked from smoothSpaceTimeVelocity. The remaining vector-calculus work for BKMResidualCurlCommutationExpansionClosed is curl/Laplacian commutation and the incompressible curl-convection identity for arbitrary smooth incompressible velocity fields."

/-- Once the standard vorticity equation is available, the BKM growth term is
checked and controlled by the stretching estimate. -/
def navierBKMVorticityGrowthNode : NavierProofNode where
  id := "navier.bkm.standard-vorticity-growth"
  status := .checked
  truthValue := ⟨86, 88⟩
  evidence := "vorticityMaterialDiffusionRemainder names partial_t omega + (u.grad)omega - nu Delta omega. vorticityMaterialDiffusionRemainder_eq_vorticityStretchingTerm proves that concreteVorticityEquationOn identifies this remainder with (omega.grad)u, and uniform_vorticityMaterialDiffusionRemainder_boundUpTo plus uniform_vorticityMaterialDiffusionPower_boundUpTo lift the checked stretching bounds to the material-minus-diffusion growth and enstrophy-production terms. PLN STV <s=.86,c=.88>, ITV [.7568,.8608], PROGRESS 49%."
  blocker := "This closes the growth estimate downstream of concreteVorticityEquationOn. The remaining analytic seam is deriving concreteVorticityEquationOn from residual curl and smooth incompressible finite-time witnesses, then completing log-Sobolev/high-norm continuation."

/-- Once log-Sobolev/Biot-Savart gradient control is supplied, the checked BKM
growth estimates use its logarithmic envelope directly. -/
def navierBKMLogSobolevControlNode : NavierProofNode where
  id := "navier.bkm.log-sobolev-gradient-control"
  status := .checked
  truthValue := ⟨87, 88⟩
  evidence := "bkmLogSobolevGradientEnvelope records the downstream envelope shape C * (1 + Omega(t) * log(exp(1) + H(t))). BKMLogSobolevGradientControlOn.to_spatialGradientOperatorEnvelopeOn converts a supplied log-Sobolev/Biot-Savart gradient-control hypothesis into spatialGradientOperatorEnvelopeOn, and BKMLogSobolevGrowthEstimateClosed_proved feeds that envelope into the checked material-vorticity and enstrophy-production bounds. Validation probe ns-bkm-log-sobolev-probe-20260629.json passed Taylor-Green plus four random solenoidal periodic fields. PLN STV <s=.87,c=.88>, ITV [.7656,.8656], PROGRESS 51%."
  blocker := "This closes the downstream interface, not the analytic log-Sobolev theorem itself. BKMAnalyticContinuationLemma still must prove such gradient control from residual curl, Biot-Savart/log-Sobolev estimates, a high-norm envelope, and the integrable vorticity envelope."

/-- The BKM route is now reduced to one explicitly named analytic lemma. -/
def navierBKMAnalyticReductionNode : NavierProofNode where
  id := "navier.bkm.single-analytic-lemma"
  status := .checked
  truthValue := ⟨86, 88⟩
  evidence := "BKMVorticityStretchingEstimateClosed_proved closes the stretching subdependency, finite-time witnesses now supply vorticityResidualCurlEquationOn, BKMResidualCurlExpansionAlgebraClosed_proved closes the algebra from residual-curl zero plus vanishing expansion defect to concreteVorticityEquationOn, BKMStandardVorticityGrowthEstimateClosed_proved closes the standard-equation growth estimate, BKMLogSobolevGrowthEstimateClosed_proved closes the supplied-log-Sobolev-control growth interface, and BKMContinuation_reduced_to_single_analytic_lemma proves that the repaired nonnegative-horizon BKM target follows from the single named hypothesis BKMAnalyticContinuationLemma. PLN STV <s=.86,c=.88>, ITV [.7568,.8608], PROGRESS 53%."
  blocker := "BKMAnalyticContinuationLemma is the remaining precise analytic lemma: for positive viscosity smooth divergence-free finite-energy data, every finite-time witness on a nonnegative slab with residual-curl vorticity equation and integrable vorticity envelope must extend to ExplicitConcreteNavierStokesGlobalOutput. Its proof must prove BKMResidualCurlExpansionDefectVanishes, prove the log-Sobolev/Biot-Savart gradient control hypothesis, then supply high-norm/enstrophy differential inequality and continuation/Gronwall closure."

/-- The one analytic BKM lemma is now split into explicit component targets. -/
def navierBKMAnalyticComponentsNode : NavierProofNode where
  id := "navier.bkm.analytic-components"
  status := .checked
  truthValue := ⟨87, 88⟩
  evidence := "BKMLogSobolevGradientControlFromEnvelope and BKMHighNormContinuationFromLogControl name the two analytic estimates still downstream of BKMResidualCurlExpansionDefectVanishes. BKMAnalyticContinuationLemma_of_components proves these three components imply BKMAnalyticContinuationLemma, and BKMContinuation_reduced_to_analytic_components proves the repaired nonnegative-horizon BKM target follows from the component bundle. PLN STV <s=.87,c=.88>, ITV [.7656,.8656], PROGRESS 55%."
  blocker := "The component split is a checked assembly layer, not the analytic proof itself. The remaining work is to prove residual-curl expansion defect vanishing, derive the log-Sobolev/Biot-Savart gradient envelope from the BKM vorticity data, and close the high-norm continuation/Gronwall step without assuming the global output."

/-- The nonzero slice-Schwartz kernel is checked, but it is not yet an
unconditional positive canary. -/
def navierNonzeroSchwartzEnergyKernelNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-kernel"
  status := .checked
  truthValue := ⟨79, 88⟩
  evidence := "SchwartzEnergyIdentityKernel, SchwartzMomentumClosureKernel, SchwartzConcreteSolutionKernel, NonzeroSchwartzConcreteNavierStokesSolution.energyIdentityKernel, NonzeroSchwartzConcreteNavierStokesSolution.nonzero_energyMomentumCanary_packet, twoModeSchwartzPressureSlice_nonzeroSchwartzConcreteSolution_of_momentumEquation, twoModeSchwartzPressureSlice_nonzero_energyIdentityKernel_of_momentumEquation, oneOneTwoModeSchwartzZeroPressure_nonzeroSchwartzConcreteSolution_of_inviscidClosure, and oneOneTwoModeSchwartzZeroPressure_nonzero_energyIdentityCanary_packet package the nonzero witness, pressure and convection cancellations, viscous formula, meaningful identity, literal momentum equation, incompressibility, pressure-residual equality, residual-curl-zero gate, and an exact whole-time zero-pressure two-profile canary at viscosity 0 when the inviscid closure is supplied. PLN STV <s=.79,c=.88>, ITV [.6952,.8152], PROGRESS 52%."
  blocker := "This is nonzero-preserving and PDE-grounded, and the reusable API now exposes both the energy cancellations and the pressure-closure gates from a single packet. The new inhabited class is still conditional on a nonzero divergence-free profile pair satisfying the inviscid two-profile closure, and it is at viscosity 0; the remaining positive-viscosity canary obligation is an exact nonzero evolution with Schwartz pressure slices, or a broader structural obstruction."

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

/-- The localized nilpotent stream seed is nonzero Schwartz data, but its
stationary inviscid pressure closure is blocked by residual curl. -/
def navierNonzeroSchwartzLocalizedNilpotentStreamObstructionNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-localized-nilpotent-stream-obstruction"
  status := .checked
  truthValue := ⟨88, 91⟩
  evidence := "nsLocalizedNilpotentStreamDivergenceFreeInitialVelocity_nonzero proves that the compactly supported localized nilpotent stream function gives a concrete nonzero divergence-free Schwartz initial datum, while spatialVorticity_momentumPressureResidual_zero_localizedNilpotentStreamVelocityField_origin and not_exists_smoothPressure_momentumEquation_zero_localizedNilpotentStreamVelocityField prove that the stationary inviscid pressure-closure route has nonzero residual curl at the origin and no smooth pressure repair. The local-germ theorems spatialVorticity_momentumPressureResidual_zero_of_localizedNilpotentStreamVelocityField_germ_origin, not_exists_smoothPressure_momentumEquation_zero_of_localizedNilpotentStreamVelocityField_germ_origin, and not_exists_nonzeroSchwartzConcreteSolution_localizedNilpotentStreamVelocityField_germ_stationary_at strengthen this to any inviscid candidate whose velocity germ matches the localized nilpotent stream and whose instantaneous time-derivative germ vanishes there. PLN STV <s=.88,c=.91>, ITV [.8008,.8908], PROGRESS 90%."
  blocker := "This supplies an inhabited localized nilpotent Schwartz seed and a germ-level pressure-closure obstruction for its stationary inviscid shortcut. It is not an exact positive-viscosity nonzero solution; the remaining canary must use nonstationary time dependence or a different localized profile with curl-free residual closure."

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
  truthValue := ⟨90, 91⟩
  evidence := "antiProfileSchwartzVelocity_nonzero_iff_exists_amplitude_ne proves that, for any nonzero Schwartz profile f, the anti-profile reconstruction a(t)f + b(t)(-f) is nonzero exactly when the scalar amplitudes differ somewhere; localizedStreamAntiProfile_velocity_nonzero_iff_exists_amplitude_ne specializes this to the localized stream seed, not_exists_nonzeroSchwartzConcreteSolution_equalAmplitudeAntiProfileVelocity excludes the equal-amplitude boundary from the nonzero interface, and nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_forces_amplitude_ne gives the necessary unequal-amplitude condition. At positive viscosity, nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_forces_amplitudeDifference_nonconstant requires genuinely time-varying amplitude difference, nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_exists_nonzero_endpoint_with_amplitudeDifference_sq_strict_drop gives a nonzero endpoint whose whole past ray has strictly decreasing squared amplitude difference, and not_exists_nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_amplitudeDifference_sq_nondecrease_before_nonzero_endpoint_of_pos_viscosity rejects nondecreasing squared amplitude-difference subintervals before a later nonzero endpoint. PLN STV <s=.90,c=.91>, ITV [.819,.909], PROGRESS 68%."
  blocker := "This gives the exact anti-profile nonzero, positive-viscosity nonstationary, and endpoint support boundary, not a pressure-slice momentum closure. The remaining canary must still prove that a time-varying unequal-amplitude localized stream/anti-stream or another non-polynomial Schwartz profile satisfies the full Navier-Stokes equation with Schwartz pressure slices."

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

/-- Positive-viscosity nonzero canaries cannot have periodic energy, periodic
velocity, or local repeated nonzero velocity slices. -/
def navierNonzeroSchwartzNoEnergyRecurrenceNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-no-energy-recurrence"
  status := .checked
  truthValue := ⟨96, 89⟩
  evidence := "normalizedKineticEnergy_eq_of_velocity_slice_eq, normalizedKineticEnergy_ne_periodic_endpoint_at_nonzero_of_pos_viscosity, not_velocity_slice_eq_after_nonzero_of_pos_viscosity, not_forall_normalizedKineticEnergy_periodic_of_pos_viscosity, and not_forall_velocity_periodic_of_pos_viscosity prove that a positive-viscosity nonzero slice-Schwartz solution cannot return normalized kinetic energy, repeat a nonzero velocity slice at any strictly later time, or be positive-periodic in velocity. The global repeated-slice no-go exposes the same filter for candidate generators. PLN STV <s=.96,c=.89>, ITV [.8544,.9644], PROGRESS 80%."
  blocker := "This rules out periodic, recurrent, and locally repeated-slice positive-viscosity shortcut canaries, but it still does not construct the required positive-viscosity pressure-slice closure."

/-- Pressure residual curl is now a reusable exact-closure gate. -/
def navierSchwartzPressureResidualCurlGateNode : NavierProofNode where
  id := "navier.energy.schwartz-pressure-residual-curl-gate"
  status := .checked
  truthValue := ⟨87, 89⟩
  evidence := "momentumPressureResidual_spatialVorticity_zero proves that every ordinary slice-Schwartz concrete solution has curl-free pressure residual νΔu - ∂tu - (u.grad)u, and not_exists_schwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero proves that any velocity whose residual curl is nonzero somewhere cannot inhabit the interface. The regression undamped_unit_heat_shear_not_schwartz_solution_velocity_regression applies this gate to an explicit heat-shear false positive. PLN STV <s=.87,c=.89>, ITV [.7743,.8843], PROGRESS 70%."
  blocker := "This is a sharp pressure-closure filter for candidate velocities. It does not construct the required nonzero localized Schwartz pressure-slice closure."

/-- Residual-curl failures are now first-class generator certificates. -/
def navierSchwartzPressureClosureCertificateNode : NavierProofNode where
  id := "navier.energy.schwartz-pressure-closure-certificate"
  status := .checked
  truthValue := ⟨90, 91⟩
  evidence := "PressureClosureObstructionCertificate packages a residual-curl witness into reusable no-smooth-pressure, no-momentum-kernel, no-concrete-kernel, no-ordinary-solution, and no-nonzero-solution consequences. localizedNilpotentStreamPressureClosureObstructionCertificate and localizedNilpotentStream_pressureClosureCertificate_packet instantiate the certificate for an explicit nonzero divergence-free Schwartz localized nilpotent stream seed at viscosity 0. PLN STV <s=.90,c=.91>, ITV [.819,.909], PROGRESS 82%."
  blocker := "This turns one failed localized Schwartz generator into a reusable certificate API. It is still a pressure-closure obstruction, not the requested positive-viscosity nonzero canary; a successful canary must prove curl-free residual closure and construct Schwartz pressure slices."

/-- The two-mode generator now exposes the exact residual-curl obligation at
the slice-Schwartz solution interface. -/
def navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-finite-mode-residual-curl-boundary"
  status := .checked
  truthValue := ⟨91, 91⟩
  evidence := "SchwartzMomentumClosureKernel and SchwartzConcreteSolutionKernel factor the momentum equation, divergence, pressure-residual equality, and residual-curl-zero condition out of any slice-Schwartz concrete solution. oneOneTwoModeSchwartzVelocity_lapSum_residualVorticity_zero_of_schwartzConcreteSolution and the not_exists_* residual-vorticity theorems specialize this to the constant-amplitude two-mode generator. oneOneTwoModeSchwartzVelocity_inviscidZeroPressureCanary_and_residualCurlBoundary now packages the positive side too: the inviscid zero-pressure closure returns a nonzero whole-time slice-Schwartz energy-identity canary at viscosity 0, while any nonzero viscous residual curl blocks reusing the same velocity in the ordinary or nonzero interface at viscosity ν. PLN STV <s=.91,c=.91>, ITV [.8281,.9181], PROGRESS 78%."
  blocker := "This turns the two-mode pressure-closure search into a concrete route boundary. It still does not provide explicit profiles satisfying the inviscid closure and curl-free viscous residual, and it does not construct a positive-viscosity nonzero solution."

/-- Stationary inviscid one-profile data now have a direct nonzero
slice-Schwartz constructor once the pressure closure is supplied. -/
def navierNonzeroSchwartzStationaryInviscidConstructorNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-stationary-inviscid-constructor"
  status := .checked
  truthValue := ⟨78, 88⟩
  evidence := "stationaryInviscidSchwartzPressureSlice_nonzeroSchwartzConcreteSolution and stationaryInviscidSchwartzPressureSlice_nonzero_concreteSolutionKernel prove that any nonzero divergence-free Schwartz initial velocity with a Schwartz pressure slice satisfying the stationary inviscid pointwise closure inhabits NonzeroSchwartzConcreteNavierStokesSolution at viscosity 0 and carries SchwartzConcreteSolutionKernel. stationaryInviscidSchwartzPressureSlice_nonzero_energyIdentityCanary_packet now exposes the constructed witness with exact velocity/pressure equalities, nonzero witness, both cancellation integrals, the coordinate viscous formula, and the zero-viscosity meaningful energy identity. PLN STV <s=.78,c=.88>, ITV [.6864,.8064], PROGRESS 75%."
  blocker := "This exposes the exact stationary localized Euler-style pressure-closure seam. It is still conditional on an explicit closure witness and works at viscosity 0, so it does not satisfy the positive-viscosity nonzero canary obligation."

/-- The exact Stokes-flow subroute is now separated as a reusable kernel. -/
def navierNonzeroSchwartzStokesKernelNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-stokes-kernel"
  status := .checked
  truthValue := ⟨85, 89⟩
  evidence := "SchwartzStokesFlowKernel packages any slice-Schwartz concrete solution whose convection and pressure-gradient terms vanish into the exact Stokes equation partial_t u = nu*Delta u plus the inherited concrete solution kernel. NonzeroSchwartzConcreteNavierStokesSolution.stokesFlow_strictDissipation_packet proves that every positive-viscosity nonzero inhabitant of this subroute has a strict negative normalized-energy derivative at some time. stokesFlow_exists_nonzero_endpoint_with_strict_past_energy_drop_packet proves that any inhabited positive-viscosity Stokes candidate has a nonzero endpoint whose whole past support ray is strictly energy-ordered; stokesFlow_endpoint_noRepeatedVelocitySlice_packet strengthens this to no repeated velocity slice on any nontrivial subinterval before that endpoint. The global energy-nondecrease, repeated-slice, and positive-period recurrence no-go theorems expose these filters for Stokes candidate generators. PLN STV <s=.85,c=.89>, ITV [.7565,.8665], PROGRESS 85%."
  blocker := "This is still conditional on an inhabited positive-viscosity nonzero Stokes-flow solution. The remaining canary obligation is to construct such a bounded whole-real-time Schwartz heat/Stokes evolution with strict, nonrecurrent past support, or prove the bounded-eternal Stokes/pressure-closure subroute is empty."

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

/-- One-profile separable candidates now face a checked amplitude-order gate. -/
def navierNonzeroSchwartzOneProfileAmplitudeBoundaryNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-one-profile-amplitude-boundary"
  status := .checked
  truthValue := ⟨89, 89⟩
  evidence := "integral_norm_sq_pos_of_schwartz_ne_zero and normalizedKineticEnergy_scalar_smul_schwartz compute the normalized kinetic energy of a scalar-modulated nonzero Schwartz profile. scalarProfile_amplitude_sq_strict_lt_before_nonzero_endpoint_of_pos_viscosity proves that if a positive-viscosity exact nonzero solution is represented as u(t,x)=a(t)f(x), then before any later nonzero endpoint the squared amplitude a(t)^2 strictly decreases forward in time; exists_nonzero_endpoint_with_scalarProfile_amplitude_sq_strict_drop and not_exists_nonzeroSchwartzConcreteSolution_scalarProfile_amplitude_sq_nondecrease_before_nonzero_endpoint_of_pos_viscosity package the nonzero-endpoint and global no-go forms. PLN STV <s=.89,c=.89>, ITV [.7921,.9021], PROGRESS 88%."
  blocker := "This rules out separable one-profile positive-viscosity shortcuts with repeated or nondecreasing absolute amplitude on the past support ray. It still does not construct the required nonzero pressure-slice closure, and it leaves genuinely multi-profile/nonseparable localized evolution or a full bounded-eternal Stokes emptiness theorem as the remaining seam."

/-- Bounded eternal slice-Schwartz solutions cannot carry a uniform positive
past dissipation gap. -/
def navierNonzeroSchwartzNoUniformPastDissipationNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-no-uniform-past-dissipation"
  status := .checked
  truthValue := ⟨97, 94⟩
  evidence := "not_forall_past_coordinateEnergyDissipationRate_ge proves that bounded whole-time slice-Schwartz concrete solutions cannot keep corrected coordinate dissipation uniformly above any positive constant on an entire past ray. not_forall_future_coordinateEnergyDissipationRate_ge proves the matching future-ray obstruction from nonnegative normalized kinetic energy, and exists_future_coordinateEnergyDissipationRate_lt plus not_exists_nonzeroSchwartzConcreteSolution_uniform_future_dissipation_gap package the positive-sample and global no-go forms. exists_past_nonzero_with_small_positive_coordinateEnergyDissipationRate proves that, at positive viscosity before a later nonzero endpoint, every positive threshold has an earlier nonzero slice with strictly positive but smaller corrected dissipation. not_forall_past_coordinateEnergyDissipationRate_ge_mul_normalizedKineticEnergy and not_exists_nonzeroSchwartzConcreteSolution_past_spectral_floor rule out positive whole-past Poincare/spectral floors of the form lambda times normalized energy below corrected dissipation. exists_past_nonzero_with_small_positive_dissipation_per_energy, exists_nonzero_endpoint_with_arbitrarily_small_past_dissipation_per_energy, exists_past_nonzero_with_small_positive_dissipation_ratio, exists_nonzero_endpoint_with_arbitrarily_small_past_dissipation_ratio, and not_exists_nonzeroSchwartzConcreteSolution_past_dissipation_ratio_floor strengthen this from a negative floor theorem to positive nonzero witnesses with arbitrarily small positive corrected-dissipation Rayleigh quotient. not_forall_past_coordinateEnstrophyAt_ge_mul_normalizedKineticEnergy, exists_past_nonzero_with_small_positive_coordinateEnstrophy_ratio, not_exists_nonzeroSchwartzConcreteSolution_past_coordinateEnstrophy_floor, not_exists_nonzeroSchwartzConcreteSolution_past_coordinateEnstrophy_ratio_floor, not_exists_nonzeroSchwartzConcreteSolution_past_exact_coordinateEnstrophyRayleigh_of_posViscosity, not_exists_nonzeroSchwartzConcreteSolution_past_exact_coordinateEnstrophyRatioRayleigh_of_posViscosity, not_exists_nonzeroSchwartzConcreteSolution_oneProfile_past_exact_coordinateEnstrophyRayleigh_of_posViscosity, and not_exists_nonzeroSchwartzConcreteSolution_oneProfile_past_exact_coordinateEnstrophyRatioRayleigh_of_posViscosity lift the same obstruction to spatial coordinate-enstrophy Rayleigh quotients, exact equality, and fixed-profile/eigenmode shortcuts. coordinateEnstrophyAt_scalar_smul_schwartz computes the coordinate-enstrophy factor for scalar-modulated Schwartz profiles, and not_exists_nonzeroSchwartzConcreteSolution_oneProfile_of_posViscosity plus not_exists_nonzeroSchwartzStokesFlow_oneProfile_of_posViscosity now rule out every positive-viscosity nonzero fixed-profile concrete solution, including the exact zero-convection/zero-pressure-gradient Stokes specialization. stokesFlow_noUniformFutureDissipation_packet, not_exists_nonzeroSchwartzStokesFlow_uniform_future_dissipation_gap, stokesFlow_positiveViscosity_profileGapObstruction_packet, stokesFlow_endpointStrictEnergy_and_smallPastCoordinateEnstrophyRatio_packet, not_exists_nonzeroSchwartzStokesFlow_past_coordinateEnstrophy_floor_of_posViscosity, not_exists_nonzeroSchwartzStokesFlow_past_coordinateEnstrophy_ratio_floor_of_posViscosity, not_exists_nonzeroSchwartzStokesFlow_past_exact_coordinateEnstrophyRayleigh_of_posViscosity, and not_exists_nonzeroSchwartzStokesFlow_past_exact_coordinateEnstrophyRatioRayleigh_of_posViscosity specialize the future gap, spatial floor, quotient-floor, exact Rayleigh-equality, and endpoint-parametric strict-energy/low-Rayleigh obstructions to exact Stokes-flow candidates. PLN STV <s=.97,c=.94>, ITV [.9118,.9718], PROGRESS 97%."
  blocker := "This rules out uniform positive past or future dissipation, corrected-dissipation Poincare/spectral-floor certificates, spatial coordinate-enstrophy Poincare floors, positive whole-past corrected-dissipation Rayleigh-quotient floors, positive whole-past spatial Rayleigh-quotient floors, exact positive spatial Rayleigh equality, fixed-profile exact Rayleigh/eigenmode shortcuts, every positive-viscosity nonzero scalar fixed-profile solution, and any zero-convection/zero-pressure-gradient Stokes fixed-profile canary. It still does not construct the required nonzero inhabitant or prove the full bounded-eternal Stokes/pressure-closure subroute empty without a stronger structural frequency/localization theorem."

/-- Finite-profile Stokes generators with a positive Rayleigh floor are now
blocked as bounded eternal positive-viscosity canaries. -/
def navierNonzeroSchwartzStokesFiniteProfileRayleighObstructionNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-stokes-finite-profile-rayleigh-obstruction"
  status := .checked
  truthValue := ⟨93, 92⟩
  evidence := "StokesFiniteProfileRayleighFloorCertificate names the exact finite-profile generator certificate: zero convection, zero pressure gradient, a nonzero endpoint, and a positive whole-past spatial Rayleigh floor for coordinate enstrophy divided by normalized kinetic energy. stokesFlow_finiteProfileRayleighFloorBoundary_packet proves that every inhabited positive-viscosity exact Stokes candidate must instead evade every positive floor, with earlier nonzero slices of arbitrarily small positive spatial Rayleigh quotient and strict past energy ordering. stokesFiniteProfileRayleighFloorCertificate_false_of_posViscosity and not_exists_nonzeroSchwartzStokesFlow_finiteProfileRayleighFloorCertificate rule out the certified finite-profile Stokes canary route. PLN STV <s=.93,c=.92>, ITV [.8556,.9356], PROGRESS 89%."
  blocker := "This is a route obstruction for finite-profile or spectral-gap Stokes generators: any such generator must either fail to prove a positive whole-past spatial Rayleigh floor or leave the exact Stokes subroute. It is not an explicit positive-viscosity solution; the remaining open canary must use a genuinely low-frequency-escaping nonseparable evolution with curl-free pressure residual, or prove a stronger full Stokes/pressure-closure emptiness theorem."

/-- The explicit nonzero slice-Schwartz canary remains open until the
finite-mode closure hypotheses are inhabited by concrete profiles. -/
def navierNonzeroSchwartzCanaryNode : NavierProofNode where
  id := "navier.energy.nonzero-schwartz-canary"
  status := .openGoal
  truthValue := ⟨84, 88⟩
  evidence := "The checked nonzero kernel removes the old zero-flow loophole from the energy-identity surface; the line-invariant, exact heat-shear boundary, rank-one zero-convection, symmetric-shear, nilpotent-shear pressure-residual, frozen nilpotent-slice, localized nilpotent stream stationary pressure-residual, anti-profile cancellation, exact anti-profile endpoint amplitude-boundary, anti-profile constant-difference obstruction, positive-viscosity stationary, strict-dissipation-kernel, flat-energy zero-rigidity, local-extremum energy, pointwise strict-derivative, local energy plateau, immediate right-drop, sampled right-drop, strict future-drop, energy-recurrence and repeated-slice, generic pressure-residual-curl, finite-mode residual-curl, stationary-inviscid constructor, zero-pressure two-profile viscosity-0 canary, Stokes-flow kernel, Stokes rank-one obstruction, generalized zero-restart gates, past-dissipation ray, endpoint nonzero-support kernel, one-profile amplitude boundary, no-uniform-past-dissipation obstruction, no-uniform-future-dissipation obstruction, no-past-spectral-floor obstruction, past dissipation-per-energy collapse, past Rayleigh-quotient collapse, spatial Rayleigh-quotient collapse, general exact Rayleigh-equality obstruction, one-profile exact Rayleigh-equality obstruction, exact Stokes Rayleigh-equality obstructions, fixed-profile positive-viscosity emptiness, fixed-profile Stokes emptiness, and finite-profile Stokes Rayleigh-floor obstruction remove, constrain, or expose many shortcut classes at stronger interfaces; and the localized stream-function seeds give concrete nonzero divergence-free Schwartz data. No unconditional positive-viscosity nonzero exact slice-Schwartz solution inhabitant is committed yet. PLN STV <s=.84,c=.88>, ITV [.7392,.8592], PROGRESS 92%."
  blocker := "Close or refute the pressure-slice closure and time evolution for the explicit localized stream-function seed or a comparable non-polynomial Schwartz profile; do not count a conditional constructor, seed-only datum, viscosity-0 finite-mode zero-pressure canary, classical heat-shear exact solution that fails Schwartz decay, rank-one zero-convection obstruction, nilpotent-shear pressure-residual obstruction, frozen nilpotent-slice obstruction, localized nilpotent stream stationary pressure-residual obstruction, profile-level nonzero anti-profile cancellation, an anti-profile endpoint amplitude-boundary guardrail, an anti-profile constant-difference obstruction, a positive-viscosity stationary obstruction, a strict-dissipation theorem conditional on the nonzero interface, a flat-energy zero-rigidity obstruction, a local-extremum energy obstruction, a pointwise strict-derivative gate, a local energy plateau obstruction, an immediate right-drop gate, a sampled right-drop gate, a strict future-drop gate, an energy-recurrence or repeated-slice obstruction, a residual-curl pressure-closure rejection, a finite-mode residual-curl boundary, a stationary inviscid closure constructor, a conditional Stokes-flow kernel, a Stokes rank-one obstruction, a zero-restart obstruction, a past-dissipation ray theorem, an endpoint support-order theorem, a one-profile amplitude-boundary theorem, a no-uniform-past-dissipation theorem, a no-uniform-future-dissipation theorem, a no-past-spectral-floor theorem, a past dissipation-per-energy collapse theorem, a past Rayleigh-quotient collapse theorem, a spatial Rayleigh-quotient collapse theorem, a general exact Rayleigh-equality obstruction, a one-profile exact Rayleigh-equality obstruction, an exact Stokes Rayleigh-equality obstruction, a fixed-profile positive-viscosity emptiness theorem, a fixed-profile Stokes emptiness theorem, a finite-profile Stokes Rayleigh-floor obstruction, or algebraic finite-mode boundary case as the requested positive canary."

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
  , navierBKMVorticityStretchingNode
  , navierBKMVorticityResidualEquationNode
  , navierBKMResidualCurlExpansionNode
  , navierBKMResidualCurlDifferentialIdentitiesNode
  , navierBKMVorticityGrowthNode
  , navierBKMLogSobolevControlNode
  , navierBKMAnalyticReductionNode
  , navierBKMAnalyticComponentsNode
  , navierNonzeroSchwartzEnergyKernelNode
  , navierNonzeroSchwartzLineInvariantObstructionNode
  , navierNonzeroSchwartzHeatShearBoundaryNode
  , navierNonzeroSchwartzRankOneShearObstructionNode
  , navierNonzeroSchwartzSymmetricShearObstructionNode
  , navierNonzeroSchwartzNilpotentShearPressureObstructionNode
  , navierNonzeroSchwartzLocalizedStreamSeedNode
  , navierNonzeroSchwartzLocalizedNilpotentStreamObstructionNode
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
  , navierSchwartzPressureClosureCertificateNode
  , navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode
  , navierNonzeroSchwartzStationaryInviscidConstructorNode
  , navierNonzeroSchwartzStokesKernelNode
  , navierNonzeroSchwartzStokesRankOneObstructionNode
  , navierNonzeroSchwartzZeroRestartNode
  , navierNonzeroSchwartzPastDissipationNode
  , navierNonzeroSchwartzEndpointSupportNode
  , navierNonzeroSchwartzOneProfileAmplitudeBoundaryNode
  , navierNonzeroSchwartzNoUniformPastDissipationNode
  , navierNonzeroSchwartzStokesFiniteProfileRayleighObstructionNode
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

theorem navierBKMVorticityStretchingNode_checked :
    navierBKMVorticityStretchingNode.status = .checked := by
  rfl

theorem navierBKMVorticityResidualEquationNode_checked :
    navierBKMVorticityResidualEquationNode.status = .checked := by
  rfl

theorem navierBKMResidualCurlExpansionNode_checked :
    navierBKMResidualCurlExpansionNode.status = .checked := by
  rfl

theorem navierBKMResidualCurlDifferentialIdentitiesNode_checked :
    navierBKMResidualCurlDifferentialIdentitiesNode.status = .checked := by
  rfl

theorem navierBKMVorticityGrowthNode_checked :
    navierBKMVorticityGrowthNode.status = .checked := by
  rfl

theorem navierBKMLogSobolevControlNode_checked :
    navierBKMLogSobolevControlNode.status = .checked := by
  rfl

theorem navierBKMAnalyticReductionNode_checked :
    navierBKMAnalyticReductionNode.status = .checked := by
  rfl

theorem navierBKMAnalyticComponentsNode_checked :
    navierBKMAnalyticComponentsNode.status = .checked := by
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

theorem navierNonzeroSchwartzLocalizedNilpotentStreamObstructionNode_checked :
    navierNonzeroSchwartzLocalizedNilpotentStreamObstructionNode.status = .checked := by
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

theorem navierSchwartzPressureClosureCertificateNode_checked :
    navierSchwartzPressureClosureCertificateNode.status = .checked := by
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

theorem navierNonzeroSchwartzOneProfileAmplitudeBoundaryNode_checked :
    navierNonzeroSchwartzOneProfileAmplitudeBoundaryNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzNoUniformPastDissipationNode_checked :
    navierNonzeroSchwartzNoUniformPastDissipationNode.status = .checked := by
  rfl

theorem navierNonzeroSchwartzStokesFiniteProfileRayleighObstructionNode_checked :
    navierNonzeroSchwartzStokesFiniteProfileRayleighObstructionNode.status = .checked := by
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

theorem currentNavierBKMVorticityStretching_node
    {u : NSVelocityField} {T G B : ℝ}
    (hG : uniformSpatialGradientOperatorBoundUpTo u T G)
    (hω : uniformVorticityBoundUpTo u T B) :
    (0 ≤ G * B ∧
      ∀ t x, 0 ≤ t → t ≤ T →
        ‖vorticityStretchingTerm u t x‖ ≤ G * B) ∧
      (0 ≤ G * (B * B) ∧
        ∀ t x, 0 ≤ t → t ≤ T →
          |vorticityStretchingPower u t x| ≤ G * (B * B)) ∧
      navierBKMVorticityStretchingNode.status = .checked := by
  exact
    ⟨uniform_vorticityStretchingTerm_boundUpTo hG hω,
      uniform_vorticityStretchingPower_boundUpTo hG hω,
      navierBKMVorticityStretchingNode_checked⟩

theorem currentNavierBKMVorticityResidualEquation_node
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hBKM : ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn W.velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B) :
    vorticityResidualCurlEquationOn ν W.velocity T ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialVorticity (momentumPressureResidual ν W.velocity) t x = 0) ∧
      navierBKMVorticityResidualEquationNode.status = .checked := by
  exact
    ⟨(finiteTimeWitness_BKMData_vorticityResidualCurl_packet W hBKM).1,
      (finiteTimeWitness_BKMData_vorticityResidualCurl_packet W hBKM).2,
      navierBKMVorticityResidualEquationNode_checked⟩

theorem currentNavierBKMResidualCurlExpansion_node
    {ν T : ℝ} {u : NSVelocityField}
    (hCurl : vorticityResidualCurlEquationOn ν u T)
    (hExpand : residualCurlExpansionClosedOn ν u T) :
    concreteVorticityEquationOn ν u T ∧
      BKMResidualCurlExpansionAlgebraClosed ∧
      navierBKMResidualCurlExpansionNode.status = .checked := by
  exact
    ⟨concreteVorticityEquationOn_of_residualCurlExpansionClosedOn hCurl hExpand,
      BKMResidualCurlExpansionAlgebraClosed_proved,
      navierBKMResidualCurlExpansionNode_checked⟩

theorem currentNavierBKMResidualCurlDifferentialIdentities_node
    {ν T : ℝ} {u : NSVelocityField}
    (hIds : residualCurlDifferentialIdentitiesClosedOn ν u T) :
    residualCurlExpansionClosedOn ν u T ∧
      (residualCurlLinearityDifferentiableOn u T →
        residualCurlLinearityClosedOn ν u T) ∧
      (smoothSpaceTimeVelocity u →
        residualCurlLinearityClosedOn ν u T) ∧
      (smoothSpaceTimeVelocity u →
        residualCurlCommutationExpansionClosedOn u T →
          residualCurlExpansionClosedOn ν u T) ∧
      (smoothSpaceTimeVelocity u →
        smoothSpaceTimeVelocity (timeVelocityDerivativeField u)) ∧
      (BKMResidualCurlCommutationExpansionClosed →
        BKMResidualCurlDifferentialIdentitiesClosed) ∧
      (smoothSpaceTimeVelocity u →
        ∀ tx v w,
          ((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) tx) v) w =
            ((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) tx) w) v) ∧
      (smoothSpaceTimeVelocity u →
        ∀ x coord comp,
          ContDiff ℝ ∞
            (fun s : NSTime => spatialDerivativeComponent u s x coord comp)) ∧
      (smoothSpaceTimeVelocity u →
        ∀ coord comp,
          ContDiff ℝ ∞
            (fun tx : NSSpacetime =>
              spatialDerivativeComponent u tx.1 tx.2 coord comp)) ∧
      (smoothSpaceTimeVelocity u →
        smoothSpaceTimeVelocity (fun t x => spatialVorticity u t x)) ∧
      (smoothSpaceTimeVelocity u →
        smoothSpaceTimeVelocity (fun t x => timeVorticityDerivative u t x)) ∧
      (smoothSpaceTimeVelocity u →
        smoothSpaceTimeVelocity
          (fun t x => spatialVorticity (timeVelocityDerivativeField u) t x)) ∧
      (smoothSpaceTimeVelocity u →
        ∀ t x coord comp,
          fderiv ℝ
            (fun s : NSTime => spatialDerivativeComponent u s x coord comp)
            t (1 : ℝ) =
              spatialDerivativeComponent (timeVelocityDerivativeField u)
                t x coord comp) ∧
      (smoothSpaceTimeVelocity u →
        ∀ t x,
          timeVorticityDerivative u t x =
            spatialVorticity (timeVelocityDerivativeField u) t x) ∧
      (smoothSpaceTimeVelocity u →
        vorticityTimeCommutationClosedOn u T) ∧
      (BKMResidualCurlDifferentialIdentitiesClosed →
        BKMResidualCurlExpansionDefectVanishes) ∧
      (BKMResidualCurlDifferentialIdentitiesClosed →
        BKMLogSobolevGradientControlFromEnvelope →
          BKMHighNormContinuationFromLogControl →
            BKMAnalyticComponentsClosed) ∧
      navierBKMResidualCurlDifferentialIdentitiesNode.status = .checked := by
  exact
    ⟨residualCurlExpansionClosedOn_of_differentialIdentitiesClosedOn hIds,
      residualCurlLinearityClosedOn_of_differentiableOn,
      residualCurlLinearityClosedOn_of_smooth,
      residualCurlExpansionClosedOn_of_smooth_commutationExpansion,
      timeVelocityDerivativeField_smoothSpaceTimeVelocity_of_smooth,
      BKMResidualCurlDifferentialIdentitiesClosed_of_commutationExpansion,
      fun hu tx v w => smoothSpaceTimeVelocity_fderiv_fderiv_swap hu tx v w,
      fun hu x coord comp => spatialDerivativeComponent_contDiff_time_of_smooth hu x coord comp,
      fun hu coord comp => spatialDerivativeComponent_contDiff_spacetime_of_smooth hu coord comp,
      spatialVorticity_smoothSpaceTimeVelocity_of_smooth,
      timeVorticityDerivative_smoothSpaceTimeVelocity_of_smooth,
      spatialVorticity_timeVelocityDerivativeField_smoothSpaceTimeVelocity_of_smooth,
      fun hu t x coord comp =>
        spatialDerivativeComponent_time_derivative_eq_timeVelocityDerivativeField
          hu t x coord comp,
      fun hu t x =>
        timeVorticityDerivative_eq_spatialVorticity_timeVelocityDerivativeField
          hu t x,
      vorticityTimeCommutationClosedOn_of_smooth,
      BKMResidualCurlDifferentialIdentitiesClosed.implies_residualCurlExpansionDefectVanishes,
      BKMAnalyticComponentsClosed_of_residualCurlDifferentialIdentities,
      navierBKMResidualCurlDifferentialIdentitiesNode_checked⟩

theorem currentNavierBKMVorticityGrowth_node
    {ν T G B : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    (hG : uniformSpatialGradientOperatorBoundUpTo u T G)
    (hω : uniformVorticityBoundUpTo u T B) :
    (0 ≤ G * B ∧
      ∀ t x, 0 ≤ t → t ≤ T →
        ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤ G * B) ∧
      (0 ≤ G * (B * B) ∧
        ∀ t x, 0 ≤ t → t ≤ T →
          |vorticityMaterialDiffusionPower ν u t x| ≤ G * (B * B)) ∧
      navierBKMVorticityGrowthNode.status = .checked := by
  exact
    ⟨uniform_vorticityMaterialDiffusionRemainder_boundUpTo hEq hG hω,
      uniform_vorticityMaterialDiffusionPower_boundUpTo hEq hG hω,
      navierBKMVorticityGrowthNode_checked⟩

theorem currentNavierBKMLogSobolevControl_node
    {ν T C : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ}
    (hEq : concreteVorticityEquationOn ν u T)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hΩ : vorticityEnvelopeOn u T Ω) :
    spatialGradientOperatorEnvelopeOn u T
        (bkmLogSobolevGradientEnvelope C Ω H) ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤
          bkmLogSobolevGradientEnvelope C Ω H t * Ω t) ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        |vorticityMaterialDiffusionPower ν u t x| ≤
          bkmLogSobolevGradientEnvelope C Ω H t * (Ω t * Ω t)) ∧
      BKMLogSobolevGrowthEstimateClosed ∧
      navierBKMLogSobolevControlNode.status = .checked := by
  exact
    ⟨(BKMLogSobolevGrowthEstimateClosed_proved ν u T C Ω H hEq hLog hΩ).1,
      (BKMLogSobolevGrowthEstimateClosed_proved ν u T C Ω H hEq hLog hΩ).2.1,
      (BKMLogSobolevGrowthEstimateClosed_proved ν u T C Ω H hEq hLog hΩ).2.2,
      BKMLogSobolevGrowthEstimateClosed_proved,
      navierBKMLogSobolevControlNode_checked⟩

theorem currentNavierBKMAnalyticReduction_node :
    BKMVorticityStretchingEstimateClosed ∧
      BKMResidualCurlExpansionAlgebraClosed ∧
      BKMStandardVorticityGrowthEstimateClosed ∧
      BKMLogSobolevGrowthEstimateClosed ∧
      (BKMAnalyticContinuationLemma →
        ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) ∧
      navierBKMAnalyticReductionNode.status = .checked := by
  exact
    ⟨BKMVorticityStretchingEstimateClosed_proved,
      BKMResidualCurlExpansionAlgebraClosed_proved,
      BKMStandardVorticityGrowthEstimateClosed_proved,
      BKMLogSobolevGrowthEstimateClosed_proved,
      BKMAnalyticContinuationLemma_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons,
      navierBKMAnalyticReductionNode_checked⟩

theorem currentNavierBKMAnalyticComponents_node :
    BKMVorticityStretchingEstimateClosed ∧
      BKMResidualCurlExpansionAlgebraClosed ∧
      BKMStandardVorticityGrowthEstimateClosed ∧
      BKMLogSobolevGrowthEstimateClosed ∧
      (BKMAnalyticComponentsClosed → BKMAnalyticContinuationLemma) ∧
      (BKMAnalyticComponentsClosed →
        ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) ∧
      navierBKMAnalyticComponentsNode.status = .checked := by
  exact
    ⟨BKMVorticityStretchingEstimateClosed_proved,
      BKMResidualCurlExpansionAlgebraClosed_proved,
      BKMStandardVorticityGrowthEstimateClosed_proved,
      BKMLogSobolevGrowthEstimateClosed_proved,
      BKMAnalyticComponentsClosed.implies_BKMAnalyticContinuationLemma,
      BKMAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons,
      navierBKMAnalyticComponentsNode_checked⟩

theorem currentNavierNonzeroSchwartzEnergyKernel_node
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν) :
    (∃ t x, S.velocity t x ≠ 0) ∧
      SchwartzEnergyIdentityKernel ν S.velocity S.pressure ∧
      SchwartzMomentumClosureKernel ν S.velocity S.pressure ∧
      SchwartzConcreteSolutionKernel ν S.velocity S.pressure ∧
      (∀ t, ∫ x, pressureEnergyPairing S.velocity S.pressure t x ∂volume = 0) ∧
      (∀ t, ∫ x, convectionEnergyPairing S.velocity t x ∂volume = 0) ∧
      CoordinateViscousEnergyPairingFormula S.velocity ∧
      (∀ t,
        HasDerivAt (normalizedKineticEnergy S.velocity)
          (-(coordinateEnergyDissipationRate S.velocity ν t)) t) ∧
      (∀ t,
        Integrable (kineticEnergyDensity S.velocity t) ∧
          HasDerivAt (normalizedKineticEnergy S.velocity)
            (-(coordinateEnergyDissipationRate S.velocity ν t)) t) ∧
      (∀ t x,
        timeVelocityDerivative S.velocity t x + spatialConvection S.velocity t x +
            spatialPressureGradient S.pressure t x =
          ν • spatialLaplacian S.velocity t x) ∧
      (∀ t x, spatialDivergence S.velocity t x = 0) ∧
      pressureGradientVelocityField S.pressure = momentumPressureResidual ν S.velocity ∧
      (∀ t x, spatialVorticity (momentumPressureResidual ν S.velocity) t x = 0) ∧
      navierNonzeroSchwartzEnergyKernelNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  rcases S.nonzero_energyMomentumCanary_packet with
    ⟨hnonzero, henergy, hmomentum, hconcrete, hpressureCancel, hconvectionCancel,
      hviscous, hcoordinate, hmeaningful, heq, hdiv, hresidual, hvort⟩
  exact
    ⟨hnonzero, henergy, hmomentum, hconcrete, hpressureCancel, hconvectionCancel,
      hviscous, hcoordinate, hmeaningful, heq, hdiv, hresidual, hvort,
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

theorem currentNavierNonzeroSchwartzLocalizedNilpotentStreamObstruction_node :
    (∃ u₀ : NSSchwartzDivergenceFreeInitialVelocity,
      ∃ x : NSSpace, u₀.1 x ≠ 0) ∧
      streamFunctionVelocity nsLocalizedNilpotentStreamFunction
          nsLocalizedNilpotentStreamWitnessPoint =
        EuclideanSpace.single nsCoord1 (nsUnitBumpScalar.rIn / 2) ∧
      spatialVorticity
          (momentumPressureResidual 0 localizedNilpotentStreamVelocityField) 0 0 =
        EuclideanSpace.single nsCoord1 (-1 : ℝ) ∧
      spatialVorticity
          (momentumPressureResidual 0 localizedNilpotentStreamVelocityField) 0 0 ≠
        0 ∧
      (¬ ∃ p : NSPressureField,
        smoothSpaceTimePressure p ∧
          ∀ t x,
            timeVelocityDerivative localizedNilpotentStreamVelocityField t x +
                spatialConvection localizedNilpotentStreamVelocityField t x +
                spatialPressureGradient p t x =
              (0 : ℝ) • spatialLaplacian localizedNilpotentStreamVelocityField t x) ∧
      (∀ {u : NSVelocityField} {t : NSTime},
        ((fun x : NSSpace => u t x) =ᶠ[𝓝 (0 : NSSpace)]
          fun x : NSSpace => localizedNilpotentStreamVelocityField 0 x) →
        ((fun x : NSSpace => timeVelocityDerivative u t x) =ᶠ[𝓝 (0 : NSSpace)]
          fun _ : NSSpace => 0) →
        spatialVorticity (momentumPressureResidual 0 u) t 0 =
          EuclideanSpace.single nsCoord1 (-1 : ℝ)) ∧
      (∀ {u : NSVelocityField} {t : NSTime},
        ((fun x : NSSpace => u t x) =ᶠ[𝓝 (0 : NSSpace)]
          fun x : NSSpace => localizedNilpotentStreamVelocityField 0 x) →
        ((fun x : NSSpace => timeVelocityDerivative u t x) =ᶠ[𝓝 (0 : NSSpace)]
          fun _ : NSSpace => 0) →
        ¬ ∃ p : NSPressureField,
          smoothSpaceTimePressure p ∧
            ∀ s x,
              timeVelocityDerivative u s x + spatialConvection u s x +
                  spatialPressureGradient p s x =
                (0 : ℝ) • spatialLaplacian u s x) ∧
      (∀ t : NSTime,
        ¬ ∃ S : SchwartzConcreteNavierStokesSolution 0,
          ((fun x : NSSpace => S.velocity t x) =ᶠ[𝓝 (0 : NSSpace)]
            fun x : NSSpace => localizedNilpotentStreamVelocityField 0 x) ∧
            ((fun x : NSSpace => timeVelocityDerivative S.velocity t x) =ᶠ[𝓝 (0 : NSSpace)]
              fun _ : NSSpace => 0)) ∧
      (∀ t : NSTime,
        ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution 0,
          ((fun x : NSSpace => S.velocity t x) =ᶠ[𝓝 (0 : NSSpace)]
            fun x : NSSpace => localizedNilpotentStreamVelocityField 0 x) ∧
            ((fun x : NSSpace => timeVelocityDerivative S.velocity t x) =ᶠ[𝓝 (0 : NSSpace)]
              fun _ : NSSpace => 0)) ∧
      navierNonzeroSchwartzLocalizedNilpotentStreamObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨⟨nsLocalizedNilpotentStreamDivergenceFreeInitialVelocity,
        nsLocalizedNilpotentStreamDivergenceFreeInitialVelocity_nonzero⟩,
      streamFunctionVelocity_nsLocalizedNilpotent_witness_value,
      spatialVorticity_momentumPressureResidual_zero_localizedNilpotentStreamVelocityField_origin,
      spatialVorticity_momentumPressureResidual_zero_localizedNilpotentStreamVelocityField_origin_ne_zero,
      not_exists_smoothPressure_momentumEquation_zero_localizedNilpotentStreamVelocityField,
      fun {_u} {_t} hvel htime =>
        spatialVorticity_momentumPressureResidual_zero_of_localizedNilpotentStreamVelocityField_germ_origin
          hvel htime,
      fun {_u} {_t} hvel htime =>
        not_exists_smoothPressure_momentumEquation_zero_of_localizedNilpotentStreamVelocityField_germ_origin
          hvel htime,
      not_exists_schwartzConcreteSolution_localizedNilpotentStreamVelocityField_germ_stationary_at,
      not_exists_nonzeroSchwartzConcreteSolution_localizedNilpotentStreamVelocityField_germ_stationary_at,
      navierNonzeroSchwartzLocalizedNilpotentStreamObstructionNode_checked,
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
      (∀ {ν : ℝ}, 0 < ν →
        ∀ (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
          (a b : NSTime → ℝ),
          S.velocity =
              twoModeSchwartzVelocity a b
                nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile →
            ∃ t₀ t₁ : NSTime, a t₀ - b t₀ ≠ a t₁ - b t₁) ∧
      (∀ {ν : ℝ}, 0 < ν →
        ∀ (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
          (a b : NSTime → ℝ),
          S.velocity =
              twoModeSchwartzVelocity a b
                nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile →
            ∃ T xT,
              S.velocity T xT ≠ 0 ∧
                ∀ {s t : NSTime}, s < t → t ≤ T →
                  (a t - b t) ^ (2 : ℕ) < (a s - b s) ^ (2 : ℕ)) ∧
      (∀ {ν : ℝ}, 0 < ν →
        ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
          ∃ (a b : NSTime → ℝ),
            S.velocity =
              twoModeSchwartzVelocity a b
                nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile ∧
              ∃ s t T : NSTime,
                s < t ∧ t ≤ T ∧
                  (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
                    (a s - b s) ^ (2 : ℕ) ≤ (a t - b t) ^ (2 : ℕ)) ∧
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
      fun hν S a b hS =>
        nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_forces_amplitudeDifference_nonconstant
          hν S a b hS,
      fun hν S a b hS =>
        nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_exists_nonzero_endpoint_with_amplitudeDifference_sq_strict_drop
          hν S a b hS,
      fun hν =>
        not_exists_nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_amplitudeDifference_sq_nondecrease_before_nonzero_endpoint_of_pos_viscosity
          hν,
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
      (∀ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∀ t₀ t₁ x₀,
          S.velocity t₀ x₀ ≠ 0 →
            t₀ < t₁ →
              ¬ ∀ x : NSSpace, S.velocity t₁ x = S.velocity t₀ x) ∧
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
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ t₀ t₁ : NSTime,
          t₀ < t₁ ∧
            (∃ x₀ : NSSpace, S.velocity t₀ x₀ ≠ 0) ∧
              ∀ x : NSSpace, S.velocity t₁ x = S.velocity t₀ x) ∧
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
      fun S t₀ t₁ x₀ hne ht =>
        S.not_velocity_slice_eq_after_nonzero_of_pos_viscosity
          hν hne ht,
      not_exists_nonzeroSchwartzConcreteSolution_energy_periodic_of_pos_viscosity
        hν,
      not_exists_nonzeroSchwartzConcreteSolution_velocity_periodic_of_pos_viscosity
        hν,
      not_exists_nonzeroSchwartzConcreteSolution_repeated_velocity_slice_after_nonzero_of_pos_viscosity
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

theorem currentNavierSchwartzPressureClosureCertificate_node
    {ν : ℝ} {u : NSVelocityField}
    (C : PressureClosureObstructionCertificate ν u) :
    (∃ t : NSTime, ∃ x : NSSpace,
      spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) ∧
      (¬ ∃ p : NSPressureField,
        smoothSpaceTimePressure p ∧
          ∀ t x,
            timeVelocityDerivative u t x + spatialConvection u t x +
                spatialPressureGradient p t x =
              ν • spatialLaplacian u t x) ∧
      (∀ p : NSPressureField, ¬ SchwartzMomentumClosureKernel ν u p) ∧
      (∀ p : NSPressureField, ¬ SchwartzConcreteSolutionKernel ν u p) ∧
      (¬ ∃ S : SchwartzConcreteNavierStokesSolution ν, S.velocity = u) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν, S.velocity = u) ∧
      Nonempty (PressureClosureObstructionCertificate 0 localizedNilpotentStreamVelocityField) ∧
      (¬ ∃ p : NSPressureField,
        SchwartzMomentumClosureKernel 0 localizedNilpotentStreamVelocityField p) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution 0,
        S.velocity = localizedNilpotentStreamVelocityField) ∧
      navierSchwartzPressureClosureCertificateNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨C.residualVorticity_witness,
      C.noSmoothPressure_momentumEquation,
      fun p => C.incompatible_momentumClosureKernel,
      fun p => C.incompatible_concreteSolutionKernel,
      C.noSchwartzConcreteSolution_velocity,
      C.noNonzeroSchwartzConcreteSolution_velocity,
      ⟨localizedNilpotentStreamPressureClosureObstructionCertificate⟩,
      not_exists_localizedNilpotentStream_momentumClosureKernel,
      not_exists_nonzeroSchwartzConcreteSolution_velocity_localizedNilpotentStream_of_pressureClosureCertificate,
      navierSchwartzPressureClosureCertificateNode_checked,
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

theorem currentNavierNonzeroSchwartzFiniteModeInviscidCanaryBoundary_node
    {ν : ℝ} (f g : NSSchwartzInitialVelocity)
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∃ S : NonzeroSchwartzConcreteNavierStokesSolution 0,
      S.velocity =
          twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
        S.pressure = (0 : NSPressureField) ∧
        SchwartzConcreteSolutionKernel 0 S.velocity S.pressure) ∧
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
  rcases
      oneOneTwoModeSchwartzVelocity_inviscidZeroPressureCanary_and_residualCurlBoundary
        (ν := ν) f g hfg hfDiv hgDiv hclosure with
    ⟨hcanary, hordinaryNoGo, hnonzeroNoGo⟩
  rcases hcanary with
    ⟨S, hvelocity, hpressure, _hnonzero, _henergy, hconcrete, _hpressureCancel,
      _hconvectionCancel, _hviscous, _hderiv, _hmeaningful⟩
  exact
    ⟨⟨S, hvelocity, hpressure, hconcrete⟩,
      hordinaryNoGo,
      hnonzeroNoGo,
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
      (∃ S : NonzeroSchwartzConcreteNavierStokesSolution 0,
        S.velocity = timeIndependentVelocity (u₀.1 : NSInitialVelocity) ∧
          S.pressure = (fun _ : NSTime => fun y : NSSpace => q y) ∧
          (∃ t x, S.velocity t x ≠ 0) ∧
          SchwartzEnergyIdentityKernel 0 S.velocity S.pressure ∧
          SchwartzConcreteSolutionKernel 0 S.velocity S.pressure ∧
          (∀ t, ∫ x, pressureEnergyPairing S.velocity S.pressure t x ∂volume = 0) ∧
          (∀ t, ∫ x, convectionEnergyPairing S.velocity t x ∂volume = 0) ∧
          CoordinateViscousEnergyPairingFormula S.velocity ∧
          (∀ t, HasDerivAt (normalizedKineticEnergy S.velocity) 0 t) ∧
          (∀ t,
            Integrable (kineticEnergyDensity S.velocity t) ∧
              HasDerivAt (normalizedKineticEnergy S.velocity) 0 t)) ∧
      (∃ t x, timeIndependentVelocity (u₀.1 : NSInitialVelocity) t x ≠ 0) ∧
      navierNonzeroSchwartzStationaryInviscidConstructorNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  let S :=
    stationaryInviscidSchwartzPressureSlice_nonzeroSchwartzConcreteSolution
      u₀ q hnonzero hstationary
  exact
    ⟨⟨S, rfl, rfl, S.concreteSolutionKernel⟩,
      stationaryInviscidSchwartzPressureSlice_nonzero_energyIdentityCanary_packet
        u₀ q hnonzero hstationary,
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
      SchwartzNonzeroTimeSupportKernel ν S.velocity S.pressure ∧
      (∃ t : NSTime,
        0 < coordinateEnergyDissipationRate S.velocity ν t ∧
          HasDerivAt (normalizedKineticEnergy S.velocity)
            (-(coordinateEnergyDissipationRate S.velocity ν t)) t ∧
          -(coordinateEnergyDissipationRate S.velocity ν t) < 0) ∧
      (∃ T xT,
        S.velocity T xT ≠ 0 ∧
          ∀ {s t : NSTime}, s < t → t ≤ T →
            normalizedKineticEnergy S.velocity t <
              normalizedKineticEnergy S.velocity s) ∧
      (∃ T xT,
        S.velocity T xT ≠ 0 ∧
          ∀ {s t : NSTime}, s < t → t ≤ T →
            ¬ ∀ x : NSSpace, S.velocity t x = S.velocity s x) ∧
      (∀ {P : NSTime}, 0 < P →
        ¬ ∀ t : NSTime, ∀ x : NSSpace,
          S.velocity (t + P) x = S.velocity t x) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
          ∃ s t T : NSTime,
            s < t ∧ t ≤ T ∧
              (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
                normalizedKineticEnergy W.velocity s ≤
                  normalizedKineticEnergy W.velocity t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
          ∃ P : NSTime,
            0 < P ∧
              ∀ t : NSTime, ∀ x : NSSpace,
                W.velocity (t + P) x = W.velocity t x) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
          ∃ s t T : NSTime,
            s < t ∧ t ≤ T ∧
              (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
                ∀ x : NSSpace, W.velocity t x = W.velocity s x) ∧
      navierNonzeroSchwartzStokesKernelNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  rcases
      S.stokesFlow_exists_nonzero_endpoint_with_strict_past_energy_drop_packet
        hν hconv hpressure with
    ⟨hkernel, hsupport, T, xT, hneT, hstrictPast⟩
  have hnoRepeatPast :
      ∀ {s t : NSTime}, s < t → t ≤ T →
        ¬ ∀ x : NSSpace, S.velocity t x = S.velocity s x :=
    (S.stokesFlow_endpoint_noRepeatedVelocitySlice_packet
      hν hconv hpressure ⟨xT, hneT⟩).2.2
  exact
    ⟨hkernel,
      hsupport,
      S.exists_strict_coordinateEnergyDissipationIdentity_of_pos_viscosity hν,
      ⟨T, xT, hneT, hstrictPast⟩,
      ⟨T, xT, hneT, hnoRepeatPast⟩,
      fun {_P} hP =>
        S.stokesFlow_not_forall_velocity_periodic_of_pos_viscosity
          hν hconv hpressure hP,
      not_exists_nonzeroSchwartzStokesFlow_energy_nondecrease_before_nonzero_endpoint_of_pos_viscosity
        hν,
      not_exists_nonzeroSchwartzStokesFlow_velocity_periodic_of_pos_viscosity hν,
      not_exists_nonzeroSchwartzStokesFlow_repeated_velocity_slice_before_nonzero_endpoint_of_pos_viscosity
        hν,
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

theorem currentNavierNonzeroSchwartzOneProfileAmplitudeBoundary_node
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {a : NSTime → ℝ} (f : NSSchwartzInitialVelocity)
    (hvelocity : S.velocity = fun r y => a r • f y)
    {s t T : NSTime} (hst : s < t) (htT : t ≤ T)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    (0 < ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume) ∧
      ((a t) ^ (2 : ℕ) < (a s) ^ (2 : ℕ)) ∧
      (∃ T xT,
        S.velocity T xT ≠ 0 ∧
          ∀ {s t : NSTime}, s < t → t ≤ T →
            (a t) ^ (2 : ℕ) < (a s) ^ (2 : ℕ)) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ (b : NSTime → ℝ) (g : NSSchwartzInitialVelocity),
          W.velocity = (fun r y => b r • g y) ∧
            ∃ s t T : NSTime,
              s < t ∧ t ≤ T ∧
                (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
                  (b s) ^ (2 : ℕ) ≤ (b t) ^ (2 : ℕ)) ∧
      navierNonzeroSchwartzOneProfileAmplitudeBoundaryNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  have hfne : ∃ x : NSSpace, f x ≠ 0 := by
    rcases hneT with ⟨xT, hxT⟩
    refine ⟨xT, ?_⟩
    intro hfx
    have hzero : S.velocity T xT = 0 := by
      rw [hvelocity]
      simp [hfx]
    exact hxT hzero
  exact
    ⟨integral_norm_sq_pos_of_schwartz_ne_zero f hfne,
      S.scalarProfile_amplitude_sq_strict_lt_before_nonzero_endpoint_of_pos_viscosity
        hν f hvelocity hst htT hneT,
      S.exists_nonzero_endpoint_with_scalarProfile_amplitude_sq_strict_drop
        hν f hvelocity,
      not_exists_nonzeroSchwartzConcreteSolution_scalarProfile_amplitude_sq_nondecrease_before_nonzero_endpoint_of_pos_viscosity
        hν,
      navierNonzeroSchwartzOneProfileAmplitudeBoundaryNode_checked,
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
      (∃ t : NSTime,
        t ≤ T ∧
          (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
            0 < coordinateEnergyDissipationRate S.velocity ν t ∧
              coordinateEnergyDissipationRate S.velocity ν t <
                κ * normalizedKineticEnergy S.velocity t) ∧
      (∃ t : NSTime,
        t ≤ T ∧
          (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
            0 < coordinateEnergyDissipationRate S.velocity ν t ∧
              0 < normalizedKineticEnergy S.velocity t ∧
                0 <
                  coordinateEnergyDissipationRate S.velocity ν t /
                    normalizedKineticEnergy S.velocity t ∧
                  coordinateEnergyDissipationRate S.velocity ν t /
                      normalizedKineticEnergy S.velocity t < κ) ∧
      (¬ ∀ t : NSTime, t ≤ T →
        κ * normalizedKineticEnergy S.velocity t ≤
          coordinateEnstrophyAt S.velocity t) ∧
      (∃ t : NSTime,
        t ≤ T ∧
          (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
            0 < coordinateEnstrophyAt S.velocity t ∧
              0 < normalizedKineticEnergy S.velocity t ∧
                0 <
                  coordinateEnstrophyAt S.velocity t /
                    normalizedKineticEnergy S.velocity t ∧
                  coordinateEnstrophyAt S.velocity t /
                      normalizedKineticEnergy S.velocity t < κ) ∧
      NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      (∃ T xT,
        S.velocity T xT ≠ 0 ∧
          ∀ κ : NSTime, 0 < κ →
            ∃ t : NSTime,
              t ≤ T ∧
                (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                  0 < coordinateEnergyDissipationRate S.velocity ν t ∧
                    coordinateEnergyDissipationRate S.velocity ν t < κ) ∧
      (∃ T xT,
        S.velocity T xT ≠ 0 ∧
          ∀ κ : NSTime, 0 < κ →
            ∃ t : NSTime,
              t ≤ T ∧
                (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                  0 < coordinateEnergyDissipationRate S.velocity ν t ∧
                    coordinateEnergyDissipationRate S.velocity ν t <
                      κ * normalizedKineticEnergy S.velocity t) ∧
      (NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
        ∃ T xT,
          S.velocity T xT ≠ 0 ∧
            ∀ κ : NSTime, 0 < κ →
              ∃ t : NSTime,
                t ≤ T ∧
                  (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                    0 < coordinateEnergyDissipationRate S.velocity ν t ∧
                      0 < normalizedKineticEnergy S.velocity t ∧
                        0 <
                          coordinateEnergyDissipationRate S.velocity ν t /
                            normalizedKineticEnergy S.velocity t ∧
                          coordinateEnergyDissipationRate S.velocity ν t /
                              normalizedKineticEnergy S.velocity t < κ) ∧
      (∃ T xT,
        S.velocity T xT ≠ 0 ∧
          ∀ κ : NSTime, 0 < κ →
            ∃ t : NSTime,
              t ≤ T ∧
                (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                  0 < coordinateEnergyDissipationRate S.velocity ν t ∧
                    0 < normalizedKineticEnergy S.velocity t ∧
                      0 <
                        coordinateEnergyDissipationRate S.velocity ν t /
                          normalizedKineticEnergy S.velocity t ∧
                        coordinateEnergyDissipationRate S.velocity ν t /
                          normalizedKineticEnergy S.velocity t < κ) ∧
      (NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
        ∃ T xT,
          S.velocity T xT ≠ 0 ∧
            ∀ κ : NSTime, 0 < κ →
              ∃ t : NSTime,
                t ≤ T ∧
                  (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                    0 < coordinateEnstrophyAt S.velocity t ∧
                      0 < normalizedKineticEnergy S.velocity t ∧
                        0 <
                          coordinateEnstrophyAt S.velocity t /
                            normalizedKineticEnergy S.velocity t ∧
                          coordinateEnstrophyAt S.velocity t /
                              normalizedKineticEnergy S.velocity t < κ) ∧
      (NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
        SchwartzNonzeroTimeSupportKernel ν S.velocity S.pressure ∧
        (∀ {s t : NSTime}, s < t → t ≤ T →
          normalizedKineticEnergy S.velocity t <
            normalizedKineticEnergy S.velocity s) ∧
        ∀ lam : NSTime, 0 < lam →
          ∃ t : NSTime,
            t ≤ T ∧
              (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                0 < coordinateEnstrophyAt S.velocity t ∧
                  0 < normalizedKineticEnergy S.velocity t ∧
                    0 <
                      coordinateEnstrophyAt S.velocity t /
                        normalizedKineticEnergy S.velocity t ∧
                      coordinateEnstrophyAt S.velocity t /
                          normalizedKineticEnergy S.velocity t < lam) ∧
      (NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
        (¬ ∀ t : NSTime, t ≤ T →
          κ * normalizedKineticEnergy S.velocity t ≤
            coordinateEnergyDissipationRate S.velocity ν t) ∧
        (¬ ∀ t : NSTime, t ≤ T →
          κ * normalizedKineticEnergy S.velocity t ≤
            coordinateEnstrophyAt S.velocity t) ∧
        (¬ ∀ t : NSTime, t ≤ T →
          κ ≤
            coordinateEnstrophyAt S.velocity t /
              normalizedKineticEnergy S.velocity t) ∧
        ∃ t : NSTime,
          t ≤ T ∧
            (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
              0 < coordinateEnstrophyAt S.velocity t ∧
                0 < normalizedKineticEnergy S.velocity t ∧
                  0 <
                    coordinateEnstrophyAt S.velocity t /
                      normalizedKineticEnergy S.velocity t ∧
                    coordinateEnstrophyAt S.velocity t /
                        normalizedKineticEnergy S.velocity t < κ) ∧
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
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ T : NSTime,
          (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
            ∀ t : NSTime, t ≤ T →
              κ ≤
                coordinateEnergyDissipationRate W.velocity ν t /
                  normalizedKineticEnergy W.velocity t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ T : NSTime,
          (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
            ∀ t : NSTime, t ≤ T →
              κ * normalizedKineticEnergy W.velocity t ≤
                coordinateEnstrophyAt W.velocity t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ T : NSTime,
          (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
            ∀ t : NSTime, t ≤ T →
              κ ≤
                coordinateEnstrophyAt W.velocity t /
                  normalizedKineticEnergy W.velocity t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
            ∃ T : NSTime,
              (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
                ∀ t : NSTime, t ≤ T →
                  κ * normalizedKineticEnergy W.velocity t ≤
                    coordinateEnstrophyAt W.velocity t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
            ∃ T : NSTime,
              (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
                ∀ t : NSTime, t ≤ T →
                  κ ≤
                    coordinateEnstrophyAt W.velocity t /
                      normalizedKineticEnergy W.velocity t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
            ∃ T : NSTime,
              (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
                ∀ t : NSTime, t ≤ T →
                  coordinateEnstrophyAt W.velocity t =
                    κ * normalizedKineticEnergy W.velocity t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
            ∃ T : NSTime,
              (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
                ∀ t : NSTime, t ≤ T →
                  coordinateEnstrophyAt W.velocity t /
                    normalizedKineticEnergy W.velocity t = κ) ∧
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
      S.toSchwartzConcreteNavierStokesSolution
        |>.exists_past_nonzero_with_small_positive_dissipation_per_energy
          hν hneT hκ,
      S.toSchwartzConcreteNavierStokesSolution
        |>.exists_past_nonzero_with_small_positive_dissipation_ratio
          hν hneT hκ,
      S.toSchwartzConcreteNavierStokesSolution
        |>.not_forall_past_coordinateEnstrophyAt_ge_mul_normalizedKineticEnergy
          hν hκ hneT,
      S.toSchwartzConcreteNavierStokesSolution
        |>.exists_past_nonzero_with_small_positive_coordinateEnstrophy_ratio
          hν hneT hκ,
      hstokes,
      hsmallPacket,
      S.exists_nonzero_endpoint_with_arbitrarily_small_past_dissipation_per_energy hν,
      S.stokesFlow_smallPastDissipationRatio_packet hν hconv hpressure,
      S.exists_nonzero_endpoint_with_arbitrarily_small_past_dissipation_ratio hν,
      S.stokesFlow_smallPastCoordinateEnstrophyRatio_packet hν hconv hpressure,
      S.stokesFlow_endpointStrictEnergy_and_smallPastCoordinateEnstrophyRatio_packet
        hν hconv hpressure hneT,
      S.stokesFlow_positiveViscosity_profileGapObstruction_packet
        hν hconv hpressure hκ hneT,
      not_exists_nonzeroSchwartzConcreteSolution_uniform_past_dissipation_gap hκ,
      not_exists_nonzeroSchwartzConcreteSolution_past_spectral_floor hν.le hκ,
      not_exists_nonzeroSchwartzConcreteSolution_past_dissipation_ratio_floor hν hκ,
      not_exists_nonzeroSchwartzConcreteSolution_past_coordinateEnstrophy_floor hν hκ,
      not_exists_nonzeroSchwartzConcreteSolution_past_coordinateEnstrophy_ratio_floor hν hκ,
      not_exists_nonzeroSchwartzStokesFlow_past_coordinateEnstrophy_floor_of_posViscosity
        hν hκ,
      not_exists_nonzeroSchwartzStokesFlow_past_coordinateEnstrophy_ratio_floor_of_posViscosity
        hν hκ,
      not_exists_nonzeroSchwartzStokesFlow_past_exact_coordinateEnstrophyRayleigh_of_posViscosity
        hν hκ,
      not_exists_nonzeroSchwartzStokesFlow_past_exact_coordinateEnstrophyRatioRayleigh_of_posViscosity
        hν hκ,
      navierNonzeroSchwartzNoUniformPastDissipationNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzStokesFiniteProfileRayleighObstruction_node
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {T : NSTime} (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      SchwartzNonzeroTimeSupportKernel ν S.velocity S.pressure ∧
      (∀ {s t : NSTime}, s < t → t ≤ T →
        normalizedKineticEnergy S.velocity t <
          normalizedKineticEnergy S.velocity s) ∧
      (∀ lam : ℝ, 0 < lam →
        ¬ ∀ t : NSTime, t ≤ T →
          lam ≤
            coordinateEnstrophyAt S.velocity t /
              normalizedKineticEnergy S.velocity t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ _ : StokesFiniteProfileRayleighFloorCertificate W, True) ∧
      navierNonzeroSchwartzStokesFiniteProfileRayleighObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  rcases S.stokesFlow_finiteProfileRayleighFloorBoundary_packet
      hν hconv hpressure hneT with
    ⟨hstokes, hsupport, hstrict, hnoFloor, _hsmall⟩
  exact
    ⟨hstokes, hsupport, hstrict, hnoFloor,
      not_exists_nonzeroSchwartzStokesFlow_finiteProfileRayleighFloorCertificate hν,
      navierNonzeroSchwartzStokesFiniteProfileRayleighObstructionNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzExactRayleighObstruction_node
    {ν κ : ℝ} (hν : 0 < ν) (hκ : 0 < κ) :
    (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ T : NSTime,
        (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
          ∀ t : NSTime, t ≤ T →
            coordinateEnstrophyAt W.velocity t =
              κ * normalizedKineticEnergy W.velocity t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ T : NSTime,
          (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
            ∀ t : NSTime, t ≤ T →
              coordinateEnstrophyAt W.velocity t /
                normalizedKineticEnergy W.velocity t = κ) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) (T : NSTime),
          W.velocity = (fun r y => a r • f y) ∧
            (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
              ∀ t : NSTime, t ≤ T →
                coordinateEnstrophyAt (fun r y => a r • f y) t =
                  κ * normalizedKineticEnergy (fun r y => a r • f y) t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) (T : NSTime),
          W.velocity = (fun r y => a r • f y) ∧
            (∃ xT : NSSpace, W.velocity T xT ≠ 0) ∧
              ∀ t : NSTime, t ≤ T →
                coordinateEnstrophyAt (fun r y => a r • f y) t /
                    normalizedKineticEnergy (fun r y => a r • f y) t =
                  κ) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity),
          W.velocity = fun r y => a r • f y) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
            ∃ (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity),
              W.velocity = fun r y => a r • f y) ∧
      navierNonzeroSchwartzNoUniformPastDissipationNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact
    ⟨not_exists_nonzeroSchwartzConcreteSolution_past_exact_coordinateEnstrophyRayleigh_of_posViscosity
        hν hκ,
      not_exists_nonzeroSchwartzConcreteSolution_past_exact_coordinateEnstrophyRatioRayleigh_of_posViscosity
        hν hκ,
      not_exists_nonzeroSchwartzConcreteSolution_oneProfile_past_exact_coordinateEnstrophyRayleigh_of_posViscosity
        hν hκ,
      not_exists_nonzeroSchwartzConcreteSolution_oneProfile_past_exact_coordinateEnstrophyRatioRayleigh_of_posViscosity
        hν hκ,
      not_exists_nonzeroSchwartzConcreteSolution_oneProfile_of_posViscosity hν,
      not_exists_nonzeroSchwartzStokesFlow_oneProfile_of_posViscosity hν,
      navierNonzeroSchwartzNoUniformPastDissipationNode_checked,
      navierNonzeroSchwartzCanaryNode_open⟩

theorem currentNavierNonzeroSchwartzNoUniformFutureDissipation_node
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {κ T : NSTime} (hκ : 0 < κ) :
    (¬ ∀ t : NSTime, T ≤ t →
      κ ≤ coordinateEnergyDissipationRate S.velocity ν t) ∧
      (∃ t : NSTime,
        T ≤ t ∧ coordinateEnergyDissipationRate S.velocity ν t < κ) ∧
      NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      (∃ t : NSTime,
        T ≤ t ∧ coordinateEnergyDissipationRate S.velocity ν t < κ) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        ∃ T : NSTime,
          ∀ t : NSTime, T ≤ t →
            κ ≤ coordinateEnergyDissipationRate W.velocity ν t) ∧
      (¬ ∃ W : NonzeroSchwartzConcreteNavierStokesSolution ν,
        (∀ t x, spatialConvection W.velocity t x = 0) ∧
          (∀ t x, spatialPressureGradient W.pressure t x = 0) ∧
            ∃ T : NSTime,
              ∀ t : NSTime, T ≤ t →
                κ ≤ coordinateEnergyDissipationRate W.velocity ν t) ∧
      navierNonzeroSchwartzNoUniformPastDissipationNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  rcases S.stokesFlow_noUniformFutureDissipation_packet hconv hpressure hκ with
    ⟨hstokes, hfutureStokes⟩
  exact
    ⟨S.toSchwartzConcreteNavierStokesSolution
        |>.not_forall_future_coordinateEnergyDissipationRate_ge hκ,
      S.toSchwartzConcreteNavierStokesSolution
        |>.exists_future_coordinateEnergyDissipationRate_lt hκ,
      hstokes,
      hfutureStokes,
      not_exists_nonzeroSchwartzConcreteSolution_uniform_future_dissipation_gap hκ,
      not_exists_nonzeroSchwartzStokesFlow_uniform_future_dissipation_gap hκ,
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
