import Mettapedia.FluidDynamics.NavierStokes.ProofState

/-!
# Navier-Stokes roadmap

This module records the checked route order for the current Navier-Stokes lane.
It is a roadmap for honest proof-state movement, not a Millennium problem result.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Roadmap stage tags for the current Navier-Stokes lane. -/
inductive NavierRoadmapStage where
  | sourceMap
  | liveRegressionSplit
  | finiteEnergyRepair
  | placeholderRetirement
  | deGroundedSurface
  | energyIdentity
  | bkmContinuation
  | nonzeroEnergyKernel
  | scalingGate
  | averagedEquationGate
  | replacementRoute
deriving DecidableEq, Repr

/-- One checked roadmap entry, tied back to a proof-state node id. -/
structure NavierRoadmapEntry where
  stage : NavierRoadmapStage
  proofNodeId : String
  status : NavierProofStatus
  truthValue : SimpleTruthValue
  obligation : String
deriving Repr

/-- Current roadmap order for the active finite-energy/BKM route audit. -/
def currentNavierRoadmap : List NavierRoadmapEntry :=
  [ { stage := .sourceMap
      proofNodeId := "navier.live-surface"
      status := .surveyed
      truthValue := ⟨100, 94⟩
      obligation := "Keep the dependency map and split threshold current." },
    { stage := .liveRegressionSplit
      proofNodeId := "navier.live-surface"
      status := .checked
      truthValue := ⟨100, 94⟩
      obligation := "Keep regression archives outside the live entrypoint." },
    { stage := .finiteEnergyRepair
      proofNodeId := "navier.finite-energy-target"
      status := .checked
      truthValue := ⟨100, 91⟩
      obligation := "Preserve finite initial energy as an explicit target input." },
    { stage := .placeholderRetirement
      proofNodeId := "navier.fefferman-lift"
      status := .retiredPlaceholder
      truthValue := ⟨100, 99⟩
      obligation := "Treat the audited FeffermanPredicateKit global-clause family as missing-lift checklists only; they establish nothing about the concrete R^3 PDE." },
    { stage := .deGroundedSurface
      proofNodeId := "navier.de-grounded-zero-canary"
      status := .checked
      truthValue := ⟨100, 98⟩
      obligation := "Use the concrete zero-solution canary and scaling arithmetic as the baseline for future PDE-grounded route work." },
    { stage := .energyIdentity
      proofNodeId := "navier.energy.schwartz-solution-identity"
      status := .checked
      truthValue := ⟨78, 84⟩
      obligation := "Use the checked slice-Schwartz solution energy identity as the PDE-grounded energy subnode; next extend derivative-under-integral and decay hypotheses beyond the current energy-admissible class." },
    { stage := .bkmContinuation
      proofNodeId := "navier.bkm.vorticity-stretching"
      status := .checked
      truthValue := ⟨83, 88⟩
      obligation := "Use the checked pointwise BKM stretching estimates to control (omega . grad)u and its enstrophy-production scalar from gradient and vorticity envelopes. Remaining BKM work is the concrete vorticity equation, log-Sobolev/Biot-Savart gradient control, H^s/enstrophy differential inequality, and continuation closure." },
    { stage := .bkmContinuation
      proofNodeId := "navier.bkm.vorticity-residual-curl-equation"
      status := .checked
      truthValue := ⟨85, 88⟩
      obligation := "Use the checked finite-time witness residual-curl equation spatialVorticity(momentumPressureResidual nu u)=0 as the pressure-free vorticity-equation surface. Remaining BKM work factors the expansion through residualCurlExpansionDefect and then completes the log-Sobolev/high-norm continuation estimate." },
    { stage := .bkmContinuation
      proofNodeId := "navier.bkm.residual-curl-expansion-defect"
      status := .checked
      truthValue := ⟨87, 88⟩
      obligation := "Use the checked algebraic bridge from residual-curl zero plus residualCurlExpansionDefect = 0 to concreteVorticityEquationOn. The exact remaining vector-calculus target is BKMResidualCurlExpansionDefectVanishes for smooth incompressible velocities on the slab." },
    { stage := .bkmContinuation
      proofNodeId := "navier.bkm.residual-curl-differential-identities"
      status := .checked
      truthValue := ⟨88, 88⟩
      obligation := "Use BKMResidualCurlDifferentialIdentitiesClosed_of_commutationExpansion: the remaining decomposed residual-curl target is BKMResidualCurlCommutationExpansionClosed, i.e. curl/time commutation, curl/Laplacian commutation, and the incompressible curl-convection identity." },
    { stage := .bkmContinuation
      proofNodeId := "navier.bkm.standard-vorticity-growth"
      status := .checked
      truthValue := ⟨86, 88⟩
      obligation := "Once concreteVorticityEquationOn is derived, use the checked material-minus-diffusion growth estimates, pointwise derivative d/dt (1/2 |omega|^2) = omega dot partial_t omega, transport algebra omega dot ((u.grad)omega) = (u.grad)(1/2 |omega|^2), Schwartz-slice transport cancellation from incompressibility, coordinate vorticity diffusion dissipation, Schwartz-slice Laplacian IBP, the witness-level Schwartz-slice a-priori enstrophy estimate, standard-equation-to-raw-enstrophy pairing algebra, and conditional dE/dt <= ||grad u||_inf E enstrophy-growth estimate. Remaining enstrophy work is lifting the pointwise time derivative through the spatial integral and instantiating or extending the Schwartz-slice transport/diffusion identities for finite-energy witnesses." },
    { stage := .bkmContinuation
      proofNodeId := "navier.bkm.log-sobolev-gradient-control"
      status := .checked
      truthValue := ⟨87, 88⟩
      obligation := "Once the analytic log-Sobolev/Biot-Savart gradient-control hypothesis is proved, use the checked logarithmic gradient envelope to feed the standard-vorticity growth, enstrophy-production, and dE/dt <= C * (1 + Omega log(exp(1) + H)) * E bounds. This does not itself prove the analytic gradient estimate." },
    { stage := .bkmContinuation
      proofNodeId := "navier.bkm.single-analytic-lemma"
      status := .checked
      truthValue := ⟨86, 88⟩
      obligation := "The repaired nonnegative-horizon BKM target is reduced to BKMAnalyticContinuationLemma, whose statement is the remaining analytic proof obligation: positive-viscosity smooth divergence-free finite-energy data plus a finite-time witness with residual-curl vorticity equation and integrable vorticity envelope extend to the global output after proving residual-curl expansion, the remaining vorticity-enstrophy integral identities, log-Sobolev gradient control, and high-norm continuation." },
    { stage := .bkmContinuation
      proofNodeId := "navier.bkm.analytic-components"
      status := .checked
      truthValue := ⟨87, 88⟩
      obligation := "Use BKMAnalyticContinuationLemma_of_components and BKMContinuation_reduced_to_analytic_components with the checked pointwise density derivative, vorticity raw-balance, transport-cancellation algebra plus Schwartz-slice transport cancellation, enstrophy-control, and gradient-growth packages. Remaining component targets are residual-curl expansion defect vanishing, the finite-energy vorticity-enstrophy integral identities, log-Sobolev/Biot-Savart gradient control from BKM envelope data, and high-norm continuation/Gronwall closure." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-kernel"
      status := .checked
      truthValue := ⟨79, 88⟩
      obligation := "Use the checked nonzero-preserving energy/momentum packet for finite-mode generator work: it exposes the nonzero witness, pressure and convection cancellations, viscous identity, meaningful energy identity, literal momentum equation, incompressibility, pressure-residual equality, residual-curl-zero gate, and a whole-time zero-pressure two-profile canary at viscosity 0 whenever the inviscid closure is supplied. Keep the positive-viscosity nonzero pressure-slice closure as the open canary obligation." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-line-invariant-obstruction"
      status := .checked
      truthValue := ⟨85, 90⟩
      obligation := "Use the checked line-invariant obstruction to rule out shear shortcuts; future nonzero canaries must break line invariance and close the pressure-slice momentum equation." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-heat-shear-boundary"
      status := .checked
      truthValue := ⟨90, 91⟩
      obligation := "Use the checked heat-shear boundary to separate the classical exact zero-pressure shear-flow solution from the whole-space slice-Schwartz canary lane; future nonzero canaries must avoid nondecaying time-zero slices as well as pressure-residual curl failures." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-rank-one-shear-obstruction"
      status := .checked
      truthValue := ⟨84, 89⟩
      obligation := "Use the checked solution-level rank-one zero-convection obstruction to rule out fixed-direction Schwartz Stokes-flow shortcuts at every slice; future nonzero canaries must close a genuinely non-rank-one pressure-slice equation." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-symmetric-shear-obstruction"
      status := .checked
      truthValue := ⟨88, 88⟩
      obligation := "Treat the exact nonzero symmetric finite-mode shear as an algebraic boundary canary only; its nonzero constant directional derivative excludes it from the Schwartz canary lane." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-nilpotent-shear-pressure-obstruction"
      status := .checked
      truthValue := ⟨91, 92⟩
      obligation := "Use the checked nilpotent-shear and frozen nilpotent-slice pressure-residual curl obstructions to reject multi-stage steady linear shear chains; future nonzero canaries must prove curl-free pressure residual closure after localization, not just divergence-free linear algebra." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-localized-stream-seed"
      status := .checked
      truthValue := ⟨72, 88⟩
      obligation := "Use the checked localized stream-function seed as the concrete nonzero divergence-free Schwartz input for the next pressure-slice closure search." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-localized-nilpotent-stream-obstruction"
      status := .checked
      truthValue := ⟨88, 91⟩
      obligation := "Use the checked localized nilpotent stream germ obstruction to reject stationary inviscid pressure-closure shortcuts for an inhabited nonzero divergence-free Schwartz datum, even when only the local velocity germ and vanishing instantaneous time-derivative germ are fixed; future canaries must use nonstationary time dependence or a different localized profile so the residual curl vanishes." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.schwartz-pressure-closure-certificate"
      status := .checked
      truthValue := ⟨90, 91⟩
      obligation := "Use the checked pressure-closure certificate API to make residual-curl failures generator-facing: the localized nilpotent stream certificate is an explicit nonzero divergence-free Schwartz failed-canary boundary, and future positive canaries must prove no such certificate exists before constructing pressure slices." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-antiprofile-canary-obstruction"
      status := .checked
      truthValue := ⟨84, 90⟩
      obligation := "Use the checked localized stream/anti-stream cancellation guardrail to reject profile-level nonzero closures whose reconstructed velocity is zero." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-antiprofile-amplitude-boundary"
      status := .checked
      truthValue := ⟨90, 91⟩
      obligation := "Use the checked anti-profile amplitude boundary to require unequal, time-varying, and endpoint-strictly-dropping amplitude differences before testing localized stream/anti-stream candidates against the pressure-slice momentum equation." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-stationary-dissipation-gate"
      status := .checked
      truthValue := ⟨89, 91⟩
      obligation := "Use the checked positive-viscosity stationary obstruction to reject time-independent nonzero slice-Schwartz canaries; future nonzero canaries must be genuinely time-dependent and close the pressure-slice momentum equation." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-strict-dissipation-kernel"
      status := .checked
      truthValue := ⟨88, 90⟩
      obligation := "Use the checked strict-dissipation kernel to ensure any positive-viscosity nonzero inhabitant has a witness time with positive corrected dissipation and strictly negative energy derivative; still require an explicit inhabitant or broader pressure-closure obstruction." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-no-flat-energy-obstruction"
      status := .checked
      truthValue := ⟨90, 90⟩
      obligation := "Use the checked flat-energy zero-rigidity theorem to reject positive-viscosity canaries with everywhere-zero normalized-energy derivative or constant normalized kinetic energy; future positive canaries must genuinely dissipate." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-local-extremum-obstruction"
      status := .checked
      truthValue := ⟨91, 90⟩
      obligation := "Use the checked local-extremum obstruction to reject positive-viscosity canaries whose nonzero witness occurs at a local minimum or maximum of normalized kinetic energy." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-pointwise-strict-derivative"
      status := .checked
      truthValue := ⟨92, 90⟩
      obligation := "Use the checked pointwise strict-derivative gate to require every positive-viscosity nonzero witness time to have strictly negative normalized kinetic-energy derivative." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-local-plateau-obstruction"
      status := .checked
      truthValue := ⟨92, 89⟩
      obligation := "Use the checked local-plateau obstruction to reject positive-viscosity canaries whose nonzero witness occurs at a locally constant normalized-energy time." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-immediate-right-drop"
      status := .checked
      truthValue := ⟨93, 89⟩
      obligation := "Use the checked immediate right-drop gate to require every positive-viscosity nonzero witness time to have normalized kinetic energy eventually strictly lower on the right." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-right-drop-sample"
      status := .checked
      truthValue := ⟨94, 89⟩
      obligation := "Use the checked sampled right-drop gate to require every positive-viscosity nonzero witness time to exhibit an actual lower-energy sample inside each positive right interval." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-strict-future-drop"
      status := .checked
      truthValue := ⟨95, 89⟩
      obligation := "Use the checked strict future-drop gate to require every later endpoint after a positive-viscosity nonzero witness time to have strictly lower normalized kinetic energy." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-no-energy-recurrence"
      status := .checked
      truthValue := ⟨96, 89⟩
      obligation := "Use the checked no-recurrence gate to reject positive-viscosity nonzero canaries with positive-period normalized-energy recurrence, periodic velocity, or a repeated nonzero velocity slice at a strictly later time." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.schwartz-pressure-residual-curl-gate"
      status := .checked
      truthValue := ⟨87, 89⟩
      obligation := "Use the checked pressure-residual curl gate to reject any candidate velocity whose residual νΔu - ∂tu - (u.grad)u has nonzero spatial vorticity; future positive canaries must prove the residual is curl-free before searching for pressure slices." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-finite-mode-residual-curl-boundary"
      status := .checked
      truthValue := ⟨91, 91⟩
      obligation := "Use the checked finite-mode route boundary: the inviscid zero-pressure two-profile closure gives a nonzero whole-time slice-Schwartz energy-identity canary at viscosity 0, and the same branch cannot be reused at viscosity ν when its viscous Laplacian residual has nonzero curl. Future positive-viscosity canaries must exhibit curl-free residual closure and explicit pressure slices." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-stationary-inviscid-constructor"
      status := .checked
      truthValue := ⟨78, 88⟩
      obligation := "Use the checked stationary inviscid energy-identity canary packet as the exact one-profile closure surface for localized Euler-style searches: at viscosity 0 it returns a nonzero concrete solution witness with exact velocity/pressure equalities, cancellation integrals, coordinate viscous formula, and zero-viscosity meaningful energy identity. Keep the positive-viscosity nonzero canary open." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-stokes-kernel"
      status := .checked
      truthValue := ⟨85, 89⟩
      obligation := "Use the checked Stokes-flow kernel to make zero-convection/zero-pressure-gradient canary attempts satisfy the exact Stokes equation, strict positive-viscosity dissipation, a nonzero endpoint with strictly ordered and nonrepeating past velocity slices, no nondecreasing energy subinterval before that endpoint, and no positive-period recurrence; still construct an inhabited bounded whole-real-time Schwartz Stokes flow or prove that subroute empty." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-stokes-rankone-obstruction"
      status := .checked
      truthValue := ⟨85, 88⟩
      obligation := "Use the checked Stokes rank-one obstruction to reject exact Stokes-flow candidates whose every slice stays in one fixed nonzero rank-one Schwartz direction; future Stokes canaries must be genuinely non-rank-one or prove the whole bounded eternal Stokes subroute empty." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-zero-restart-obstruction"
      status := .checked
      truthValue := ⟨84, 88⟩
      obligation := "Use the checked zero-restart kernel to reject candidate evolutions that pass from a zero velocity slice to a later nonzero slice at nonnegative viscosity, both in the general slice-Schwartz interface and in the Stokes subroute; future positive canaries must either stay nonzero on every earlier slice before a nonzero witness or prove the full pressure/time-evolution closure directly." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-past-dissipation-ray"
      status := .checked
      truthValue := ⟨86, 88⟩
      obligation := "Use the checked past-dissipation ray to require every positive-viscosity nonzero canary to expose a witness whose whole earlier half-line is nonzero somewhere, strictly dissipative, and strictly energy-dropping on forward subintervals; future Stokes/pressure-closure work must supply a real bounded eternal construction or a quantitative obstruction for that half-line." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-endpoint-support"
      status := .checked
      truthValue := ⟨88, 89⟩
      obligation := "Use the checked endpoint support kernel to test any candidate from each later nonzero endpoint: every earlier slice must be nonzero somewhere and every earlier forward subinterval must strictly lose normalized energy. A full bounded-eternal Stokes obstruction still needs a quantitative lower-bound or spectral-gap input." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-one-profile-amplitude-boundary"
      status := .checked
      truthValue := ⟨89, 89⟩
      obligation := "Use the checked one-profile amplitude boundary to reject positive-viscosity separable Schwartz candidates whose squared scalar amplitude is repeated or nondecreasing before a later nonzero endpoint; future canaries must be genuinely multi-profile/nonseparable or prove the full pressure/time-evolution closure directly." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-no-uniform-past-dissipation"
      status := .checked
      truthValue := ⟨97, 94⟩
      obligation := "Use the checked no-uniform-past/future-dissipation, no-past-spectral-floor, past dissipation-per-energy collapse, corrected-dissipation Rayleigh collapse, spatial Rayleigh collapse, exact Rayleigh-equality obstruction, one-profile exact Rayleigh/eigenmode obstruction, fixed-profile positive-viscosity emptiness theorem, fixed-profile Stokes emptiness theorem, Stokes profile-gap, endpoint strict-energy/low-Rayleigh, and exact Stokes Rayleigh-equality obstruction packets to reject bounded eternal positive-viscosity candidates certified by a uniform positive past or future dissipation gap, a positive Poincare/spectral floor of corrected dissipation or coordinate enstrophy over normalized energy, a positive whole-past Rayleigh-quotient floor, an endpoint ray avoiding arbitrarily small positive spatial Rayleigh samples, an exact positive whole-past spatial Rayleigh equality, a fixed-profile exact Rayleigh/eigenmode shortcut, or any nonzero scalar fixed-profile evolution. Future canary work must construct the exact nonzero evolution in a genuinely multi-profile/nonseparable class while allowing arbitrarily small past spatial Rayleigh-quotient samples before every nonzero endpoint and no uniform positive future dissipation floor, or prove a stronger structural emptiness theorem for the Stokes/pressure-closure class." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-stokes-finite-profile-rayleigh-obstruction"
      status := .checked
      truthValue := ⟨93, 92⟩
      obligation := "Use the checked finite-profile Stokes Rayleigh-floor obstruction to reject generator classes that try to certify a bounded eternal positive-viscosity exact Stokes canary by a positive whole-past spatial Rayleigh floor; future Stokes canaries must either evade every positive past Rayleigh floor with low-frequency slices, leave the exact Stokes subroute, or prove a stronger full Stokes/pressure-closure emptiness theorem." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-canary"
      status := .openGoal
      truthValue := ⟨84, 88⟩
      obligation := "Produce or refute an exact smooth positive-viscosity evolution and Schwartz pressure slices for the localized stream-function seed or a comparable non-polynomial Schwartz profile; seed-only data, conditional constructors, viscosity-0 finite-mode zero-pressure canaries, classical heat-shear exact solutions that fail Schwartz decay, rank-one zero-convection obstructions, nilpotent-shear pressure-residual obstructions, frozen nilpotent-slice obstructions, localized nilpotent stream stationary pressure-residual obstructions, profile-level nonzero anti-profile cancellation, anti-profile endpoint amplitude-boundary guardrails, anti-profile constant-difference obstructions, positive-viscosity stationary obstructions, strict-dissipation theorems conditional on the nonzero interface, flat-energy zero-rigidity obstructions, local-extremum energy obstructions, pointwise strict-derivative gates, local energy plateau obstructions, immediate right-drop gates, sampled right-drop gates, strict future-drop gates, energy-recurrence or repeated-slice obstructions, residual-curl pressure-closure rejections, finite-mode residual-curl boundaries, stationary inviscid closure constructors, conditional Stokes-flow kernels, Stokes rank-one obstructions, generalized zero-restart obstructions, past-dissipation ray theorems, endpoint support-order theorems, one-profile amplitude-boundary theorems, no-uniform-past-dissipation theorems, no-uniform-future-dissipation theorems, no-past-spectral-floor theorems, past dissipation-per-energy collapse theorems, past Rayleigh-quotient collapse theorems, spatial Rayleigh-quotient collapse theorems, general exact Rayleigh-equality obstructions, one-profile exact Rayleigh-equality obstructions, exact Stokes Rayleigh-equality obstructions, fixed-profile positive-viscosity emptiness theorems, fixed-profile Stokes emptiness theorem, finite-profile Stokes Rayleigh-floor obstruction, and algebraic finite-mode boundary cases do not count as the remaining positive-viscosity canary." },
    { stage := .scalingGate
      proofNodeId := "navier.regularity-promotion-gate"
      status := .scalingUncleared
      truthValue := ⟨0, 99⟩
      obligation := "Do not promote the finite-energy/BKM route while critical and supercritical gates fail." },
    { stage := .averagedEquationGate
      proofNodeId := "navier.averaged-equation-all-obstructions"
      status := .scalingUncleared
      truthValue := ⟨0, 99⟩
      obligation := "Replace the four missing averaged-equation witnesses before using averaged-equation evidence." },
    { stage := .replacementRoute
      proofNodeId := "navier.open-global-regularity-route"
      status := .openGoal
      truthValue := ⟨0, 99⟩
      obligation := "Start a replacement global route only after scaling, challenge-world, and averaged-equation checks clear." } ]

theorem currentNavierRoadmap_nonempty : currentNavierRoadmap ≠ [] := by
  simp [currentNavierRoadmap]

/-- The roadmap records the checked local BKM vorticity-stretching estimate and
keeps the global continuation criterion open. -/
theorem currentNavierRoadmap_records_bkm_vorticity_stretching :
    ({ stage := NavierRoadmapStage.bkmContinuation
       proofNodeId := "navier.bkm.vorticity-stretching"
       status := .checked
       truthValue := ⟨83, 88⟩
       obligation :=
        "Use the checked pointwise BKM stretching estimates to control (omega . grad)u and its enstrophy-production scalar from gradient and vorticity envelopes. Remaining BKM work is the concrete vorticity equation, log-Sobolev/Biot-Savart gradient control, H^s/enstrophy differential inequality, and continuation closure." } :
      NavierRoadmapEntry) ∈ currentNavierRoadmap := by
  simp [currentNavierRoadmap]

/-- The roadmap records the residual-curl vorticity-equation surface supplied
by finite-time BKM witnesses. -/
theorem currentNavierRoadmap_records_bkm_vorticity_residual_curl_equation :
    ({ stage := NavierRoadmapStage.bkmContinuation
       proofNodeId := "navier.bkm.vorticity-residual-curl-equation"
       status := .checked
       truthValue := ⟨85, 88⟩
       obligation :=
        "Use the checked finite-time witness residual-curl equation spatialVorticity(momentumPressureResidual nu u)=0 as the pressure-free vorticity-equation surface. Remaining BKM work factors the expansion through residualCurlExpansionDefect and then completes the log-Sobolev/high-norm continuation estimate." } :
      NavierRoadmapEntry) ∈ currentNavierRoadmap := by
  simp [currentNavierRoadmap]

/-- The roadmap records the residual-curl expansion defect bridge and its
precise remaining vector-calculus target. -/
theorem currentNavierRoadmap_records_bkm_residual_curl_expansion_defect :
    ({ stage := NavierRoadmapStage.bkmContinuation
       proofNodeId := "navier.bkm.residual-curl-expansion-defect"
       status := .checked
       truthValue := ⟨87, 88⟩
       obligation :=
        "Use the checked algebraic bridge from residual-curl zero plus residualCurlExpansionDefect = 0 to concreteVorticityEquationOn. The exact remaining vector-calculus target is BKMResidualCurlExpansionDefectVanishes for smooth incompressible velocities on the slab." } :
      NavierRoadmapEntry) ∈ currentNavierRoadmap := by
  simp [currentNavierRoadmap]

/-- The roadmap records the differential-identity decomposition of the
residual-curl expansion target. -/
theorem currentNavierRoadmap_records_bkm_residual_curl_differential_identities :
    ({ stage := NavierRoadmapStage.bkmContinuation
       proofNodeId := "navier.bkm.residual-curl-differential-identities"
       status := .checked
       truthValue := ⟨88, 88⟩
       obligation :=
        "Use BKMResidualCurlDifferentialIdentitiesClosed_of_commutationExpansion: the remaining decomposed residual-curl target is BKMResidualCurlCommutationExpansionClosed, i.e. curl/time commutation, curl/Laplacian commutation, and the incompressible curl-convection identity." } :
      NavierRoadmapEntry) ∈ currentNavierRoadmap := by
  simp [currentNavierRoadmap]

/-- The roadmap records the checked standard-vorticity-equation growth estimate. -/
theorem currentNavierRoadmap_records_bkm_standard_vorticity_growth :
    ({ stage := NavierRoadmapStage.bkmContinuation
       proofNodeId := "navier.bkm.standard-vorticity-growth"
       status := .checked
       truthValue := ⟨86, 88⟩
       obligation :=
        "Once concreteVorticityEquationOn is derived, use the checked material-minus-diffusion growth estimates, pointwise derivative d/dt (1/2 |omega|^2) = omega dot partial_t omega, transport algebra omega dot ((u.grad)omega) = (u.grad)(1/2 |omega|^2), Schwartz-slice transport cancellation from incompressibility, coordinate vorticity diffusion dissipation, Schwartz-slice Laplacian IBP, the witness-level Schwartz-slice a-priori enstrophy estimate, standard-equation-to-raw-enstrophy pairing algebra, and conditional dE/dt <= ||grad u||_inf E enstrophy-growth estimate. Remaining enstrophy work is lifting the pointwise time derivative through the spatial integral and instantiating or extending the Schwartz-slice transport/diffusion identities for finite-energy witnesses." } :
      NavierRoadmapEntry) ∈ currentNavierRoadmap := by
  simp [currentNavierRoadmap]

/-- The roadmap records the checked log-Sobolev gradient-control interface. -/
theorem currentNavierRoadmap_records_bkm_log_sobolev_gradient_control :
    ({ stage := NavierRoadmapStage.bkmContinuation
       proofNodeId := "navier.bkm.log-sobolev-gradient-control"
       status := .checked
       truthValue := ⟨87, 88⟩
       obligation :=
        "Once the analytic log-Sobolev/Biot-Savart gradient-control hypothesis is proved, use the checked logarithmic gradient envelope to feed the standard-vorticity growth, enstrophy-production, and dE/dt <= C * (1 + Omega log(exp(1) + H)) * E bounds. This does not itself prove the analytic gradient estimate." } :
      NavierRoadmapEntry) ∈ currentNavierRoadmap := by
  simp [currentNavierRoadmap]

/-- The roadmap records the one-lemma analytic reduction for the repaired BKM
continuation target. -/
theorem currentNavierRoadmap_records_bkm_single_analytic_lemma :
    ({ stage := NavierRoadmapStage.bkmContinuation
       proofNodeId := "navier.bkm.single-analytic-lemma"
       status := .checked
       truthValue := ⟨86, 88⟩
       obligation :=
        "The repaired nonnegative-horizon BKM target is reduced to BKMAnalyticContinuationLemma, whose statement is the remaining analytic proof obligation: positive-viscosity smooth divergence-free finite-energy data plus a finite-time witness with residual-curl vorticity equation and integrable vorticity envelope extend to the global output after proving residual-curl expansion, the remaining vorticity-enstrophy integral identities, log-Sobolev gradient control, and high-norm continuation." } :
      NavierRoadmapEntry) ∈ currentNavierRoadmap := by
  simp [currentNavierRoadmap]

/-- The roadmap records the componentized analytic route for the repaired BKM
continuation target. -/
theorem currentNavierRoadmap_records_bkm_analytic_components :
    ({ stage := NavierRoadmapStage.bkmContinuation
       proofNodeId := "navier.bkm.analytic-components"
       status := .checked
       truthValue := ⟨87, 88⟩
       obligation :=
        "Use BKMAnalyticContinuationLemma_of_components and BKMContinuation_reduced_to_analytic_components with the checked pointwise density derivative, vorticity raw-balance, transport-cancellation algebra plus Schwartz-slice transport cancellation, enstrophy-control, and gradient-growth packages. Remaining component targets are residual-curl expansion defect vanishing, the finite-energy vorticity-enstrophy integral identities, log-Sobolev/Biot-Savart gradient control from BKM envelope data, and high-norm continuation/Gronwall closure." } :
      NavierRoadmapEntry) ∈ currentNavierRoadmap := by
  simp [currentNavierRoadmap]

/-- The roadmap records the checked nonzero-preserving kernel and keeps the
explicit nonzero canary open. -/
theorem currentNavierRoadmap_records_nonzero_schwartz_kernel_and_open_canary :
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-kernel"
         status := .checked
         truthValue := ⟨79, 88⟩
         obligation :=
          "Use the checked nonzero-preserving energy/momentum packet for finite-mode generator work: it exposes the nonzero witness, pressure and convection cancellations, viscous identity, meaningful energy identity, literal momentum equation, incompressibility, pressure-residual equality, residual-curl-zero gate, and a whole-time zero-pressure two-profile canary at viscosity 0 whenever the inviscid closure is supplied. Keep the positive-viscosity nonzero pressure-slice closure as the open canary obligation." } :
      NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-line-invariant-obstruction"
         status := .checked
         truthValue := ⟨85, 90⟩
         obligation :=
          "Use the checked line-invariant obstruction to rule out shear shortcuts; future nonzero canaries must break line invariance and close the pressure-slice momentum equation." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-heat-shear-boundary"
         status := .checked
         truthValue := ⟨90, 91⟩
         obligation :=
          "Use the checked heat-shear boundary to separate the classical exact zero-pressure shear-flow solution from the whole-space slice-Schwartz canary lane; future nonzero canaries must avoid nondecaying time-zero slices as well as pressure-residual curl failures." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-canary"
         status := .openGoal
         truthValue := ⟨84, 88⟩
         obligation :=
          "Produce or refute an exact smooth positive-viscosity evolution and Schwartz pressure slices for the localized stream-function seed or a comparable non-polynomial Schwartz profile; seed-only data, conditional constructors, viscosity-0 finite-mode zero-pressure canaries, classical heat-shear exact solutions that fail Schwartz decay, rank-one zero-convection obstructions, nilpotent-shear pressure-residual obstructions, frozen nilpotent-slice obstructions, localized nilpotent stream stationary pressure-residual obstructions, profile-level nonzero anti-profile cancellation, anti-profile endpoint amplitude-boundary guardrails, anti-profile constant-difference obstructions, positive-viscosity stationary obstructions, strict-dissipation theorems conditional on the nonzero interface, flat-energy zero-rigidity obstructions, local-extremum energy obstructions, pointwise strict-derivative gates, local energy plateau obstructions, immediate right-drop gates, sampled right-drop gates, strict future-drop gates, energy-recurrence or repeated-slice obstructions, residual-curl pressure-closure rejections, finite-mode residual-curl boundaries, stationary inviscid closure constructors, conditional Stokes-flow kernels, Stokes rank-one obstructions, generalized zero-restart obstructions, past-dissipation ray theorems, endpoint support-order theorems, one-profile amplitude-boundary theorems, no-uniform-past-dissipation theorems, no-uniform-future-dissipation theorems, no-past-spectral-floor theorems, past dissipation-per-energy collapse theorems, past Rayleigh-quotient collapse theorems, spatial Rayleigh-quotient collapse theorems, general exact Rayleigh-equality obstructions, one-profile exact Rayleigh-equality obstructions, exact Stokes Rayleigh-equality obstructions, fixed-profile positive-viscosity emptiness theorems, fixed-profile Stokes emptiness theorem, finite-profile Stokes Rayleigh-floor obstruction, and algebraic finite-mode boundary cases do not count as the remaining positive-viscosity canary." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-rank-one-shear-obstruction"
         status := .checked
         truthValue := ⟨84, 89⟩
         obligation :=
          "Use the checked solution-level rank-one zero-convection obstruction to rule out fixed-direction Schwartz Stokes-flow shortcuts at every slice; future nonzero canaries must close a genuinely non-rank-one pressure-slice equation." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-symmetric-shear-obstruction"
         status := .checked
         truthValue := ⟨88, 88⟩
         obligation :=
          "Treat the exact nonzero symmetric finite-mode shear as an algebraic boundary canary only; its nonzero constant directional derivative excludes it from the Schwartz canary lane." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-nilpotent-shear-pressure-obstruction"
         status := .checked
         truthValue := ⟨91, 92⟩
         obligation :=
          "Use the checked nilpotent-shear and frozen nilpotent-slice pressure-residual curl obstructions to reject multi-stage steady linear shear chains; future nonzero canaries must prove curl-free pressure residual closure after localization, not just divergence-free linear algebra." } :
      NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-localized-stream-seed"
         status := .checked
         truthValue := ⟨72, 88⟩
         obligation :=
          "Use the checked localized stream-function seed as the concrete nonzero divergence-free Schwartz input for the next pressure-slice closure search." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-localized-nilpotent-stream-obstruction"
         status := .checked
         truthValue := ⟨88, 91⟩
         obligation :=
          "Use the checked localized nilpotent stream germ obstruction to reject stationary inviscid pressure-closure shortcuts for an inhabited nonzero divergence-free Schwartz datum, even when only the local velocity germ and vanishing instantaneous time-derivative germ are fixed; future canaries must use nonstationary time dependence or a different localized profile so the residual curl vanishes." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-antiprofile-canary-obstruction"
         status := .checked
         truthValue := ⟨84, 90⟩
         obligation :=
          "Use the checked localized stream/anti-stream cancellation guardrail to reject profile-level nonzero closures whose reconstructed velocity is zero." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-antiprofile-amplitude-boundary"
         status := .checked
         truthValue := ⟨90, 91⟩
         obligation :=
          "Use the checked anti-profile amplitude boundary to require unequal, time-varying, and endpoint-strictly-dropping amplitude differences before testing localized stream/anti-stream candidates against the pressure-slice momentum equation." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-stationary-dissipation-gate"
         status := .checked
         truthValue := ⟨89, 91⟩
         obligation :=
          "Use the checked positive-viscosity stationary obstruction to reject time-independent nonzero slice-Schwartz canaries; future nonzero canaries must be genuinely time-dependent and close the pressure-slice momentum equation." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-strict-dissipation-kernel"
         status := .checked
         truthValue := ⟨88, 90⟩
         obligation :=
          "Use the checked strict-dissipation kernel to ensure any positive-viscosity nonzero inhabitant has a witness time with positive corrected dissipation and strictly negative energy derivative; still require an explicit inhabitant or broader pressure-closure obstruction." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-no-flat-energy-obstruction"
         status := .checked
         truthValue := ⟨90, 90⟩
         obligation :=
          "Use the checked flat-energy zero-rigidity theorem to reject positive-viscosity canaries with everywhere-zero normalized-energy derivative or constant normalized kinetic energy; future positive canaries must genuinely dissipate." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-local-extremum-obstruction"
         status := .checked
         truthValue := ⟨91, 90⟩
         obligation :=
          "Use the checked local-extremum obstruction to reject positive-viscosity canaries whose nonzero witness occurs at a local minimum or maximum of normalized kinetic energy." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-pointwise-strict-derivative"
         status := .checked
         truthValue := ⟨92, 90⟩
         obligation :=
          "Use the checked pointwise strict-derivative gate to require every positive-viscosity nonzero witness time to have strictly negative normalized kinetic-energy derivative." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-local-plateau-obstruction"
         status := .checked
         truthValue := ⟨92, 89⟩
         obligation :=
          "Use the checked local-plateau obstruction to reject positive-viscosity canaries whose nonzero witness occurs at a locally constant normalized-energy time." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-immediate-right-drop"
         status := .checked
         truthValue := ⟨93, 89⟩
         obligation :=
          "Use the checked immediate right-drop gate to require every positive-viscosity nonzero witness time to have normalized kinetic energy eventually strictly lower on the right." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-right-drop-sample"
         status := .checked
         truthValue := ⟨94, 89⟩
         obligation :=
          "Use the checked sampled right-drop gate to require every positive-viscosity nonzero witness time to exhibit an actual lower-energy sample inside each positive right interval." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-strict-future-drop"
         status := .checked
         truthValue := ⟨95, 89⟩
         obligation :=
          "Use the checked strict future-drop gate to require every later endpoint after a positive-viscosity nonzero witness time to have strictly lower normalized kinetic energy." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-no-energy-recurrence"
         status := .checked
         truthValue := ⟨96, 89⟩
         obligation :=
          "Use the checked no-recurrence gate to reject positive-viscosity nonzero canaries with positive-period normalized-energy recurrence, periodic velocity, or a repeated nonzero velocity slice at a strictly later time." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.schwartz-pressure-residual-curl-gate"
         status := .checked
         truthValue := ⟨87, 89⟩
         obligation :=
          "Use the checked pressure-residual curl gate to reject any candidate velocity whose residual νΔu - ∂tu - (u.grad)u has nonzero spatial vorticity; future positive canaries must prove the residual is curl-free before searching for pressure slices." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-finite-mode-residual-curl-boundary"
         status := .checked
         truthValue := ⟨91, 91⟩
         obligation :=
          "Use the checked finite-mode route boundary: the inviscid zero-pressure two-profile closure gives a nonzero whole-time slice-Schwartz energy-identity canary at viscosity 0, and the same branch cannot be reused at viscosity ν when its viscous Laplacian residual has nonzero curl. Future positive-viscosity canaries must exhibit curl-free residual closure and explicit pressure slices." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-stationary-inviscid-constructor"
         status := .checked
         truthValue := ⟨78, 88⟩
         obligation :=
          "Use the checked stationary inviscid energy-identity canary packet as the exact one-profile closure surface for localized Euler-style searches: at viscosity 0 it returns a nonzero concrete solution witness with exact velocity/pressure equalities, cancellation integrals, coordinate viscous formula, and zero-viscosity meaningful energy identity. Keep the positive-viscosity nonzero canary open." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-stokes-kernel"
         status := .checked
         truthValue := ⟨85, 89⟩
         obligation :=
          "Use the checked Stokes-flow kernel to make zero-convection/zero-pressure-gradient canary attempts satisfy the exact Stokes equation, strict positive-viscosity dissipation, a nonzero endpoint with strictly ordered and nonrepeating past velocity slices, no nondecreasing energy subinterval before that endpoint, and no positive-period recurrence; still construct an inhabited bounded whole-real-time Schwartz Stokes flow or prove that subroute empty." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-stokes-rankone-obstruction"
         status := .checked
         truthValue := ⟨85, 88⟩
         obligation :=
          "Use the checked Stokes rank-one obstruction to reject exact Stokes-flow candidates whose every slice stays in one fixed nonzero rank-one Schwartz direction; future Stokes canaries must be genuinely non-rank-one or prove the whole bounded eternal Stokes subroute empty." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-zero-restart-obstruction"
         status := .checked
         truthValue := ⟨84, 88⟩
         obligation :=
          "Use the checked zero-restart kernel to reject candidate evolutions that pass from a zero velocity slice to a later nonzero slice at nonnegative viscosity, both in the general slice-Schwartz interface and in the Stokes subroute; future positive canaries must either stay nonzero on every earlier slice before a nonzero witness or prove the full pressure/time-evolution closure directly." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-past-dissipation-ray"
         status := .checked
         truthValue := ⟨86, 88⟩
         obligation :=
          "Use the checked past-dissipation ray to require every positive-viscosity nonzero canary to expose a witness whose whole earlier half-line is nonzero somewhere, strictly dissipative, and strictly energy-dropping on forward subintervals; future Stokes/pressure-closure work must supply a real bounded eternal construction or a quantitative obstruction for that half-line." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-endpoint-support"
         status := .checked
         truthValue := ⟨88, 89⟩
         obligation :=
          "Use the checked endpoint support kernel to test any candidate from each later nonzero endpoint: every earlier slice must be nonzero somewhere and every earlier forward subinterval must strictly lose normalized energy. A full bounded-eternal Stokes obstruction still needs a quantitative lower-bound or spectral-gap input." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-one-profile-amplitude-boundary"
         status := .checked
         truthValue := ⟨89, 89⟩
         obligation :=
          "Use the checked one-profile amplitude boundary to reject positive-viscosity separable Schwartz candidates whose squared scalar amplitude is repeated or nondecreasing before a later nonzero endpoint; future canaries must be genuinely multi-profile/nonseparable or prove the full pressure/time-evolution closure directly." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-no-uniform-past-dissipation"
         status := .checked
         truthValue := ⟨97, 94⟩
         obligation :=
          "Use the checked no-uniform-past/future-dissipation, no-past-spectral-floor, past dissipation-per-energy collapse, corrected-dissipation Rayleigh collapse, spatial Rayleigh collapse, exact Rayleigh-equality obstruction, one-profile exact Rayleigh/eigenmode obstruction, fixed-profile positive-viscosity emptiness theorem, fixed-profile Stokes emptiness theorem, Stokes profile-gap, endpoint strict-energy/low-Rayleigh, and exact Stokes Rayleigh-equality obstruction packets to reject bounded eternal positive-viscosity candidates certified by a uniform positive past or future dissipation gap, a positive Poincare/spectral floor of corrected dissipation or coordinate enstrophy over normalized energy, a positive whole-past Rayleigh-quotient floor, an endpoint ray avoiding arbitrarily small positive spatial Rayleigh samples, an exact positive whole-past spatial Rayleigh equality, a fixed-profile exact Rayleigh/eigenmode shortcut, or any nonzero scalar fixed-profile evolution. Future canary work must construct the exact nonzero evolution in a genuinely multi-profile/nonseparable class while allowing arbitrarily small past spatial Rayleigh-quotient samples before every nonzero endpoint and no uniform positive future dissipation floor, or prove a stronger structural emptiness theorem for the Stokes/pressure-closure class." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-stokes-finite-profile-rayleigh-obstruction"
         status := .checked
         truthValue := ⟨93, 92⟩
         obligation :=
          "Use the checked finite-profile Stokes Rayleigh-floor obstruction to reject generator classes that try to certify a bounded eternal positive-viscosity exact Stokes canary by a positive whole-past spatial Rayleigh floor; future Stokes canaries must either evade every positive past Rayleigh floor with low-frequency slices, leave the exact Stokes subroute, or prove a stronger full Stokes/pressure-closure emptiness theorem." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.schwartz-pressure-closure-certificate"
         status := .checked
         truthValue := ⟨90, 91⟩
         obligation :=
          "Use the checked pressure-closure certificate API to make residual-curl failures generator-facing: the localized nilpotent stream certificate is an explicit nonzero divergence-free Schwartz failed-canary boundary, and future positive canaries must prove no such certificate exists before constructing pressure slices." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      navierNonzeroSchwartzEnergyKernelNode.status = .checked ∧
      navierNonzeroSchwartzLineInvariantObstructionNode.status = .checked ∧
      navierNonzeroSchwartzHeatShearBoundaryNode.status = .checked ∧
      navierNonzeroSchwartzRankOneShearObstructionNode.status = .checked ∧
      navierNonzeroSchwartzSymmetricShearObstructionNode.status = .checked ∧
      navierNonzeroSchwartzNilpotentShearPressureObstructionNode.status = .checked ∧
      navierNonzeroSchwartzLocalizedStreamSeedNode.status = .checked ∧
      navierNonzeroSchwartzLocalizedNilpotentStreamObstructionNode.status = .checked ∧
      navierNonzeroSchwartzAntiProfileCanaryObstructionNode.status = .checked ∧
      navierNonzeroSchwartzAntiProfileAmplitudeBoundaryNode.status = .checked ∧
      navierNonzeroSchwartzStationaryDissipationGateNode.status = .checked ∧
      navierNonzeroSchwartzStrictDissipationKernelNode.status = .checked ∧
      navierNonzeroSchwartzNoFlatEnergyObstructionNode.status = .checked ∧
      navierNonzeroSchwartzLocalExtremumEnergyObstructionNode.status = .checked ∧
      navierNonzeroSchwartzPointwiseStrictDerivativeNode.status = .checked ∧
      navierNonzeroSchwartzLocalPlateauObstructionNode.status = .checked ∧
      navierNonzeroSchwartzImmediateRightDropNode.status = .checked ∧
      navierNonzeroSchwartzRightDropSampleNode.status = .checked ∧
      navierNonzeroSchwartzStrictFutureDropNode.status = .checked ∧
      navierNonzeroSchwartzNoEnergyRecurrenceNode.status = .checked ∧
      navierSchwartzPressureResidualCurlGateNode.status = .checked ∧
      navierSchwartzPressureClosureCertificateNode.status = .checked ∧
      navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode.status = .checked ∧
      navierNonzeroSchwartzStationaryInviscidConstructorNode.status = .checked ∧
      navierNonzeroSchwartzStokesKernelNode.status = .checked ∧
      navierNonzeroSchwartzStokesRankOneObstructionNode.status = .checked ∧
      navierNonzeroSchwartzZeroRestartNode.status = .checked ∧
      navierNonzeroSchwartzPastDissipationNode.status = .checked ∧
      navierNonzeroSchwartzEndpointSupportNode.status = .checked ∧
      navierNonzeroSchwartzOneProfileAmplitudeBoundaryNode.status = .checked ∧
      navierNonzeroSchwartzNoUniformPastDissipationNode.status = .checked ∧
      navierNonzeroSchwartzStokesFiniteProfileRayleighObstructionNode.status = .checked ∧
      navierNonzeroSchwartzCanaryNode.status = .openGoal := by
  exact ⟨by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    by simp [currentNavierRoadmap],
    navierNonzeroSchwartzEnergyKernelNode_checked,
    navierNonzeroSchwartzLineInvariantObstructionNode_checked,
    navierNonzeroSchwartzHeatShearBoundaryNode_checked,
    navierNonzeroSchwartzRankOneShearObstructionNode_checked,
    navierNonzeroSchwartzSymmetricShearObstructionNode_checked,
    navierNonzeroSchwartzNilpotentShearPressureObstructionNode_checked,
    navierNonzeroSchwartzLocalizedStreamSeedNode_checked,
    navierNonzeroSchwartzLocalizedNilpotentStreamObstructionNode_checked,
    navierNonzeroSchwartzAntiProfileCanaryObstructionNode_checked,
    navierNonzeroSchwartzAntiProfileAmplitudeBoundaryNode_checked,
    navierNonzeroSchwartzStationaryDissipationGateNode_checked,
    navierNonzeroSchwartzStrictDissipationKernelNode_checked,
    navierNonzeroSchwartzNoFlatEnergyObstructionNode_checked,
    navierNonzeroSchwartzLocalExtremumEnergyObstructionNode_checked,
    navierNonzeroSchwartzPointwiseStrictDerivativeNode_checked,
    navierNonzeroSchwartzLocalPlateauObstructionNode_checked,
    navierNonzeroSchwartzImmediateRightDropNode_checked,
    navierNonzeroSchwartzRightDropSampleNode_checked,
    navierNonzeroSchwartzStrictFutureDropNode_checked,
    navierNonzeroSchwartzNoEnergyRecurrenceNode_checked,
    navierSchwartzPressureResidualCurlGateNode_checked,
    navierSchwartzPressureClosureCertificateNode_checked,
    navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode_checked,
    navierNonzeroSchwartzStationaryInviscidConstructorNode_checked,
    navierNonzeroSchwartzStokesKernelNode_checked,
    navierNonzeroSchwartzStokesRankOneObstructionNode_checked,
    navierNonzeroSchwartzZeroRestartNode_checked,
    navierNonzeroSchwartzPastDissipationNode_checked,
    navierNonzeroSchwartzEndpointSupportNode_checked,
    navierNonzeroSchwartzOneProfileAmplitudeBoundaryNode_checked,
    navierNonzeroSchwartzNoUniformPastDissipationNode_checked,
    navierNonzeroSchwartzStokesFiniteProfileRayleighObstructionNode_checked,
    navierNonzeroSchwartzCanaryNode_open⟩

/-- The current roadmap pins the averaged-equation obstruction before any
replacement global-regularity route. -/
theorem currentNavierRoadmap_orders_averaged_obstruction_before_replacement :
    currentNavierEnergyBKMRouteAllAveragedEquationObstructionPacket ∧
      ¬ currentNavierEnergyBKMRegularityPromotionGate.ClearsAll ∧
      ({ stage := NavierRoadmapStage.replacementRoute
         proofNodeId := "navier.open-global-regularity-route"
         status := .openGoal
         truthValue := ⟨0, 99⟩
         obligation :=
          "Start a replacement global route only after scaling, challenge-world, and averaged-equation checks clear." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap := by
  exact
    ⟨currentNavierEnergyBKMRoute_allAveragedEquationObstructions,
      currentNavierEnergyBKMRegularityPromotionGate_not_cleared,
      by simp [currentNavierRoadmap]⟩

end NavierStokes
end FluidDynamics
end Mettapedia
