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
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-kernel"
      status := .checked
      truthValue := ⟨73, 86⟩
      obligation := "Use the checked nonzero-preserving kernel for finite-mode generator work, but keep the explicit inhabited nonzero pressure-slice closure as the open canary obligation." },
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
      proofNodeId := "navier.energy.nonzero-schwartz-antiprofile-canary-obstruction"
      status := .checked
      truthValue := ⟨84, 90⟩
      obligation := "Use the checked localized stream/anti-stream cancellation guardrail to reject profile-level nonzero closures whose reconstructed velocity is zero." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-antiprofile-amplitude-boundary"
      status := .checked
      truthValue := ⟨88, 91⟩
      obligation := "Use the checked anti-profile amplitude boundary to require unequal and, at positive viscosity, time-varying amplitude differences before testing localized stream/anti-stream candidates against the pressure-slice momentum equation." },
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
      truthValue := ⟨95, 89⟩
      obligation := "Use the checked no-recurrence gate to reject positive-viscosity nonzero canaries with positive-period normalized-energy recurrence or periodic velocity." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.schwartz-pressure-residual-curl-gate"
      status := .checked
      truthValue := ⟨87, 89⟩
      obligation := "Use the checked pressure-residual curl gate to reject any candidate velocity whose residual νΔu - ∂tu - (u.grad)u has nonzero spatial vorticity; future positive canaries must prove the residual is curl-free before searching for pressure slices." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-finite-mode-residual-curl-boundary"
      status := .checked
      truthValue := ⟨89, 90⟩
      obligation := "Use the checked finite-mode residual-curl boundary to require the constant-amplitude two-mode generator's viscous Laplacian residual to be curl-free before treating its pressure-slice closure as a canary candidate." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-stationary-inviscid-constructor"
      status := .checked
      truthValue := ⟨76, 88⟩
      obligation := "Use the checked stationary inviscid constructor as the exact one-profile closure surface for localized Euler-style searches, while keeping the positive-viscosity nonzero canary open." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-stokes-kernel"
      status := .checked
      truthValue := ⟨82, 88⟩
      obligation := "Use the checked Stokes-flow kernel to make zero-convection/zero-pressure-gradient canary attempts satisfy the exact Stokes equation, strict positive-viscosity dissipation, and no positive-period recurrence; still construct an inhabited bounded whole-real-time Schwartz Stokes flow or prove that subroute empty." },
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
      proofNodeId := "navier.energy.nonzero-schwartz-no-uniform-past-dissipation"
      status := .checked
      truthValue := ⟨93, 90⟩
      obligation := "Use the checked no-uniform-past-dissipation, no-past-spectral-floor, past dissipation-per-energy collapse, and past Rayleigh-quotient collapse obstructions to reject bounded eternal positive-viscosity candidates certified by a uniform positive past dissipation gap, a positive Poincare/spectral floor of corrected dissipation over normalized energy, or a positive whole-past corrected-dissipation Rayleigh-quotient floor. Future canary work must construct the exact nonzero evolution while allowing arbitrarily small past Rayleigh-quotient samples, or prove a stronger structural emptiness theorem for the Stokes/pressure-closure class." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-canary"
      status := .openGoal
      truthValue := ⟨80, 87⟩
      obligation := "Produce or refute an exact smooth evolution and Schwartz pressure slices for the localized stream-function seed or a comparable non-polynomial Schwartz profile; seed-only data, conditional constructors, classical heat-shear exact solutions that fail Schwartz decay, rank-one zero-convection obstructions, nilpotent-shear pressure-residual obstructions, frozen nilpotent-slice obstructions, profile-level nonzero anti-profile cancellation, amplitude-boundary guardrails, anti-profile constant-difference obstructions, positive-viscosity stationary obstructions, strict-dissipation theorems conditional on the nonzero interface, flat-energy zero-rigidity obstructions, local-extremum energy obstructions, pointwise strict-derivative gates, local energy plateau obstructions, immediate right-drop gates, sampled right-drop gates, strict future-drop gates, energy-recurrence obstructions, residual-curl pressure-closure rejections, finite-mode residual-curl boundaries, stationary inviscid closure constructors, conditional Stokes-flow kernels, Stokes rank-one obstructions, generalized zero-restart obstructions, past-dissipation ray theorems, endpoint support-order theorems, no-uniform-past-dissipation theorems, no-past-spectral-floor theorems, past dissipation-per-energy collapse theorems, past Rayleigh-quotient collapse theorems, and algebraic finite-mode boundary cases do not count." },
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

/-- The roadmap records the checked nonzero-preserving kernel and keeps the
explicit nonzero canary open. -/
theorem currentNavierRoadmap_records_nonzero_schwartz_kernel_and_open_canary :
    ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
       proofNodeId := "navier.energy.nonzero-schwartz-kernel"
       status := .checked
       truthValue := ⟨73, 86⟩
       obligation :=
        "Use the checked nonzero-preserving kernel for finite-mode generator work, but keep the explicit inhabited nonzero pressure-slice closure as the open canary obligation." } :
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
         truthValue := ⟨80, 87⟩
         obligation :=
          "Produce or refute an exact smooth evolution and Schwartz pressure slices for the localized stream-function seed or a comparable non-polynomial Schwartz profile; seed-only data, conditional constructors, classical heat-shear exact solutions that fail Schwartz decay, rank-one zero-convection obstructions, nilpotent-shear pressure-residual obstructions, frozen nilpotent-slice obstructions, profile-level nonzero anti-profile cancellation, amplitude-boundary guardrails, anti-profile constant-difference obstructions, positive-viscosity stationary obstructions, strict-dissipation theorems conditional on the nonzero interface, flat-energy zero-rigidity obstructions, local-extremum energy obstructions, pointwise strict-derivative gates, local energy plateau obstructions, immediate right-drop gates, sampled right-drop gates, strict future-drop gates, energy-recurrence obstructions, residual-curl pressure-closure rejections, finite-mode residual-curl boundaries, stationary inviscid closure constructors, conditional Stokes-flow kernels, Stokes rank-one obstructions, generalized zero-restart obstructions, past-dissipation ray theorems, endpoint support-order theorems, no-uniform-past-dissipation theorems, no-past-spectral-floor theorems, past dissipation-per-energy collapse theorems, past Rayleigh-quotient collapse theorems, and algebraic finite-mode boundary cases do not count." } :
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
         proofNodeId := "navier.energy.nonzero-schwartz-antiprofile-canary-obstruction"
         status := .checked
         truthValue := ⟨84, 90⟩
         obligation :=
          "Use the checked localized stream/anti-stream cancellation guardrail to reject profile-level nonzero closures whose reconstructed velocity is zero." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-antiprofile-amplitude-boundary"
         status := .checked
         truthValue := ⟨88, 91⟩
         obligation :=
          "Use the checked anti-profile amplitude boundary to require unequal and, at positive viscosity, time-varying amplitude differences before testing localized stream/anti-stream candidates against the pressure-slice momentum equation." } :
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
         truthValue := ⟨95, 89⟩
         obligation :=
          "Use the checked no-recurrence gate to reject positive-viscosity nonzero canaries with positive-period normalized-energy recurrence or periodic velocity." } :
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
         truthValue := ⟨89, 90⟩
         obligation :=
          "Use the checked finite-mode residual-curl boundary to require the constant-amplitude two-mode generator's viscous Laplacian residual to be curl-free before treating its pressure-slice closure as a canary candidate." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-stationary-inviscid-constructor"
         status := .checked
         truthValue := ⟨76, 88⟩
         obligation :=
          "Use the checked stationary inviscid constructor as the exact one-profile closure surface for localized Euler-style searches, while keeping the positive-viscosity nonzero canary open." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-stokes-kernel"
         status := .checked
         truthValue := ⟨82, 88⟩
         obligation :=
          "Use the checked Stokes-flow kernel to make zero-convection/zero-pressure-gradient canary attempts satisfy the exact Stokes equation, strict positive-viscosity dissipation, and no positive-period recurrence; still construct an inhabited bounded whole-real-time Schwartz Stokes flow or prove that subroute empty." } :
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
         proofNodeId := "navier.energy.nonzero-schwartz-no-uniform-past-dissipation"
         status := .checked
         truthValue := ⟨93, 90⟩
         obligation :=
          "Use the checked no-uniform-past-dissipation, no-past-spectral-floor, past dissipation-per-energy collapse, and past Rayleigh-quotient collapse obstructions to reject bounded eternal positive-viscosity candidates certified by a uniform positive past dissipation gap, a positive Poincare/spectral floor of corrected dissipation over normalized energy, or a positive whole-past corrected-dissipation Rayleigh-quotient floor. Future canary work must construct the exact nonzero evolution while allowing arbitrarily small past Rayleigh-quotient samples, or prove a stronger structural emptiness theorem for the Stokes/pressure-closure class." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      navierNonzeroSchwartzEnergyKernelNode.status = .checked ∧
      navierNonzeroSchwartzLineInvariantObstructionNode.status = .checked ∧
      navierNonzeroSchwartzHeatShearBoundaryNode.status = .checked ∧
      navierNonzeroSchwartzRankOneShearObstructionNode.status = .checked ∧
      navierNonzeroSchwartzSymmetricShearObstructionNode.status = .checked ∧
      navierNonzeroSchwartzNilpotentShearPressureObstructionNode.status = .checked ∧
      navierNonzeroSchwartzLocalizedStreamSeedNode.status = .checked ∧
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
      navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode.status = .checked ∧
      navierNonzeroSchwartzStationaryInviscidConstructorNode.status = .checked ∧
      navierNonzeroSchwartzStokesKernelNode.status = .checked ∧
      navierNonzeroSchwartzStokesRankOneObstructionNode.status = .checked ∧
      navierNonzeroSchwartzZeroRestartNode.status = .checked ∧
      navierNonzeroSchwartzPastDissipationNode.status = .checked ∧
      navierNonzeroSchwartzEndpointSupportNode.status = .checked ∧
      navierNonzeroSchwartzNoUniformPastDissipationNode.status = .checked ∧
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
    navierNonzeroSchwartzEnergyKernelNode_checked,
    navierNonzeroSchwartzLineInvariantObstructionNode_checked,
    navierNonzeroSchwartzHeatShearBoundaryNode_checked,
    navierNonzeroSchwartzRankOneShearObstructionNode_checked,
    navierNonzeroSchwartzSymmetricShearObstructionNode_checked,
    navierNonzeroSchwartzNilpotentShearPressureObstructionNode_checked,
    navierNonzeroSchwartzLocalizedStreamSeedNode_checked,
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
    navierNonzeroSchwartzFiniteModeResidualCurlBoundaryNode_checked,
    navierNonzeroSchwartzStationaryInviscidConstructorNode_checked,
    navierNonzeroSchwartzStokesKernelNode_checked,
    navierNonzeroSchwartzStokesRankOneObstructionNode_checked,
    navierNonzeroSchwartzZeroRestartNode_checked,
    navierNonzeroSchwartzPastDissipationNode_checked,
    navierNonzeroSchwartzEndpointSupportNode_checked,
    navierNonzeroSchwartzNoUniformPastDissipationNode_checked,
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
