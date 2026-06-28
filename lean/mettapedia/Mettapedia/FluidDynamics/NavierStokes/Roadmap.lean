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
      proofNodeId := "navier.energy.nonzero-schwartz-rank-one-shear-obstruction"
      status := .checked
      truthValue := ⟨82, 89⟩
      obligation := "Use the checked rank-one zero-convection obstruction to rule out fixed-direction Schwartz Stokes-flow shortcuts; future nonzero canaries must close a genuinely non-rank-one pressure-slice equation." },
    { stage := .nonzeroEnergyKernel
      proofNodeId := "navier.energy.nonzero-schwartz-symmetric-shear-obstruction"
      status := .checked
      truthValue := ⟨88, 88⟩
      obligation := "Treat the exact nonzero symmetric finite-mode shear as an algebraic boundary canary only; its nonzero constant directional derivative excludes it from the Schwartz canary lane." },
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
      truthValue := ⟨87, 91⟩
      obligation := "Use the checked anti-profile amplitude boundary to require unequal amplitudes before testing localized stream/anti-stream candidates against the pressure-slice momentum equation." },
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
      proofNodeId := "navier.energy.nonzero-schwartz-canary"
      status := .openGoal
      truthValue := ⟨62, 86⟩
      obligation := "Produce or refute an exact smooth evolution and Schwartz pressure slices for the localized stream-function seed or a comparable non-polynomial Schwartz profile; seed-only data, conditional constructors, rank-one zero-convection obstructions, profile-level nonzero anti-profile cancellation, amplitude-boundary guardrails, positive-viscosity stationary obstructions, strict-dissipation theorems conditional on the nonzero interface, and algebraic finite-mode boundary cases do not count." },
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
         proofNodeId := "navier.energy.nonzero-schwartz-canary"
         status := .openGoal
         truthValue := ⟨62, 86⟩
         obligation :=
          "Produce or refute an exact smooth evolution and Schwartz pressure slices for the localized stream-function seed or a comparable non-polynomial Schwartz profile; seed-only data, conditional constructors, rank-one zero-convection obstructions, profile-level nonzero anti-profile cancellation, amplitude-boundary guardrails, positive-viscosity stationary obstructions, strict-dissipation theorems conditional on the nonzero interface, and algebraic finite-mode boundary cases do not count." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-rank-one-shear-obstruction"
         status := .checked
         truthValue := ⟨82, 89⟩
         obligation :=
          "Use the checked rank-one zero-convection obstruction to rule out fixed-direction Schwartz Stokes-flow shortcuts; future nonzero canaries must close a genuinely non-rank-one pressure-slice equation." } :
        NavierRoadmapEntry) ∈ currentNavierRoadmap ∧
      ({ stage := NavierRoadmapStage.nonzeroEnergyKernel
         proofNodeId := "navier.energy.nonzero-schwartz-symmetric-shear-obstruction"
         status := .checked
         truthValue := ⟨88, 88⟩
         obligation :=
          "Treat the exact nonzero symmetric finite-mode shear as an algebraic boundary canary only; its nonzero constant directional derivative excludes it from the Schwartz canary lane." } :
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
         truthValue := ⟨87, 91⟩
         obligation :=
          "Use the checked anti-profile amplitude boundary to require unequal amplitudes before testing localized stream/anti-stream candidates against the pressure-slice momentum equation." } :
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
      navierNonzeroSchwartzEnergyKernelNode.status = .checked ∧
      navierNonzeroSchwartzLineInvariantObstructionNode.status = .checked ∧
      navierNonzeroSchwartzRankOneShearObstructionNode.status = .checked ∧
      navierNonzeroSchwartzSymmetricShearObstructionNode.status = .checked ∧
      navierNonzeroSchwartzLocalizedStreamSeedNode.status = .checked ∧
      navierNonzeroSchwartzAntiProfileCanaryObstructionNode.status = .checked ∧
      navierNonzeroSchwartzAntiProfileAmplitudeBoundaryNode.status = .checked ∧
      navierNonzeroSchwartzStationaryDissipationGateNode.status = .checked ∧
      navierNonzeroSchwartzStrictDissipationKernelNode.status = .checked ∧
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
    navierNonzeroSchwartzEnergyKernelNode_checked,
    navierNonzeroSchwartzLineInvariantObstructionNode_checked,
    navierNonzeroSchwartzRankOneShearObstructionNode_checked,
    navierNonzeroSchwartzSymmetricShearObstructionNode_checked,
    navierNonzeroSchwartzLocalizedStreamSeedNode_checked,
    navierNonzeroSchwartzAntiProfileCanaryObstructionNode_checked,
    navierNonzeroSchwartzAntiProfileAmplitudeBoundaryNode_checked,
    navierNonzeroSchwartzStationaryDissipationGateNode_checked,
    navierNonzeroSchwartzStrictDissipationKernelNode_checked,
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
