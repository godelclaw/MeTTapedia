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
