import Mettapedia.Computability.PNP.ProofState

/-!
# PNP roadmap

This module records the checked route order for the current PNP lane.  It is a
roadmap for honest proof-state movement, not a P versus NP result.
-/

namespace Mettapedia.Computability.PNP

/-- Roadmap stage tags for the current PNP lane. -/
inductive PNPRoadmapStage where
  | sourceMap
  | liveRegressionSplit
  | localLedgerAudit
  | barrierObstruction
  | replacementRoute
deriving DecidableEq, Repr

/-- One checked roadmap entry, tied back to a proof-state node key. -/
structure PNPRoadmapEntry where
  stage : PNPRoadmapStage
  proofNodeKey : String
  status : PNPProofNodeStatus
  truthValue : SimpleTruthValue
  obligation : String
deriving Repr

/-- Current roadmap order for the active PNP route. -/
def currentPNPRoadmap : List PNPRoadmapEntry :=
  [ { stage := .sourceMap
      proofNodeKey := "pnp.map.current-lane"
      status := .surveyed
      truthValue := ⟨100, 94⟩
      obligation := "Keep the dependency map and split threshold current." },
    { stage := .liveRegressionSplit
      proofNodeKey := "pnp.map.current-lane"
      status := .checked
      truthValue := ⟨100, 93⟩
      obligation := "Keep the live entrypoint separate from the regression aggregator." },
    { stage := .localLedgerAudit
      proofNodeKey := "pnp.v13.locked-core-identity-readout-family"
      status := .blockedByCounterexample
      truthValue := ⟨100, 99⟩
      obligation := "Treat deterministic readout as refuted for the scaled identity-readout locked-core family unless a public-message invariant is supplied." },
    { stage := .localLedgerAudit
      proofNodeKey := "pnp.kpoly-promoted-packet"
      status := .ledgerCovered
      truthValue := ⟨100, 92⟩
      obligation := "Treat local Kpoly coverage as local ledger evidence only." },
    { stage := .localLedgerAudit, proofNodeKey := "pnp.kpoly.support-surjectivity-weakness-boundary", status := .blockedByCounterexample, truthValue := ⟨100, 99⟩, obligation := "Treat observed-support polynomial images as resolved insufficient unless the route supplies support-surjective feature/query coverage or a supported resolving side-information package." },
    { stage := .barrierObstruction
      proofNodeKey := "pnp.kpoly-promoted.all-barrier-obstructions"
      status := .barrierBlocked
      truthValue := ⟨100, 99⟩
      obligation := "Do not promote the route while all three barrier escape layers are missing." },
    { stage := .replacementRoute
      proofNodeKey := "pnp.global-separation"
      status := .openBackground
      truthValue := ⟨0, 99⟩
      obligation := "Start a replacement global route only after the barrier-world interfaces and escape witnesses are represented." } ]

theorem currentPNPRoadmap_nonempty : currentPNPRoadmap ≠ [] := by
  simp [currentPNPRoadmap]

/-- The current roadmap pins the local ledger before the blocked global
promotion gate. -/
theorem currentPNPRoadmap_orders_local_ledger_before_global_promotion :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll ∧
      ({ stage := PNPRoadmapStage.replacementRoute
         proofNodeKey := "pnp.global-separation"
         status := .openBackground
         truthValue := ⟨0, 99⟩
         obligation :=
          "Start a replacement global route only after the barrier-world interfaces and escape witnesses are represented." } :
        PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  exact
    ⟨(currentPNPKpolyPromotedPacket_stopGrade_and_allBarrierObstructions).1,
      currentPNPKpolyPromotedBarrierPromotionGate_not_cleared,
      by simp [currentPNPRoadmap]⟩

end Mettapedia.Computability.PNP
