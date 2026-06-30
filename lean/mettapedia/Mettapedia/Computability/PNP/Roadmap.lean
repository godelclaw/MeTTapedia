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
  | goertzelCalibrationBreak
  | barrierObstruction
  | replacementRoute
deriving DecidableEq, Repr

/-- One checked roadmap entry, tied back to a proof-state node key. -/
structure PNPRoadmapEntry where
  stage : PNPRoadmapStage
  proofNodeKey : String
  status : PNPProofNodeStatus
  truthValue : SimpleTruthValue
  progressPercent : Nat
  itvLowerPercent : Nat
  itvUpperPercent : Nat
  obligation : String
deriving Repr

/-- Current roadmap order for the active PNP route. -/
def currentPNPRoadmap : List PNPRoadmapEntry :=
  [ { stage := .sourceMap
      proofNodeKey := "pnp.map.current-lane"
      status := .surveyed
      truthValue := ⟨100, 94⟩
      progressPercent := 100
      itvLowerPercent := 94
      itvUpperPercent := 100
      obligation := "Keep the dependency map and split threshold current." },
    { stage := .liveRegressionSplit
      proofNodeKey := "pnp.map.current-lane"
      status := .checked
      truthValue := ⟨100, 93⟩
      progressPercent := 100
      itvLowerPercent := 93
      itvUpperPercent := 100
      obligation := "Keep the live entrypoint separate from the regression aggregator." },
    { stage := .localLedgerAudit
      proofNodeKey := "pnp.v13.locked-core-identity-readout-family"
      status := .blockedByCounterexample
      truthValue := ⟨100, 99⟩
      progressPercent := 100
      itvLowerPercent := 99
      itvUpperPercent := 100
      obligation := "Treat deterministic readout as refuted for the scaled identity-readout locked-core family unless a public-message invariant is supplied." },
    { stage := .localLedgerAudit
      proofNodeKey := "pnp.kpoly-promoted-packet"
      status := .ledgerCovered
      truthValue := ⟨100, 92⟩
      progressPercent := 100
      itvLowerPercent := 92
      itvUpperPercent := 100
      obligation := "Treat local Kpoly coverage as local ledger evidence only." },
    { stage := .localLedgerAudit, proofNodeKey := "pnp.kpoly.feature-route-quantale-boundary", status := .checked, truthValue := ⟨100, 99⟩, progressPercent := 100, itvLowerPercent := 99, itvUpperPercent := 100, obligation := "Treat the shortcut-removal packet as a non-vacuous necessary-condition boundary: the committed singleton/Bool canary inhabits all four obligations, while scaled or global routes still need the same obligations plus separate barrier-world evidence." },
    { stage := .goertzelCalibrationBreak
      proofNodeKey := "pnp.goertzel-calibration-success-domination-break"
      status := .blockedByCounterexample
      truthValue := ⟨100, 98⟩
      progressPercent := 100
      itvLowerPercent := 98
      itvUpperPercent := 100
      obligation := "Treat Ben Goertzel's calibration/success-domination step as refuted as stated: the full post-switch input is not T_i-invariant on nonzero VV columns, and a finite two-point witness separates global exact recovery from every shared-local-input decoder. P vs NP remains open." },
    { stage := .barrierObstruction
      proofNodeKey := "pnp.kpoly-promoted.all-barrier-obstructions"
      status := .barrierBlocked
      truthValue := ⟨100, 99⟩
      progressPercent := 100
      itvLowerPercent := 99
      itvUpperPercent := 100
      obligation := "Do not promote the local Kpoly ledger route; its own promotion gate remains blocked." },
    { stage := .replacementRoute
      proofNodeKey := "pnp.replacement-route.opened-barrier-gate"
      status := .replacementOpened
      truthValue := ⟨100, 99⟩
      progressPercent := 10
      itvLowerPercent := 10
      itvUpperPercent := 15
      obligation := "Replacement route opened at the represented all-three barrier gate; next formalize the global complexity-class interface." },
    { stage := .replacementRoute
      proofNodeKey := "pnp.global-separation"
      status := .openBackground
      truthValue := ⟨0, 99⟩
      progressPercent := 0
      itvLowerPercent := 0
      itvUpperPercent := 1
      obligation := "No final separation theorem is asserted before the global complexity-class interface is formalized." } ]

theorem currentPNPRoadmap_nonempty : currentPNPRoadmap ≠ [] := by
  simp [currentPNPRoadmap]

/-- The current roadmap pins the local ledger before the blocked global
promotion gate and opens only the replacement barrier interface. -/
theorem currentPNPRoadmap_decides_kpoly_barrier_and_opens_replacement :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll ∧
      currentPNPBarrierRouteDecision.barrierGate.ClearsAll ∧
      ({ stage := PNPRoadmapStage.replacementRoute
         proofNodeKey := "pnp.replacement-route.opened-barrier-gate"
         status := .replacementOpened
         truthValue := ⟨100, 99⟩
         progressPercent := 10
         itvLowerPercent := 10
         itvUpperPercent := 15
         obligation :=
          "Replacement route opened at the represented all-three barrier gate; next formalize the global complexity-class interface." } :
        PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  exact
    ⟨(currentPNPKpolyPromotedPacket_stopGrade_and_allBarrierObstructions).1,
      currentPNPKpolyPromotedBarrierPromotionGate_not_cleared,
      (currentPNPBarrierRouteDecision_scope).2.2.2.1,
      by simp [currentPNPRoadmap]⟩

theorem currentPNPRoadmap_orders_local_ledger_before_global_promotion :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll ∧
      ({ stage := PNPRoadmapStage.replacementRoute
         proofNodeKey := "pnp.global-separation"
         status := .openBackground
         truthValue := ⟨0, 99⟩
         progressPercent := 0
         itvLowerPercent := 0
         itvUpperPercent := 1
         obligation :=
          "No final separation theorem is asserted before the global complexity-class interface is formalized." } :
        PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  exact
    ⟨(currentPNPRoadmap_decides_kpoly_barrier_and_opens_replacement).1,
      (currentPNPRoadmap_decides_kpoly_barrier_and_opens_replacement).2.1,
      by simp [currentPNPRoadmap]⟩

end Mettapedia.Computability.PNP
