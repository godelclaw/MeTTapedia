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
  | steelmanConditional
  | coarseProjectionObstruction
  | v13EvidenceSpine
  | v13CDENF
  | v13GaugeBufferedLedger
  | v13ConditionalClash
  | v13FaithfulnessAudit
  | v13PhaseEConcrete
  | v13PhaseEScaled
  | v13RealRungOneLinear
  | v13RealRungOneRowObservers
  | v13ObserverLadder
  | weaknessCalculus
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
    { stage := .steelmanConditional
      proofNodeKey := "pnp.steelman.kernel-flip-no-threading-star-sw-conditional"
      status := .checked
      truthValue := ⟨100, 92⟩
      progressPercent := 100
      itvLowerPercent := 92
      itvUpperPercent := 100
      obligation := "Kernel-flip exact neutrality and no-threading are finite checked facts; the conditional chain is checked only after the explicit StarSWAverageCaseWitnessBitHardness input is supplied. No concentration/log-Sobolev replacement and no final separation are asserted." },
    { stage := .coarseProjectionObstruction
      proofNodeKey := "pnp.coarse-projection-repair-obstruction"
      status := .checked
      truthValue := ⟨100, 93⟩
      progressPercent := 100
      itvLowerPercent := 93
      itvUpperPercent := 100
      obligation := "Coarse-projection domination is checked only as an equivalence to the StarSW half-bound under explicit EnsembleCoarseNeutral; StarSWImpliesSeparation remains a separate open chain input." },
    { stage := .v13EvidenceSpine
      proofNodeKey := "pnp.v13.phase-a.finite-evidence-spine"
      status := .checked
      truthValue := ⟨100, 91⟩
      progressPercent := 100
      itvLowerPercent := 91
      itvUpperPercent := 100
      obligation := "Use the finite gap/capture/telescoping spine as the numeric input to CD-ENF and safe/gauge budget accounting; it is not a concrete ensemble instantiation." },
    { stage := .v13CDENF
      proofNodeKey := "pnp.v13.phase-b.cd-enf-normalization"
      status := .checked
      truthValue := ⟨100, 91⟩
      progressPercent := 100
      itvLowerPercent := 91
      itvUpperPercent := 100
      obligation := "Route observer output through semantics-preserving CD-ENF before any safe/gauge ledger accounting; no opaque observer-output raw atom is available." },
    { stage := .v13GaugeBufferedLedger
      proofNodeKey := "pnp.v13.phase-c.gauge-buffered-ledger"
      status := .checked
      truthValue := ⟨100, 90⟩
      progressPercent := 100
      itvLowerPercent := 90
      itvUpperPercent := 100
      obligation := "Treat the two-point joint toy as evidence that the abstract nine-field ledger is consistent; the concrete ensemble remains out of scope." },
    { stage := .v13ConditionalClash
      proofNodeKey := "pnp.v13.phase-d.conditional-upper-lower-clash"
      status := .checked
      truthValue := ⟨100, 89⟩
      progressPercent := 100
      itvLowerPercent := 89
      itvUpperPercent := 100
      obligation := "Treat `v13_upperLowerClash` as the abstract conditional Phase-D object with lower consequence derived from the compression budget machine and only one named self-reduction upper hypothesis; concrete ensemble parameters remain out of scope." },
    { stage := .v13FaithfulnessAudit
      proofNodeKey := "pnp.v13.faithfulness-audit"
      status := .checked
      truthValue := ⟨100, 88⟩
      progressPercent := 100
      itvLowerPercent := 88
      itvUpperPercent := 100
      obligation := "Carry weaker-than-note audit rows into Phase E as concrete ensemble obligations." },
    { stage := .v13PhaseEConcrete
      proofNodeKey := "pnp.v13.phase-e.small-locked-sat-smoke"
      status := .checked
      truthValue := ⟨100, 86⟩
      progressPercent := 100
      itvLowerPercent := 86
      itvUpperPercent := 100
      obligation := "Treat the small locked-SAT smoke instance as a checked Phase E entry, not as a scaled-ensemble qSSM or boundary-law proof." },
    { stage := .v13PhaseEScaled
      proofNodeKey := "pnp.v13.phase-e.scaled-obligation-map"
      status := .checked
      truthValue := ⟨100, 86⟩
      progressPercent := 100
      itvLowerPercent := 86
      itvUpperPercent := 100
      obligation := "Treat the parameterized Phase E family as inadmissible for the architecture: a single public targetLock coordinate determines the target, so its obligation map is re-tagged familyInadmissible." },
    { stage := .v13RealRungOneLinear
      proofNodeKey := "pnp.v13.real-rung-one.linear-public-surface"
      status := .replacementOpened
      truthValue := ⟨100, 88⟩
      progressPercent := 60
      itvLowerPercent := 88
      itvUpperPercent := 100
      obligation := "Use the certified invertible F2^m public surface `(A, A x)`: full public input decodes the target coordinate, and no elementary coordinate of A, A inverse, or the RHS determines it when a spare coordinate exists. The adaptive q-row bound remains open." },
    { stage := .v13RealRungOneRowObservers
      proofNodeKey := "pnp.v13.real-rung-one.row-observer-hard-core"
      status := .replacementOpened
      truthValue := ⟨100, 89⟩
      progressPercent := 70
      itvLowerPercent := 89
      itvUpperPercent := 100
      obligation := "Use the conditioned row-kernel flip: whenever observed rows do not span-block the target coordinate, opposite-target worlds share the same row transcript. The remaining q-row theorem is exactly the adaptive row-span counting bound, about 2^(q-m)." },
    { stage := .v13ObserverLadder
      proofNodeKey := "pnp.v13.phase-e.observer-ladder-mark"
      status := .checked
      truthValue := ⟨100, 87⟩
      progressPercent := 100
      itvLowerPercent := 87
      itvUpperPercent := 100
      obligation := "Treat the observer ladder mark as checked: unrestricted full-coordinate observers stop at a q=1 public target-lock counterexample; target-blind payload domination is equivalent to the StarSW half-bound, and full random switching is pinned as PhaseEScaledSwitchingStatementNeeded." },
    { stage := .weaknessCalculus
      proofNodeKey := "pnp.weakness-calculus.finite-spectrum-gap"
      status := .checked
      truthValue := ⟨100, 93⟩
      progressPercent := 100
      itvLowerPercent := 93
      itvUpperPercent := 100
      obligation := "Use the finite spectrum/gap, split-budget additive tensor, independent-value tensor, and sequential budget-composition calculus as reusable bookkeeping only; domination remains the explicit StarSW open input and no final separation is asserted." },
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

theorem currentPNPRoadmap_records_pnp_steelman_conditional :
    ({ stage := PNPRoadmapStage.steelmanConditional
       proofNodeKey := "pnp.steelman.kernel-flip-no-threading-star-sw-conditional"
       status := .checked
       truthValue := ⟨100, 92⟩
       progressPercent := 100
       itvLowerPercent := 92
       itvUpperPercent := 100
       obligation :=
        "Kernel-flip exact neutrality and no-threading are finite checked facts; the conditional chain is checked only after the explicit StarSWAverageCaseWitnessBitHardness input is supplied. No concentration/log-Sobolev replacement and no final separation are asserted." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_weakness_calculus :
    ({ stage := PNPRoadmapStage.weaknessCalculus
       proofNodeKey := "pnp.weakness-calculus.finite-spectrum-gap"
       status := .checked
       truthValue := ⟨100, 93⟩
       progressPercent := 100
       itvLowerPercent := 93
       itvUpperPercent := 100
       obligation :=
        "Use the finite spectrum/gap, split-budget additive tensor, independent-value tensor, and sequential budget-composition calculus as reusable bookkeeping only; domination remains the explicit StarSW open input and no final separation is asserted." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_coarse_projection_obstruction :
    ({ stage := PNPRoadmapStage.coarseProjectionObstruction
       proofNodeKey := "pnp.coarse-projection-repair-obstruction"
       status := .checked
       truthValue := ⟨100, 93⟩
       progressPercent := 100
       itvLowerPercent := 93
       itvUpperPercent := 100
       obligation :=
        "Coarse-projection domination is checked only as an equivalence to the StarSW half-bound under explicit EnsembleCoarseNeutral; StarSWImpliesSeparation remains a separate open chain input." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_evidence_spine :
    ({ stage := PNPRoadmapStage.v13EvidenceSpine
       proofNodeKey := "pnp.v13.phase-a.finite-evidence-spine"
       status := .checked
       truthValue := ⟨100, 91⟩
       progressPercent := 100
       itvLowerPercent := 91
       itvUpperPercent := 100
       obligation :=
        "Use the finite gap/capture/telescoping spine as the numeric input to CD-ENF and safe/gauge budget accounting; it is not a concrete ensemble instantiation." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_cd_enf :
    ({ stage := PNPRoadmapStage.v13CDENF
       proofNodeKey := "pnp.v13.phase-b.cd-enf-normalization"
       status := .checked
       truthValue := ⟨100, 91⟩
       progressPercent := 100
       itvLowerPercent := 91
       itvUpperPercent := 100
       obligation :=
        "Route observer output through semantics-preserving CD-ENF before any safe/gauge ledger accounting; no opaque observer-output raw atom is available." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_gauge_buffered_ledger :
    ({ stage := PNPRoadmapStage.v13GaugeBufferedLedger
       proofNodeKey := "pnp.v13.phase-c.gauge-buffered-ledger"
       status := .checked
       truthValue := ⟨100, 90⟩
       progressPercent := 100
       itvLowerPercent := 90
       itvUpperPercent := 100
       obligation :=
        "Treat the two-point joint toy as evidence that the abstract nine-field ledger is consistent; the concrete ensemble remains out of scope." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_conditional_clash :
    ({ stage := PNPRoadmapStage.v13ConditionalClash
       proofNodeKey := "pnp.v13.phase-d.conditional-upper-lower-clash"
       status := .checked
       truthValue := ⟨100, 89⟩
       progressPercent := 100
       itvLowerPercent := 89
       itvUpperPercent := 100
       obligation :=
        "Treat `v13_upperLowerClash` as the abstract conditional Phase-D object with lower consequence derived from the compression budget machine and only one named self-reduction upper hypothesis; concrete ensemble parameters remain out of scope." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_faithfulness_audit :
    ({ stage := PNPRoadmapStage.v13FaithfulnessAudit
       proofNodeKey := "pnp.v13.faithfulness-audit"
       status := .checked
       truthValue := ⟨100, 88⟩
       progressPercent := 100
       itvLowerPercent := 88
       itvUpperPercent := 100
       obligation :=
        "Carry weaker-than-note audit rows into Phase E as concrete ensemble obligations." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_phase_e_concrete :
    ({ stage := PNPRoadmapStage.v13PhaseEConcrete
       proofNodeKey := "pnp.v13.phase-e.small-locked-sat-smoke"
       status := .checked
       truthValue := ⟨100, 86⟩
       progressPercent := 100
       itvLowerPercent := 86
       itvUpperPercent := 100
       obligation :=
        "Treat the small locked-SAT smoke instance as a checked Phase E entry, not as a scaled-ensemble qSSM or boundary-law proof." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_phase_e_scaled :
    ({ stage := PNPRoadmapStage.v13PhaseEScaled
       proofNodeKey := "pnp.v13.phase-e.scaled-obligation-map"
       status := .checked
       truthValue := ⟨100, 86⟩
       progressPercent := 100
       itvLowerPercent := 86
       itvUpperPercent := 100
       obligation :=
        "Treat the parameterized Phase E family as inadmissible for the architecture: a single public targetLock coordinate determines the target, so its obligation map is re-tagged familyInadmissible." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_real_rung_one_linear :
    ({ stage := PNPRoadmapStage.v13RealRungOneLinear
       proofNodeKey := "pnp.v13.real-rung-one.linear-public-surface"
       status := .replacementOpened
       truthValue := ⟨100, 88⟩
       progressPercent := 60
       itvLowerPercent := 88
       itvUpperPercent := 100
       obligation :=
        "Use the certified invertible F2^m public surface `(A, A x)`: full public input decodes the target coordinate, and no elementary coordinate of A, A inverse, or the RHS determines it when a spare coordinate exists. The adaptive q-row bound remains open." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_real_rung_one_row_observers :
    ({ stage := PNPRoadmapStage.v13RealRungOneRowObservers
       proofNodeKey := "pnp.v13.real-rung-one.row-observer-hard-core"
       status := .replacementOpened
       truthValue := ⟨100, 89⟩
       progressPercent := 70
       itvLowerPercent := 89
       itvUpperPercent := 100
       obligation :=
        "Use the conditioned row-kernel flip: whenever observed rows do not span-block the target coordinate, opposite-target worlds share the same row transcript. The remaining q-row theorem is exactly the adaptive row-span counting bound, about 2^(q-m)." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_observer_ladder :
    ({ stage := PNPRoadmapStage.v13ObserverLadder
       proofNodeKey := "pnp.v13.phase-e.observer-ladder-mark"
       status := .checked
       truthValue := ⟨100, 87⟩
       progressPercent := 100
       itvLowerPercent := 87
       itvUpperPercent := 100
       obligation :=
        "Treat the observer ladder mark as checked: unrestricted full-coordinate observers stop at a q=1 public target-lock counterexample; target-blind payload domination is equivalent to the StarSW half-bound, and full random switching is pinned as PhaseEScaledSwitchingStatementNeeded." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

end Mettapedia.Computability.PNP
