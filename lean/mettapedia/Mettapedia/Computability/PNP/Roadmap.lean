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
  | v13RealRungOneAdaptiveRows
  | v13RealRungOneLinear
  | v13RealRungOneQRowBound
  | v13RealRungOneRowObservers
  | v13RealRungOneStaticRows
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
      obligation := "Use the certified invertible F2^m public surface `(A, A x)`: full public input decodes the target coordinate, and no elementary coordinate of A, A inverse, or the RHS determines it when a spare coordinate exists; the checked package is V13RealLinearPublicSurfaceCertificate." },
    { stage := .v13RealRungOneLinear
      proofNodeKey := "pnp.v13.real-rung-one.square-gl-rhs-balance-obstruction"
      status := .checked
      truthValue := ⟨100, 97⟩
      progressPercent := 100
      itvLowerPercent := 97
      itvUpperPercent := 100
      obligation := "Record the dimension-two square-GL obstruction: the RHS coordinate fiber `b0 = 0` has unequal target-bit counts, so exact coordinate-balance admissibility requires a changed sampler or a different formal statement." },
    { stage := .v13RealRungOneLinear
      proofNodeKey := "pnp.v13.real-rung-one.no-target-rows-rhs-balance"
      status := .replacementOpened
      truthValue := ⟨100, 91⟩
      progressPercent := 72
      itvLowerPercent := 91
      itvUpperPercent := 100
      obligation := "Use the no-target-row sampler condition: if no public row functional is exactly the target coordinate, every fixed RHS coordinate fiber is target-bit balanced by adding a row-kernel vector with target bit one." },
    { stage := .v13RealRungOneLinear
      proofNodeKey := "pnp.v13.real-rung-one.no-target-rows-public-surface"
      status := .replacementOpened
      truthValue := ⟨100, 92⟩
      progressPercent := 78
      itvLowerPercent := 92
      itvUpperPercent := 100
      obligation := "Package the adjusted no-target-row sampler surface: full public input still decodes and determines the target, and every elementary public coordinate has exactly balanced target-bit fibers." },
    { stage := .v13RealRungOneRowObservers
      proofNodeKey := "pnp.v13.real-rung-one.row-observer-hard-core"
      status := .replacementOpened
      truthValue := ⟨100, 89⟩
      progressPercent := 70
      itvLowerPercent := 89
      itvUpperPercent := 100
      obligation := "Use the conditioned row-kernel flip: whenever observed rows do not span-block the target coordinate, opposite-target worlds share the same row transcript. The remaining q-row theorem is exactly the adaptive row-span counting bound, about 2^(q-m)." },
    { stage := .v13RealRungOneStaticRows
      proofNodeKey := "pnp.v13.real-rung-one.static-row-exact-half"
      status := .replacementOpened
      truthValue := ⟨100, 90⟩
      progressPercent := 75
      itvLowerPercent := 90
      itvUpperPercent := 100
      obligation := "Use the fixed-branch theorem: any static row observer whose rows do not block the target has exactly paired correct and incorrect hidden witnesses by kernel flip. The remaining q-row theorem is the adaptive row-span counting lift." },
    { stage := .v13RealRungOneAdaptiveRows
      proofNodeKey := "pnp.v13.real-rung-one.adaptive-branch-exact-half"
      status := .replacementOpened
      truthValue := ⟨100, 91⟩
      progressPercent := 80
      itvLowerPercent := 91
      itvUpperPercent := 100
      obligation := "Use the adaptive branch-stability theorem: every realized non-blocked adaptive branch has paired correct and incorrect hidden witnesses. The remaining q-row theorem is the row-span counting bound for blocked branches." },
    { stage := .v13RealRungOneQRowBound
      proofNodeKey := "pnp.v13.real-rung-one.qrow-bound-assembly"
      status := .openBackground
      truthValue := ⟨100, 98⟩
      progressPercent := 98
      itvLowerPercent := 98
      itvUpperPercent := 100
      obligation := "Assemble the explicit q-row success bound for the uniform certified-invertible sampler: the proved kernel-flip surcharge, row-combination space bound, block-iff-generate characterization, blocked/generated mass equality, closed zero-row plus high-budget cases, and target-row chooser mass equality identifies q = 1 exactly with uniform target-row occurrence mass. The proved two-dimensional GL2(F2) count bound turns the full-map branch-interface obstruction unconditional. The active theorem surface is the causal row-query interface: zero-row and high-budget cases are closed, the low-positive row-span mass bound is formally equivalent to the division-free completion count, and the all-q theorem follows from either equivalent form. The coefficient-counting pin V13RealLinearUniformCausalLowPositiveCoefficientCountingBound remains a stronger sufficient route into that count. The naive pointwise fixed-map fiber strengthening V13RealLinearUniformCausalLowPositiveFiberCoefficientCountingBound is formally refuted in the two-dimensional identity case. Constant one-row causal observers are now closed in all dimensions: a zero-at-coordinate transvection injection proves V13RealLinearUniformFixedTargetRowOccurrenceCountingBound and hence its representative form, which now feeds generated-world completion count, row-span count, and q = 1 success directly. Arbitrary one-row generated worlds now inject into a row-indexed fixed-row occurrence world, giving a proved row-factor bound. Generated one-row causal branches are now localized to generated cylinders: their row set is exactly a singleton target row, and every world with the same singleton row transcript is generated on the same target row. Fixed target-row plus fixed RHS-bit cylinders now satisfy the sharp one-cylinder count `card cylinder * 2^m <= card worlds`, and arbitrary one-row generated worlds are now charged by the finite active row-bit cylinder index. The exact q = 1 row/bit sub-obligation is `V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound`; it now conditionally feeds both the one-row row-span bound and the q = 1 success bound. The sharper sufficient hard core is `V13RealLinearUniformCausalOneRowActiveRowIndexBound`, equivalently `V13RealLinearUniformCausalOneRowActiveRowPairExclusion`: any two active generated target rows for the same causal one-row observer must be the same row, and either form conditionally feeds the same row-span and success consequences. The GL2 no-target maps `v13RealLinearSwapShear10` and `v13RealLinearShear01` are now recorded as finite rest-world witnesses for the pair-exclusion route at targets 0 and 1 respectively; neither can be generated under the corresponding one-row causal target, their branch rows split into the empty, row-0, or row-1 cases, and the empty plus both mismatched active/rest singleton cases are excluded. These are bundled into quantified dimension-two theorems over every `i₀ : Fin 2`, feeding the active row/bit bound, generated-world completion count, row-span mass bound, and q = 1 success bound for arbitrary target coordinate in dimension 2. In every dimension `m > 1`, `v13RealLinearNoTargetRowShear` now supplies an explicit invertible no-target rest map by shearing the target output row with a spare coordinate. The no-target rest world is never generated, and once any active generated singleton exists, causality now also excludes the empty branch for every rest world and forces every q = 1 rest branch, including this no-target rest branch, to be a singleton. The all-dimensional bridge is now isolated as `V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion`: for every active generated singleton row `r`, the no-target rest branch cannot be a different singleton `{s}`. This single mismatch exclusion theorem conditionally proves active-row pair exclusion, active row/bit index bounds, generated-world counting, row-span mass, and q = 1 success. The causal part of that bridge is now factored out: `v13RealLinearUniformCausalOneRow_restActiveSingleton_collision_of_bridge` proves that any bridge world matching the rest singleton transcript and active singleton transcript forces a row collision, and `v13RealLinearNoTargetRowShear_branchRows_ne_of_activeRowIndex_of_bridgeFamily` reduces the no-target mismatch statement to constructing such bridge worlds for active witnesses. The no-target rest row functional is now explicitly separated from the target coordinate and from every active target-row functional by `v13RealLinearNoTargetRowShear_rowFunctional_ne_target` and `v13RealLinearNoTargetRowShear_rowFunctional_ne_activeTarget`. Singleton transcript matching is now factored into row-functional and RHS-bit matching by `v13RealLinearRowsTranscript_singleton_eq_of_row_match`, with the no-target bridge conjunction packaged by `v13RealLinearNoTargetRowShear_bridgeTranscripts_of_row_matches`. The RHS-vector half of that bridge is now explicit: `v13RealLinearNoTargetRowShear_exists_bridgeX_for_row_target_bits` realizes any requested no-target rest-row RHS bit together with any target-coordinate bit. The derived reduction `v13RealLinearNoTargetRowShear_branchRows_ne_of_activeRowIndex_of_bridgeMapFamily` now combines the bridge-map functional hypothesis with the RHS-vector solver and transcript factoring, so the bridge-family route has no remaining RHS obligation. The matching bridge map construction is now proved in all dimensions by `v13RealLinearNoTargetRowShear_exists_bridgeMap_for_rows`; the hard case `restRow = i₀` uses `v13RealLinearNoTargetHardBridgeMap`, and the remaining cases use identity/permutation maps. This closes `V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion_proved`, making active-row pair exclusion, active row/bit bounds, generated-world counting, one-row row-span mass, and q = 1 success unconditional for every `m > 1`. The q = 1 closure now residualizes the low-positive interval: the exact remaining hard cores are named `V13RealLinearUniformCausalTwoOrMoreRowSpanCountingBound`, `V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound`, and the stronger sufficient `V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound`. The low-positive row-span and completion statements are equivalent to their two-or-more residual forms, the residual coefficient form is equivalent to the compressed average-per-map bound `V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound`, and that compression is equivalent to the fixed-map fiber-average form `V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound`; that fiber-average form is equivalent to the target-coefficient fiber average `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound`, which exposes each fixed-map fiber as hidden vectors carrying rowset-local target coefficients; that form is further equivalent to the realized-rowset double sum `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound`, avoiding any finiteness assumption on abstract causal branches; each rowset cell now factors exactly into hidden-vector rowset-fiber count times rowset-local target-coefficient count, yielding the product hard core `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound`; over-budget rowsets have empty hidden-vector fibers, so this is equivalent to the budgeted-rowset product hard core `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound`; each budgeted rowset fiber now splits exactly by the finite observed row transcript, yielding the transcript-indexed hard core `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetTranscriptProductAverageBound`; the product factor is now exposed as `V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetTranscriptProductCell`, with cardinal equation `v13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetTranscriptProductCell_card_eq_product` and rowset-product sum equation `v13RealLinearAdaptiveQRow_rowsetProduct_eq_sum_transcriptProductCells`; within any such transcript cell the causal branch is branch-local by `v13RealLinearUniformCausal_rowsetTranscriptCell_branch_eq`, the causal decision is decision-local by `v13RealLinearUniformCausal_rowsetTranscriptCell_decision_eq`, every transcript product-cell element is generated by `v13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetTranscriptProductCell_generated`, and product-cell correctness is all-or-none by `v13RealLinearUniformCausal_rowsetTranscriptProductCell_correctCard_eq_zero_or_card`; the equivalent product-cell average hard core is `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetTranscriptProductCellAverageBound`; these coefficient/product forms feed residual completion directly. It is enough to prove arbitrary causal q-row branch accounting for `1 < q` and `q < m` in one of these forms." },
    { stage := .v13RealRungOneQRowBound
      proofNodeKey := "pnp.v13.real-rung-one.sequential-qrow-transfer"
      status := .checked
      truthValue := ⟨100, 96⟩
      progressPercent := 100
      itvLowerPercent := 96
      itvUpperPercent := 100
      obligation := "Record the sequential adaptive row-query theorem: every sequential q-row observer over the uniform certified-invertible sampler has success at most 1/2 + 4*(2^q - 1)/2^m. The broader causal interface remains tracked by the row-span hard-core entry." },
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
        "Use the certified invertible F2^m public surface `(A, A x)`: full public input decodes the target coordinate, and no elementary coordinate of A, A inverse, or the RHS determines it when a spare coordinate exists; the checked package is V13RealLinearPublicSurfaceCertificate." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_real_rung_one_square_gl_rhs_balance_obstruction :
    ({ stage := PNPRoadmapStage.v13RealRungOneLinear
       proofNodeKey := "pnp.v13.real-rung-one.square-gl-rhs-balance-obstruction"
       status := .checked
       truthValue := ⟨100, 97⟩
       progressPercent := 100
       itvLowerPercent := 97
       itvUpperPercent := 100
       obligation :=
        "Record the dimension-two square-GL obstruction: the RHS coordinate fiber `b0 = 0` has unequal target-bit counts, so exact coordinate-balance admissibility requires a changed sampler or a different formal statement." } :
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

theorem currentPNPRoadmap_records_v13_real_rung_one_static_rows :
    ({ stage := PNPRoadmapStage.v13RealRungOneStaticRows
       proofNodeKey := "pnp.v13.real-rung-one.static-row-exact-half"
       status := .replacementOpened
       truthValue := ⟨100, 90⟩
       progressPercent := 75
       itvLowerPercent := 90
       itvUpperPercent := 100
       obligation :=
        "Use the fixed-branch theorem: any static row observer whose rows do not block the target has exactly paired correct and incorrect hidden witnesses by kernel flip. The remaining q-row theorem is the adaptive row-span counting lift." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_real_rung_one_adaptive_rows :
    ({ stage := PNPRoadmapStage.v13RealRungOneAdaptiveRows
       proofNodeKey := "pnp.v13.real-rung-one.adaptive-branch-exact-half"
       status := .replacementOpened
       truthValue := ⟨100, 91⟩
       progressPercent := 80
       itvLowerPercent := 91
       itvUpperPercent := 100
       obligation :=
        "Use the adaptive branch-stability theorem: every realized non-blocked adaptive branch has paired correct and incorrect hidden witnesses. The remaining q-row theorem is the row-span counting bound for blocked branches." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_real_rung_one_qrow_bound :
    ({ stage := PNPRoadmapStage.v13RealRungOneQRowBound
       proofNodeKey := "pnp.v13.real-rung-one.qrow-bound-assembly"
       status := .openBackground
       truthValue := ⟨100, 98⟩
       progressPercent := 98
       itvLowerPercent := 98
       itvUpperPercent := 100
       obligation :=
        "Assemble the explicit q-row success bound for the uniform certified-invertible sampler: the proved kernel-flip surcharge, row-combination space bound, block-iff-generate characterization, blocked/generated mass equality, closed zero-row plus high-budget cases, and target-row chooser mass equality identifies q = 1 exactly with uniform target-row occurrence mass. The proved two-dimensional GL2(F2) count bound turns the full-map branch-interface obstruction unconditional. The active theorem surface is the causal row-query interface: zero-row and high-budget cases are closed, the low-positive row-span mass bound is formally equivalent to the division-free completion count, and the all-q theorem follows from either equivalent form. The coefficient-counting pin V13RealLinearUniformCausalLowPositiveCoefficientCountingBound remains a stronger sufficient route into that count. The naive pointwise fixed-map fiber strengthening V13RealLinearUniformCausalLowPositiveFiberCoefficientCountingBound is formally refuted in the two-dimensional identity case. Constant one-row causal observers are now closed in all dimensions: a zero-at-coordinate transvection injection proves V13RealLinearUniformFixedTargetRowOccurrenceCountingBound and hence its representative form, which now feeds generated-world completion count, row-span count, and q = 1 success directly. Arbitrary one-row generated worlds now inject into a row-indexed fixed-row occurrence world, giving a proved row-factor bound. Generated one-row causal branches are now localized to generated cylinders: their row set is exactly a singleton target row, and every world with the same singleton row transcript is generated on the same target row. Fixed target-row plus fixed RHS-bit cylinders now satisfy the sharp one-cylinder count `card cylinder * 2^m <= card worlds`, and arbitrary one-row generated worlds are now charged by the finite active row-bit cylinder index. The exact q = 1 row/bit sub-obligation is `V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound`; it now conditionally feeds both the one-row row-span bound and the q = 1 success bound. The sharper sufficient hard core is `V13RealLinearUniformCausalOneRowActiveRowIndexBound`, equivalently `V13RealLinearUniformCausalOneRowActiveRowPairExclusion`: any two active generated target rows for the same causal one-row observer must be the same row, and either form conditionally feeds the same row-span and success consequences. The GL2 no-target maps `v13RealLinearSwapShear10` and `v13RealLinearShear01` are now recorded as finite rest-world witnesses for the pair-exclusion route at targets 0 and 1 respectively; neither can be generated under the corresponding one-row causal target, their branch rows split into the empty, row-0, or row-1 cases, and the empty plus both mismatched active/rest singleton cases are excluded. These are bundled into quantified dimension-two theorems over every `i₀ : Fin 2`, feeding the active row/bit bound, generated-world completion count, row-span mass bound, and q = 1 success bound for arbitrary target coordinate in dimension 2. In every dimension `m > 1`, `v13RealLinearNoTargetRowShear` now supplies an explicit invertible no-target rest map by shearing the target output row with a spare coordinate. The no-target rest world is never generated, and once any active generated singleton exists, causality now also excludes the empty branch for every rest world and forces every q = 1 rest branch, including this no-target rest branch, to be a singleton. The all-dimensional bridge is now isolated as `V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion`: for every active generated singleton row `r`, the no-target rest branch cannot be a different singleton `{s}`. This single mismatch exclusion theorem conditionally proves active-row pair exclusion, active row/bit index bounds, generated-world counting, row-span mass, and q = 1 success. The causal part of that bridge is now factored out: `v13RealLinearUniformCausalOneRow_restActiveSingleton_collision_of_bridge` proves that any bridge world matching the rest singleton transcript and active singleton transcript forces a row collision, and `v13RealLinearNoTargetRowShear_branchRows_ne_of_activeRowIndex_of_bridgeFamily` reduces the no-target mismatch statement to constructing such bridge worlds for active witnesses. The no-target rest row functional is now explicitly separated from the target coordinate and from every active target-row functional by `v13RealLinearNoTargetRowShear_rowFunctional_ne_target` and `v13RealLinearNoTargetRowShear_rowFunctional_ne_activeTarget`. Singleton transcript matching is now factored into row-functional and RHS-bit matching by `v13RealLinearRowsTranscript_singleton_eq_of_row_match`, with the no-target bridge conjunction packaged by `v13RealLinearNoTargetRowShear_bridgeTranscripts_of_row_matches`. The RHS-vector half of that bridge is now explicit: `v13RealLinearNoTargetRowShear_exists_bridgeX_for_row_target_bits` realizes any requested no-target rest-row RHS bit together with any target-coordinate bit. The derived reduction `v13RealLinearNoTargetRowShear_branchRows_ne_of_activeRowIndex_of_bridgeMapFamily` now combines the bridge-map functional hypothesis with the RHS-vector solver and transcript factoring, so the bridge-family route has no remaining RHS obligation. The matching bridge map construction is now proved in all dimensions by `v13RealLinearNoTargetRowShear_exists_bridgeMap_for_rows`; the hard case `restRow = i₀` uses `v13RealLinearNoTargetHardBridgeMap`, and the remaining cases use identity/permutation maps. This closes `V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion_proved`, making active-row pair exclusion, active row/bit bounds, generated-world counting, one-row row-span mass, and q = 1 success unconditional for every `m > 1`. The q = 1 closure now residualizes the low-positive interval: the exact remaining hard cores are named `V13RealLinearUniformCausalTwoOrMoreRowSpanCountingBound`, `V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound`, and the stronger sufficient `V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound`. The low-positive row-span and completion statements are equivalent to their two-or-more residual forms, the residual coefficient form is equivalent to the compressed average-per-map bound `V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound`, and that compression is equivalent to the fixed-map fiber-average form `V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound`; that fiber-average form is equivalent to the target-coefficient fiber average `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound`, which exposes each fixed-map fiber as hidden vectors carrying rowset-local target coefficients; that form is further equivalent to the realized-rowset double sum `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound`, avoiding any finiteness assumption on abstract causal branches; each rowset cell now factors exactly into hidden-vector rowset-fiber count times rowset-local target-coefficient count, yielding the product hard core `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound`; over-budget rowsets have empty hidden-vector fibers, so this is equivalent to the budgeted-rowset product hard core `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound`; each budgeted rowset fiber now splits exactly by the finite observed row transcript, yielding the transcript-indexed hard core `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetTranscriptProductAverageBound`; the product factor is now exposed as `V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetTranscriptProductCell`, with cardinal equation `v13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetTranscriptProductCell_card_eq_product` and rowset-product sum equation `v13RealLinearAdaptiveQRow_rowsetProduct_eq_sum_transcriptProductCells`; within any such transcript cell the causal branch is branch-local by `v13RealLinearUniformCausal_rowsetTranscriptCell_branch_eq`, the causal decision is decision-local by `v13RealLinearUniformCausal_rowsetTranscriptCell_decision_eq`, every transcript product-cell element is generated by `v13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetTranscriptProductCell_generated`, and product-cell correctness is all-or-none by `v13RealLinearUniformCausal_rowsetTranscriptProductCell_correctCard_eq_zero_or_card`; the equivalent product-cell average hard core is `V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetTranscriptProductCellAverageBound`; these coefficient/product forms feed residual completion directly. It is enough to prove arbitrary causal q-row branch accounting for `1 < q` and `q < m` in one of these forms." } :
      PNPRoadmapEntry) ∈ currentPNPRoadmap := by
  simp [currentPNPRoadmap]

theorem currentPNPRoadmap_records_v13_real_rung_one_sequential_qrow_transfer :
    ({ stage := PNPRoadmapStage.v13RealRungOneQRowBound
       proofNodeKey := "pnp.v13.real-rung-one.sequential-qrow-transfer"
       status := .checked
       truthValue := ⟨100, 96⟩
       progressPercent := 100
       itvLowerPercent := 96
       itvUpperPercent := 100
       obligation :=
        "Record the sequential adaptive row-query theorem: every sequential q-row observer over the uniform certified-invertible sampler has success at most 1/2 + 4*(2^q - 1)/2^m. The broader causal interface remains tracked by the row-span hard-core entry." } :
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
