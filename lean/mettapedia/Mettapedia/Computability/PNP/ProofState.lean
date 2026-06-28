import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryConcentrationObstruction
import Mettapedia.Computability.PNP.ClockedKpolyActualGapClosure
import Mettapedia.Computability.PNP.CruxKpolyBridgeCurrentStatus
import Mettapedia.Computability.PNP.CruxKpolyPromotedPacket
import Mettapedia.Computability.PNP.CruxSynthesisRegression
import Mettapedia.Computability.PNP.KpolyPolynomialFunctorAgreementObstruction
import Mettapedia.Computability.PNP.KpolyQuantaleShortcutRemovalCanary
import Mettapedia.Computability.PNP.Barriers.ProperSubsetLabCanaries
import Mettapedia.Computability.PNP.PNPv13AtomicBudgetLedgerAuditorCanaries
import Mettapedia.Computability.PNP.PNPv13CDENFNormalizerCanaries
import Mettapedia.Computability.PNP.PNPv13FiniteGibbsDobrushinCanaries
import Mettapedia.Computability.PNP.PNPv13LockedCoreLabCanaries
import Mettapedia.Computability.PNP.PNPv13SwitchedHistoryProductAuditorCanaries
import Mettapedia.Computability.PNP.PNPv13TraceFactorizationCanaries
import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListStructuralObstructionExactZAB
/-!
# PNP proof state

This module records the current public proof-state surface for the PNP lane.
The entries below are bookkeeping data: `truthValue.supportPercent` means
current formal support for the named node, not a claim about the Millennium
problem itself.
-/
namespace Mettapedia.Computability.PNP
/-- Coarse status tags for public proof-state bookkeeping. -/
inductive PNPProofNodeStatus where
  | surveyed
  | checked
  | repaired
  | ledgerCovered
  | blockedByCounterexample
  | barrierBlocked
  | barrierUncleared
  | openBackground
deriving DecidableEq, Repr

/-- Source-survey counts for the active PNP lane. -/
structure PNPLaneSurveyCounts where
  sourceFiles : Nat
  sourceLines : Nat
  internalImportEdges : Nat
  regressionFiles : Nat
  filesOverSevenHundredFiftyLines : Nat
  zeroInternalImporterEntrypoints : Nat
  noDeclarationCompatibilityHubs : Nat
deriving Repr

/-- Current source-map summary for `Mettapedia/Computability/PNP`. -/
def currentPNPLaneSurveyCounts : PNPLaneSurveyCounts where
  sourceFiles := 947
  sourceLines := 125417
  internalImportEdges := 2291
  regressionFiles := 294
  filesOverSevenHundredFiftyLines := 0
  zeroInternalImporterEntrypoints := 256
  noDeclarationCompatibilityHubs := 126

/-- Simple PLN-style truth bookkeeping: support and confidence percentages. -/
structure SimpleTruthValue where
  supportPercent : Nat
  confidencePercent : Nat
deriving Repr

/-- A public node in the PNP proof-state ledger. -/
structure PNPProofNode where
  key : String
  status : PNPProofNodeStatus
  truthValue : SimpleTruthValue
  evidence : String
  nextObligation : String
deriving Repr

/-- Current public proof-state nodes for the PNP lane. -/
def currentPNPProofNodes : List PNPProofNode := [
  {
    key := "pnp.map.current-lane",
    status := .surveyed,
    truthValue := ⟨100, 94⟩,
    evidence := "The lane currently has 947 Lean files, 125417 lines, 2291 internal import edges, and no files over the split threshold.",
    nextObligation := "Keep broad regression files separate from the live entrypoint unless a checked theorem needs them."
  },
  {
    key := "pnp.crux-synthesis.current-honest-status",
    status := .checked,
    truthValue := ⟨100, 96⟩,
    evidence := "CruxSynthesis is a compatibility import over the current live crux status; currentPNPStrongestHonestStatus_local_gap_marker records clocked finite-uniform coverage while the local packet still leaves the kpoly compression bridge uncovered and is not stop-grade.",
    nextObligation := "Treat the promoted Kpoly packet as a local ledger closure only; global promotion remains blocked by the separate barrier nodes."
  },
  {
    key := "pnp.local-packet.current-status",
    status := .checked,
    truthValue := ⟨100, 93⟩,
    evidence := "currentPNPStrongestHonestStatus records covered local items and the still-uncovered kpoly compression bridge for the current local packet.",
    nextObligation := "Continue distinguishing ledger coverage from a global complexity separation."
  },
  {
    key := "pnp.v13.locked-core-lab-canaries",
    status := .blockedByCounterexample,
    truthValue := ⟨100, 97⟩,
    evidence := "ambiguousAppendixDLockedCore_lab_negative_canary proves that lock satisfiability and deterministic per-state readout do not imply locked-message rigidity; rigidAppendixDLockedCore_lab_positive_canary records the bounded public-message invariant canary.",
    nextObligation := "Do not replace Appendix D.8 locked-message rigidity by deterministic readout; require a public-message invariant or an equivalent cross-completion rigidity theorem before SAT-search promotion."
  },
  {
    key := "pnp.v13.locked-core-public-message-invariant",
    status := .blockedByCounterexample,
    truthValue := ⟨100, 99⟩,
    evidence := "lockedCorePublicMessageInvariant_bool_guardrails records the finite lab gate: a public-message invariant clears the rigid canary, while deterministic readout with a cross-completion ambiguity blocks the gate and refutes the invariant.",
    nextObligation := "Treat public-message invariance, or an equivalent cross-completion theorem, as a real missing hypothesis before promoting the locked-core readout route."
  },
  { key := "pnp.v13.locked-core-identity-readout-family",
    status := .blockedByCounterexample, truthValue := ⟨100, 99⟩,
    evidence := "lockedCoreIdentityReadoutFamily_lab_refutation proves that every positive finite identity-readout locked-core dimension is satisfiable and read-deterministic, while every public-message invariant and D.8 locked-message rigidity fail.",
    nextObligation := "Do not try to derive Appendix D.8 from local satisfiability plus deterministic readout; a replacement route must supply a public-message invariant or a stronger cross-completion theorem."
  },
  {
    key := "pnp.v13.cd-enf-normalizer-canaries",
    status := .blockedByCounterexample,
    truthValue := ⟨100, 97⟩,
    evidence := "cdenfNormalizer_lab_positive_canary clears the finite target Neutral/Safe/Gauge canary, while cdenfNormalizer_lab_negative_canary reports one target-relevant Residual leaf with raw atom, source, and branch context.",
    nextObligation := "Do not treat CD evidence normalization as closed until every target-relevant raw leaf normalizes to Neutral, Safe, or Gauge and the residual report list is empty."
  },
  {
    key := "pnp.v13.atomic-budget-ledger-auditor-canaries",
    status := .blockedByCounterexample,
    truthValue := ⟨100, 97⟩,
    evidence := "atomicBudgetLedger_lab_positive_canary clears the finite structural stack, while the negative canaries expose overcharging, undercharging, scalar equality by cancellation, stale gauge use, incidence overflow, and safe-budget overflow.",
    nextObligation := "Do not replace structural atomic accounting by scalar equality; require NoDoubleCounting, AllPositiveCostAtomsCharged, FreshGaugeOnly, BoundedIncidence, and SafeBudget together."
  },
  {
    key := "pnp.v13.trace-factorization-canaries",
    status := .blockedByCounterexample,
    truthValue := ⟨100, 97⟩,
    evidence := "traceFactorizationIdentitySurface_lab_positive_canary clears the distinct-trace toy surface, while the negative canaries show that trace assignment alone, same-trace observer conflicts, and one random coin-slice conflict block trace factorization.",
    nextObligation := "Do not replace trace factorization by an opaque trace assignment; require named observers to be constant on target-relevant trace fibers, with the same check for every random coin slice."
  },
  {
    key := "pnp.v13.switched-history-product-auditor-canaries",
    status := .blockedByCounterexample,
    truthValue := ⟨100, 97⟩,
    evidence := "switchedHistoryConditionalProduct_lab_positive_canary clears the finite prefix-relative product canary, while the negative canaries show that global averages and product success alone do not clear the switched-history/Kpoly gates.",
    nextObligation := "Do not replace conditional sequential product hypotheses by global averages, and do not replace a finite-image theorem by product-success evidence alone."
  },
  {
    key := "pnp.v13.finite-gibbs-dobrushin-canaries",
    status := .blockedByCounterexample,
    truthValue := ⟨100, 97⟩,
    evidence := "finiteGibbsDobrushinStrictContraction_lab_positive_canary clears a strict max-row contraction toy matrix, while the negative canaries show that average influence, critical equality, and sampled-row evidence do not clear the full Dobrushin/qSSM gate.",
    nextObligation := "Do not promote finite Gibbs boundary-law mixing claims unless the explicit max-qSSM row constant is strictly below scale for every row."
  },
  {
    key := "pnp.kpoly-promoted-packet",
    status := .ledgerCovered,
    truthValue := ⟨100, 92⟩,
    evidence := "currentPNPKpolyCompressionBridgePromotedStatus and stopGrade_currentPNPKpolyCompressionBridgePromotedPacket build after the repair pass.",
    nextObligation := "Audit whether each promoted coverage component has a nonlocal complexity-class interpretation."
  },
  {
    key := "pnp.kpoly-bridge.coverage-core",
    status := .blockedByCounterexample,
    truthValue := ⟨100, 97⟩,
    evidence := "currentPNPKpolyCompressionBridgeCoverage_refutation_packet records that clocked Kpoly payload is exactly finite predictor-image cover, while empty product-bound-only and fielded-switching bridge schemas are refuted below the exact-visible surface threshold.",
    nextObligation := "Treat the promoted Kpoly bridge as a route refutation unless a new bridge supplies a stronger finite-cover theorem rather than product-bound or fielded-switching-only evidence."
  },
  { key := "pnp.kpoly.polynomial-functor-agreement", status := .blockedByCounterexample, truthValue := ⟨100, 99⟩, evidence := "polynomialFunctorSmallImageAgreement_obstruction_packet proves that a one-shape finite polynomial-container image and its two-code bit family do not force any strict pure-atom bad-code agreement bound.", nextObligation := "Do not derive Kpoly recovery or quantale weakness bounds from polynomial small-image evidence alone; require a separate support-disagreement or agreement-mass theorem." },
  { key := "pnp.kpoly.feature-route-quantale-boundary", status := .checked, truthValue := ⟨100, 99⟩, evidence := "kpolyQuantaleShortcutRemovalRoute_nonempty and kpolyQuantaleShortcutRemoval_positive_canary_packet prove a concrete singleton exact-visible and Bool-weakness inhabitant satisfying all four route obligations; kpolyQuantaleShortcutRemoval_obstruction_packet is therefore a non-vacuous necessary-condition boundary for this route class, not a global separation claim.", nextObligation := "Scale or replace the canary only with routes that satisfy all four obligations together; keep barrier-world and positive escape-witness obligations separate before any global promotion." },
  {
    key := "pnp.kpoly-promoted.barrier-clearance",
    status := .barrierBlocked,
    truthValue := ⟨100, 99⟩,
    evidence := "currentPNPKpolyPromotedPacket_stopGrade_and_allBarriersBlocked records that the Kpoly-promoted packet is locally stop-grade while relativization, natural-proof, and algebrization all block the current route shape; currentPNPKpolyPromotedPacket_stopGrade_and_worldInterface_packet records that the route supplies no barrier-world interfaces; currentPNPKpolyPromotedPacket_stopGrade_and_escapeWitness_packet records that it also supplies no positive escape witnesses; currentPNPKpolyPromotedPacket_stopGrade_and_promotionGate_refuted records the combined promotion-gate failure.",
    nextObligation := "Do not promote the local Kpoly packet as a global route unless a new route shape clears the barrier verdict, challenge-world interface, and positive escape-witness layers together."
  },
  {
    key := "pnp.kpoly-promoted.promotion-gate",
    status := .barrierBlocked,
    truthValue := ⟨100, 99⟩,
    evidence := "currentPNPKpolyPromotedPacket_stopGrade_and_promotionGate_refuted records that the local stop-grade packet fails all three global-promotion layers: barrier verdicts, challenge-world interfaces, and positive escape witnesses.",
    nextObligation := "Require any replacement route to clear all three promotion-gate layers before it is treated as a candidate global separation route."
  },
  {
    key := "pnp.kpoly-promoted.escape-witness",
    status := .barrierUncleared,
    truthValue := ⟨100, 99⟩,
    evidence := "currentPNPKpolyPromotedPacket_stopGrade_and_escapeWitness_packet records that the current route is locally stop-grade but lacks nonrelativizing oracle-separation, non-natural property-escape, and non-algebrizing algebraic-oracle-separation witnesses.",
    nextObligation := "Treat any replacement global route as uncleared until it represents the positive witness family required by each barrier."
  },
  {
    key := "pnp.kpoly-promoted.relativization",
    status := .barrierBlocked,
    truthValue := ⟨100, 98⟩,
    evidence := "currentPNPKpolyPromotedPacket_stopGrade_and_relativizationBlocked proves the current local-ledger route shape lacks the oracle challenge-world generator required to clear relativization.",
    nextObligation := "Do not promote the local Kpoly packet as a global route unless a new route shape supplies the oracle-world interface."
  },
  {
    key := "pnp.kpoly-promoted.relativization-obstruction",
    status := .barrierBlocked,
    truthValue := ⟨100, 99⟩,
    evidence := "currentPNPKpolyPromotedPacket_stopGrade_and_relativizationObstruction records that the local stop-grade Kpoly packet has no oracle challenge-world generator and no represented nonrelativizing oracle-separation witness.",
    nextObligation := "A replacement PNP route must supply both the oracle-world interface and the positive nonrelativizing escape witness before the relativization barrier can be treated as cleared."
  },
  {
    key := "pnp.kpoly-promoted.natural-proof",
    status := .barrierBlocked,
    truthValue := ⟨100, 98⟩,
    evidence := "currentPNPKpolyPromotedPacket_stopGrade_and_naturalProofBlocked proves the current local-ledger route shape lacks the pseudorandom-world sampler and non-naturalness interface required to clear natural proofs.",
    nextObligation := "Do not promote the local Kpoly packet as a global route unless a new route shape supplies the natural-proof challenge-world and escape-certificate interface."
  },
  {
    key := "pnp.kpoly-promoted.natural-proof-obstruction",
    status := .barrierBlocked,
    truthValue := ⟨100, 99⟩,
    evidence := "currentPNPKpolyPromotedPacket_stopGrade_and_naturalProofObstruction records that the local stop-grade Kpoly packet supplies no pseudorandom challenge-world sampler, no constructivity/largeness/usefulness audit, no non-natural escape certificate, and no represented non-natural property escape witness.",
    nextObligation := "A replacement PNP route must supply the pseudorandom-world interface, the natural-proof audit, and a positive non-natural escape witness before the natural-proofs barrier can be treated as cleared."
  },
  {
    key := "pnp.kpoly-promoted.algebrization",
    status := .barrierBlocked,
    truthValue := ⟨100, 98⟩,
    evidence := "currentPNPKpolyPromotedPacket_stopGrade_and_algebrizationBlocked proves the current local-ledger route shape lacks the algebraic-oracle generator and algebraic-lift interface required to clear algebrization.",
    nextObligation := "Do not promote the local Kpoly packet as a global route unless a new route shape supplies the algebraic-oracle and lift interface."
  },
  {
    key := "pnp.kpoly-promoted.algebrization-obstruction",
    status := .barrierBlocked,
    truthValue := ⟨100, 99⟩,
    evidence := "currentPNPKpolyPromotedPacket_stopGrade_and_algebrizationObstruction records that the local stop-grade Kpoly packet supplies no algebraic-oracle challenge-world generator, no algebraic lift interface, no algebraic-oracle invariant separation claim, and no represented non-algebrizing algebraic-oracle separation witness.",
    nextObligation := "A replacement PNP route must supply the algebraic-oracle world interface, the lift interface, the lifted invariant separation claim, and a positive non-algebrizing escape witness before algebrization can be treated as cleared."
  },
  {
    key := "pnp.kpoly-promoted.all-barrier-obstructions",
    status := .barrierBlocked,
    truthValue := ⟨100, 99⟩,
    evidence := "currentPNPKpolyPromotedPacket_stopGrade_and_allBarrierObstructions consolidates the detailed relativization, natural-proof, and algebrization obstruction packets, while currentPNPKpolyPromotedBarrierPromotionGate_not_cleared keeps the combined promotion gate refuted.",
    nextObligation := "Do not continue this local Kpoly packet as a global route; begin a replacement route only if it supplies all three barrier-world interfaces and positive escape witnesses."
  },
  {
    key := "pnp.replacement-route.promotion-gate-obligations",
    status := .checked,
    truthValue := ⟨100, 94⟩,
    evidence := "PNPBarrierPromotionGate.clearsAll_requires_replacement_obligations proves that any gate-clearing replacement route must have cleared verdicts for all three barriers, supply every required barrier-world interface, and represent every required positive escape witness.",
    nextObligation := "Use this generic gate theorem as the entry condition for any future replacement route before advertising it as a candidate global separation route."
  },
  {
    key := "pnp.replacement-route.relativization-only-boundary",
    status := .barrierBlocked,
    truthValue := ⟨100, 95⟩,
    evidence := "currentPNPRelativizationOnlyCandidate_clears_relativization_but_not_promotion proves that a candidate with the relativization interfaces and witness represented still fails promotion when natural-proof and algebrization obligations are not represented.",
    nextObligation := "A replacement route that represents the oracle layer must next represent the natural-proof and algebrization layers before it can be tested as a global candidate."
  },
  {
    key := "pnp.replacement-route.natural-proof-only-boundary",
    status := .barrierBlocked,
    truthValue := ⟨100, 95⟩,
    evidence := "currentPNPNaturalProofOnlyCandidate_clears_naturalProof_but_not_promotion proves that a candidate with the natural-proof interfaces and witness represented still fails promotion when relativization and algebrization obligations are not represented.",
    nextObligation := "A replacement route that represents the natural-proof layer must next represent the relativization and algebrization layers before it can be tested as a global candidate."
  },
  {
    key := "pnp.replacement-route.algebrization-only-boundary",
    status := .barrierBlocked,
    truthValue := ⟨100, 95⟩,
    evidence := "currentPNPAlgebrizationOnlyCandidate_clears_algebrization_but_not_promotion proves that a candidate with the algebrization interfaces and witness represented still fails promotion when relativization and natural-proof obligations are not represented.",
    nextObligation := "A replacement route that represents the algebrization layer must next represent the relativization and natural-proof layers before it can be tested as a global candidate."
  },
  {
    key := "pnp.replacement-route.one-barrier-frontier",
    status := .barrierBlocked,
    truthValue := ⟨100, 95⟩,
    evidence := "currentPNPOneBarrierCandidatePromotionGates_all_fail_promotion proves that the three one-barrier candidate gates all fail global promotion.",
    nextObligation := "Do not treat one represented barrier layer as sufficient for global promotion."
  },
  {
    key := "pnp.replacement-route.two-barrier-frontier",
    status := .barrierBlocked,
    truthValue := ⟨100, 96⟩,
    evidence := "currentPNPTwoBarrierCandidatePromotionGates_all_fail_promotion proves that the three two-barrier candidate gates all fail global promotion; currentPNPTwoBarrierFrontier_all_double_layer_clearances_fail_promotion records the represented barrier pairs.",
    nextObligation := "A replacement route must represent all three barrier layers before it can be tested as a globally promoted PNP route."
  },
  {
    key := "pnp.replacement-route.proper-subset-frontier",
    status := .barrierBlocked,
    truthValue := ⟨100, 97⟩,
    evidence := "currentPNPProperSubsetBarrierCandidatePromotionGates_all_fail_promotion proves that the six current one- and two-barrier candidate gates all fail global promotion; currentPNPProperSubsetBarrierFrontier_all_strict_subsets_fail_promotion records every current strict-subset clearance case.",
    nextObligation := "Do not test a replacement route as global until it represents all three barrier layers at the verdict, world-interface, and escape-witness levels."
  },
  {
    key := "pnp.replacement-route.barrier-subset-lab-canaries",
    status := .barrierBlocked,
    truthValue := ⟨100, 98⟩,
    evidence := "pnpBarrierSubsetFrontierCanaries_guardrails records the finite lab-backed Boolean gate: a toy all-three-barrier route clears, every proper subset of the barrier layers fails promotion, and the current local Kpoly promotion gate remains blocked.",
    nextObligation := "Do not begin a replacement global route unless the finite lab and Lean gate both show all three barrier layers represented."
  },
  {
    key := "pnp.replacement-route.promotion-layer-omissions",
    status := .barrierBlocked,
    truthValue := ⟨100, 98⟩,
    evidence := "pnpBarrierPromotionLayerOmissions_guardrails records that verdict-only, world-interface-only, witness-only, and every two-layer omission shape all fail the finite global-promotion gate.",
    nextObligation := "Do not replace the three-layer PNP barrier gate by verdict clearance, challenge-world interfaces, or escape witnesses in isolation."
  },
  {
    key := "pnp.exact-visible.bare-interface",
    status := .blockedByCounterexample,
    truthValue := ⟨100, 95⟩,
    evidence := "currentExactVisibleInterface_not_forall_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard refutes the bare exact-visible interface below full visible surface size.",
    nextObligation := "Avoid using the bare exact-visible interface as a compression bridge without extra structure."
  },
  {
    key := "pnp.exact-zab.decision-list-transport",
    status := .repaired,
    truthValue := ⟨100, 92⟩,
    evidence := "not_injective_exactZABAffineDecisionListSignature_id_of_one_lt and the full-rule nonrealization corollary now build through the identity exact-ZAB visible-data transport.",
    nextObligation := "Use this obstruction to separate decision-list transport from stronger sparse-threshold liveness."
  },
  {
    key := "pnp.sparse-threshold.surjective-concentration",
    status := .repaired,
    truthValue := ⟨100, 91⟩,
    evidence := "half_le_of_surjective_predict_of_exists_ne now builds and shows surjective recovery packets on nontrivial visible surfaces force q at least one half.",
    nextObligation := "Propagate the concentration obstruction only through recovery packets that actually provide the required surjectivity or injective-region hypotheses."
  },
  {
    key := "pnp.global-separation",
    status := .openBackground,
    truthValue := ⟨0, 99⟩,
    evidence := "The live PNP surface is a route audit; it does not assert a final P versus NP separation theorem.",
    nextObligation := "Formalize the missing global complexity-class interface and barrier checks before introducing any final separation statement."
  },
  {
    key := "pnp.barrier-checks",
    status := .barrierBlocked,
    truthValue := ⟨0, 99⟩,
    evidence := "currentPNPKpolyPromotedBarrierStatus_missingEvidenceBarriers is empty, currentPNPKpolyPromotedPacket_stopGrade_and_allBarriersBlocked records all three barrier families as blocked for the current local-ledger route shape, currentPNPKpolyPromotedPacket_stopGrade_and_worldInterface_packet lists the missing barrier-world interfaces, currentPNPKpolyPromotedPacket_stopGrade_and_escapeWitness_packet records that the positive escape-witness ledger is empty, and currentPNPKpolyPromotedPacket_stopGrade_and_promotionGate_refuted combines those blockers into a failed promotion gate.",
    nextObligation := "Start a different global-route shape only if it clears the barrier verdicts, challenge-world interfaces, and positive escape witnesses before any separation endpoint is advertised."
  }
]
theorem currentPNPStrongestHonestStatus_local_gap_marker :
    currentPNPLocalCruxPacket.covers .clockedFiniteUniformKernel ∧
      ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge ∧
      ¬ currentPNPLocalCruxPacket.StopGrade := by
  exact
    ⟨clockedFiniteUniformKernel_covered_currentPNPLocalCruxPacket,
      kpolyCompressionBridge_uncovered_currentPNPLocalCruxPacket,
      not_stopGrade_currentPNPLocalCruxPacket⟩

theorem currentPNPKpolyBridgeCoverageCore_node_refutation_packet :
    currentPNPKpolyCompressionBridgePromotedPacket.covers .kpolyCompressionBridge ∧
      (∀ {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
        {G : ExactVisibleSwitchedFamily Z k Index},
          ClockedKpolyFiniteLearningPayload G s clock ↔
            G.FinitePredictorCover (2 ^ s)) ∧
      (∀ {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s clock : ℕ},
        s < Fintype.card (ExactVisiblePostSwitchSurface Z k) →
          ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
              Ω Z k s clock
              ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω))) ∧
      (∀ {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s clock : ℕ},
        s < Fintype.card (ExactVisiblePostSwitchSurface Z k) →
          ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
              Ω Z k s clock
              ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω))) := by
  exact
    ⟨kpolyCompressionBridge_covered_currentPNPKpolyCompressionBridgePromotedPacket,
      currentPNPKpolyCompressionBridgeCoverage_refutation_packet⟩

theorem currentPNPv13LockedCoreLabCanaries_node :
    (rigidAppendixDLockedCore.LockSatisfiable ∧
      rigidAppendixDLockedCore.ReadDeterministic ∧
      rigidAppendixDLockedCore.LockedMessageRigidity) ∧
      (ambiguousAppendixDLockedCore.LockSatisfiable ∧
        ambiguousAppendixDLockedCore.ReadDeterministic ∧
        ¬ ambiguousAppendixDLockedCore.LockedMessageRigidity) := by
  exact
    ⟨rigidAppendixDLockedCore_lab_positive_canary,
      ambiguousAppendixDLockedCore_lab_negative_canary⟩

theorem currentPNPv13LockedCorePublicMessageInvariant_node :
    lockedCoreRigidPublicMessageInvariantAudit.clearsPublicMessageInvariantGate =
        true ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.deterministicReadoutOnlyCounterexample =
        true ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.clearsPublicMessageInvariantGate =
        false ∧
      lockedCoreAmbiguousDeterministicReadoutAudit.blocksPublicMessageInvariant =
        true := by
  exact lockedCorePublicMessageInvariant_bool_guardrails

theorem currentPNPv13LockedCoreIdentityReadoutFamily_node (n : Nat) :
    (identityReadoutAppendixDLockedCoreFinSucc n).LockSatisfiable ∧
      (identityReadoutAppendixDLockedCoreFinSucc n).ReadDeterministic ∧
      (∀ publicMessage : Unit → Fin (n + 1) → Bool, ¬
        (identityReadoutAppendixDLockedCoreFinSucc n).PublicMessageInvariant publicMessage) ∧
      ¬ (identityReadoutAppendixDLockedCoreFinSucc n).LockedMessageRigidity := by
  exact lockedCoreIdentityReadoutFamily_lab_refutation n

theorem currentPNPv13CDENFNormalizerCanaries_node :
    CDENFAllTargetRelevantLeavesInAllowedClasses cdenfPositiveCanaryLeaves ∧
      CDENFResidualReports cdenfPositiveCanaryLeaves = [] ∧
      CDENFResidualReports cdenfNegativeCanaryLeaves =
        [cdenfTargetResidualReport] ∧
      ¬ CDENFAllTargetRelevantLeavesInAllowedClasses
        cdenfNegativeCanaryLeaves := by
  rcases cdenfNormalizer_lab_positive_canary with ⟨hclear, hreports⟩
  rcases cdenfNormalizer_lab_negative_canary with ⟨hresidual, hblocked⟩
  exact ⟨hclear, hreports, hresidual, hblocked⟩

theorem currentPNPv13AtomicBudgetLedgerAuditorCanaries_node :
    atomicBudgetGoodLedger.ClearsAllStructuralChecks ∧
      ¬ atomicBudgetOverchargeLedger.NoDoubleCounting ∧
      ¬ atomicBudgetUnderchargeLedger.AllPositiveCostAtomsCharged ∧
      ¬ atomicBudgetCancellationLedger.ClearsAllStructuralChecks ∧
      ¬ atomicBudgetStaleGaugeLedger.FreshGaugeOnly ∧
      ¬ atomicBudgetIncidenceOverflowLedger.BoundedIncidence ∧
      ¬ atomicBudgetSafeBudgetOverflowLedger.SafeBudget := by
  exact
    ⟨atomicBudgetLedger_lab_positive_canary.1,
      atomicBudgetLedger_overcharge_negative_canary.2.2.2,
      atomicBudgetLedger_undercharge_negative_canary.2.2,
      atomicBudgetLedger_cancellation_negative_canary.2.2.2.2,
      atomicBudgetLedger_staleGauge_negative_canary.2,
      atomicBudgetLedger_incidence_negative_canary.2,
      atomicBudgetLedger_safeBudget_negative_canary.2⟩

theorem currentPNPv13TraceFactorizationCanaries_node :
    traceFactorizationIdentitySurface.CapturesAllBoolObservers ∧
      traceFactorizationIdentitySurface.ObserverTraceDecodable
        traceFactorizationSeparatingObserver ∧
      ¬ traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationSeparatingObserver ∧
      traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationConstantObserver ∧
      ¬ traceFactorizationCollapsedSurface.RandomObserverTraceDecodable
        traceFactorizationRandomSeparatingObserver := by
  exact
    ⟨traceFactorizationIdentitySurface_lab_positive_canary.1,
      traceFactorizationIdentitySurface_lab_positive_canary.2.1,
      traceFactorizationCollapsed_conflictingObserver_negative_canary.2,
      traceFactorizationCollapsed_constantObserver_guard_canary.1,
      traceFactorizationCollapsed_randomCoin_negative_canary.2⟩

theorem currentPNPv13SwitchedHistoryProductAuditorCanaries_node :
    switchedHistoryConditionalProductAudit.clearsSequentialProductGate = true ∧
      switchedHistoryGlobalAverageOnlyAudit.allGlobalHalfClears = true ∧
      switchedHistoryGlobalAverageOnlyAudit.allConditionalHalfClears = false ∧
      switchedHistoryRepeatedStepAudit.clearsSequentialProductGate = false ∧
      switchedHistoryProductSuccessOnlyAudit.productSuccessClears = true ∧
      switchedHistoryProductSuccessOnlyAudit.clearsFiniteImageGate = false := by
  exact
    ⟨switchedHistoryConditionalProduct_lab_positive_canary.2.2,
      switchedHistoryGlobalAverageOnly_negative_canary.1,
      switchedHistoryGlobalAverageOnly_negative_canary.2.1,
      switchedHistoryProductAuditorCanaries_guardrails.2.2.2.1,
      switchedHistoryProductSuccessOnly_negative_canary.1,
      switchedHistoryProductSuccessOnly_negative_canary.2.2⟩

theorem currentPNPv13FiniteGibbsDobrushinCanaries_node :
    finiteGibbsDobrushinStrictContractionAudit.strictMaxRowContractionClears = true ∧
      finiteGibbsDobrushinStrictContractionAudit.maxQSSMConstantScaled = 35 ∧
      finiteGibbsDobrushinAverageOnlyAudit.averageRowMassClears = true ∧
      finiteGibbsDobrushinAverageOnlyAudit.strictMaxRowContractionClears = false ∧
      finiteGibbsDobrushinEqualityAudit.nonStrictMaxRowBoundClears = true ∧
      finiteGibbsDobrushinEqualityAudit.strictMaxRowContractionClears = false ∧
      finiteGibbsDobrushinSampledRowsAudit.sampledRowsStrictBelow = true ∧
      finiteGibbsDobrushinSampledRowsAudit.strictMaxRowContractionClears = false := by
  exact
    ⟨finiteGibbsDobrushinStrictContraction_lab_positive_canary.2.2.1,
      finiteGibbsDobrushinStrictContraction_lab_positive_canary.2.1,
      finiteGibbsDobrushinAverageOnly_negative_canary.1,
      finiteGibbsDobrushinAverageOnly_negative_canary.2.2.1,
      finiteGibbsDobrushinEquality_negative_canary.1,
      finiteGibbsDobrushinEquality_negative_canary.2.2.1,
      finiteGibbsDobrushinSampledRows_negative_canary.1,
      finiteGibbsDobrushinSampledRows_negative_canary.2.2.2⟩

theorem currentPNPBarrierPromotionLayerOmissions_node :
    pnpBarrierPromotionVerdictsOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionWorldInterfacesOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionEscapeWitnessesOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionVerdictsWorldsNoEscapesCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionVerdictsEscapesNoWorldsCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionWorldsEscapesNoVerdictsCanaryAudit.clearsGlobalPromotionGate =
        false := by
  exact pnpBarrierPromotionLayerOmissions_guardrails

theorem currentPNPKpolyPromotedRelativizationObstruction_node :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.relativization = .blocked ∧
      ¬ currentPNPKpolyPromotedRelativizationRouteShape.Clears ∧
      PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .relativization ∧
      ¬ PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .relativization ∧
      ¬ PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_relativizationObstruction

theorem currentPNPKpolyPromotedNaturalProofObstruction_node :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.naturalProof = .blocked ∧
      ¬ currentPNPKpolyPromotedNaturalProofRouteShape.Clears ∧
      PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
      ¬ PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
      ¬ PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
      ¬ PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .naturalProof ∧
      ¬ PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_naturalProofObstruction

theorem currentPNPKpolyPromotedAlgebrizationObstruction_node :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.algebrization = .blocked ∧
      ¬ currentPNPKpolyPromotedAlgebrizationRouteShape.Clears ∧
      PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
      ¬ PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierWorldInterface.algebraicLiftInterface ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
      ¬ PNPBarrierWorldInterface.algebraicLiftInterface ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
      ¬ PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .algebrization ∧
      ¬ PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_algebrizationObstruction

theorem currentPNPKpolyPromotedAllBarrierObstructions_node :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      (currentPNPKpolyPromotedBarrierStatus.relativization = .blocked ∧
        ¬ currentPNPKpolyPromotedRelativizationRouteShape.Clears ∧
        PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .relativization ∧
        ¬ PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .relativization ∧
        ¬ PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.represented) ∧
      (currentPNPKpolyPromotedBarrierStatus.naturalProof = .blocked ∧
        ¬ currentPNPKpolyPromotedNaturalProofRouteShape.Clears ∧
        PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
        ¬ PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
        ¬ PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
        ¬ PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .naturalProof ∧
        ¬ PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.represented) ∧
      (currentPNPKpolyPromotedBarrierStatus.algebrization = .blocked ∧
        ¬ currentPNPKpolyPromotedAlgebrizationRouteShape.Clears ∧
        PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
        ¬ PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierWorldInterface.algebraicLiftInterface ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
        ¬ PNPBarrierWorldInterface.algebraicLiftInterface ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
        ¬ PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .algebrization ∧
        ¬ PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.represented) ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_allBarrierObstructions

theorem currentPNPReplacementGateObligations_node :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      (∀ {gate : PNPBarrierPromotionGate},
        gate.ClearsAll →
          (gate.status.relativization = .cleared ∧
            gate.status.naturalProof = .cleared ∧
            gate.status.algebrization = .cleared) ∧
          (∀ {kind : PNPBarrierKind} {requirement : PNPBarrierWorldInterface},
            requirement ∈ kind.requiredWorldInterfaces →
              requirement ∈ gate.worldInterfaces.supplied) ∧
          (∀ {kind : PNPBarrierKind} {witness : PNPBarrierEscapeWitness},
            witness ∈ kind.requiredEscapeWitnesses →
              witness ∈ gate.escapeLedger.represented)) ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_replacement_gate_obligations

theorem currentPNPRelativizationOnlyBoundary_node :
    currentPNPRelativizationOnlyBarrierStatus.relativization = .cleared ∧
      currentPNPRelativizationOnlyWorldInterfaces.missingFor .relativization = [] ∧
      currentPNPRelativizationOnlyEscapeLedger.missingFor .relativization = [] ∧
      currentPNPRelativizationOnlyBarrierStatus.naturalProof = .notRepresented ∧
      currentPNPRelativizationOnlyWorldInterfaces.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredWorldInterfaces ∧
      currentPNPRelativizationOnlyEscapeLedger.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredEscapeWitnesses ∧
      currentPNPRelativizationOnlyBarrierStatus.algebrization = .notRepresented ∧
      currentPNPRelativizationOnlyWorldInterfaces.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredWorldInterfaces ∧
      currentPNPRelativizationOnlyEscapeLedger.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredEscapeWitnesses ∧
      ¬ currentPNPRelativizationOnlyPromotionGate.ClearsAll := by
  exact currentPNPRelativizationOnlyCandidate_clears_relativization_but_not_promotion

theorem currentPNPNaturalProofOnlyBoundary_node :
    currentPNPNaturalProofOnlyBarrierStatus.relativization = .notRepresented ∧
      currentPNPNaturalProofOnlyWorldInterfaces.missingFor .relativization =
        PNPBarrierKind.relativization.requiredWorldInterfaces ∧
      currentPNPNaturalProofOnlyEscapeLedger.missingFor .relativization =
        PNPBarrierKind.relativization.requiredEscapeWitnesses ∧
      currentPNPNaturalProofOnlyBarrierStatus.naturalProof = .cleared ∧
      currentPNPNaturalProofOnlyWorldInterfaces.missingFor .naturalProof = [] ∧
      currentPNPNaturalProofOnlyEscapeLedger.missingFor .naturalProof = [] ∧
      currentPNPNaturalProofOnlyBarrierStatus.algebrization = .notRepresented ∧
      currentPNPNaturalProofOnlyWorldInterfaces.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredWorldInterfaces ∧
      currentPNPNaturalProofOnlyEscapeLedger.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredEscapeWitnesses ∧
      ¬ currentPNPNaturalProofOnlyPromotionGate.ClearsAll := by
  exact currentPNPNaturalProofOnlyCandidate_clears_naturalProof_but_not_promotion

theorem currentPNPAlgebrizationOnlyBoundary_node :
    currentPNPAlgebrizationOnlyBarrierStatus.relativization = .notRepresented ∧
      currentPNPAlgebrizationOnlyWorldInterfaces.missingFor .relativization =
        PNPBarrierKind.relativization.requiredWorldInterfaces ∧
      currentPNPAlgebrizationOnlyEscapeLedger.missingFor .relativization =
        PNPBarrierKind.relativization.requiredEscapeWitnesses ∧
      currentPNPAlgebrizationOnlyBarrierStatus.naturalProof = .notRepresented ∧
      currentPNPAlgebrizationOnlyWorldInterfaces.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredWorldInterfaces ∧
      currentPNPAlgebrizationOnlyEscapeLedger.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredEscapeWitnesses ∧
      currentPNPAlgebrizationOnlyBarrierStatus.algebrization = .cleared ∧
      currentPNPAlgebrizationOnlyWorldInterfaces.missingFor .algebrization = [] ∧
      currentPNPAlgebrizationOnlyEscapeLedger.missingFor .algebrization = [] ∧
      ¬ currentPNPAlgebrizationOnlyPromotionGate.ClearsAll := by
  exact currentPNPAlgebrizationOnlyCandidate_clears_algebrization_but_not_promotion

theorem currentPNPOneBarrierFrontier_node :
    currentPNPOneBarrierCandidatePromotionGates.length = 3 ∧
      (∀ gate ∈ currentPNPOneBarrierCandidatePromotionGates,
        ¬ gate.ClearsAll) ∧
      (currentPNPRelativizationOnlyBarrierStatus.relativization = .cleared ∧
        ¬ currentPNPRelativizationOnlyPromotionGate.ClearsAll) ∧
      (currentPNPNaturalProofOnlyBarrierStatus.naturalProof = .cleared ∧
        ¬ currentPNPNaturalProofOnlyPromotionGate.ClearsAll) ∧
      (currentPNPAlgebrizationOnlyBarrierStatus.algebrization = .cleared ∧
        ¬ currentPNPAlgebrizationOnlyPromotionGate.ClearsAll) := by
  exact
    ⟨(currentPNPOneBarrierCandidatePromotionGates_length_and_all_fail_promotion).1,
      (currentPNPOneBarrierCandidatePromotionGates_length_and_all_fail_promotion).2,
      currentPNPOneBarrierFrontier_all_single_layer_clearances_fail_promotion⟩

theorem currentPNPTwoBarrierFrontier_node :
    currentPNPTwoBarrierCandidatePromotionGates.length = 3 ∧
      (∀ gate ∈ currentPNPTwoBarrierCandidatePromotionGates,
        ¬ gate.ClearsAll) ∧
      (currentPNPRelativizationNaturalProofBarrierStatus.relativization =
          .cleared ∧
        currentPNPRelativizationNaturalProofBarrierStatus.naturalProof =
          .cleared ∧
        ¬ currentPNPRelativizationNaturalProofPromotionGate.ClearsAll) ∧
      (currentPNPRelativizationAlgebrizationBarrierStatus.relativization =
          .cleared ∧
        currentPNPRelativizationAlgebrizationBarrierStatus.algebrization =
          .cleared ∧
        ¬ currentPNPRelativizationAlgebrizationPromotionGate.ClearsAll) ∧
      (currentPNPNaturalProofAlgebrizationBarrierStatus.naturalProof =
          .cleared ∧
        currentPNPNaturalProofAlgebrizationBarrierStatus.algebrization =
          .cleared ∧
        ¬ currentPNPNaturalProofAlgebrizationPromotionGate.ClearsAll) := by
  exact
    ⟨(currentPNPTwoBarrierCandidatePromotionGates_length_and_all_fail_promotion).1,
      (currentPNPTwoBarrierCandidatePromotionGates_length_and_all_fail_promotion).2,
      currentPNPTwoBarrierFrontier_all_double_layer_clearances_fail_promotion⟩

theorem currentPNPProperSubsetBarrierFrontier_node :
    currentPNPOneBarrierCandidatePromotionGates.length = 3 ∧
      currentPNPTwoBarrierCandidatePromotionGates.length = 3 ∧
      currentPNPProperSubsetBarrierCandidatePromotionGates.length = 6 ∧
      (∀ gate ∈ currentPNPProperSubsetBarrierCandidatePromotionGates,
        ¬ gate.ClearsAll) ∧
      (currentPNPRelativizationOnlyBarrierStatus.relativization = .cleared ∧
        ¬ currentPNPRelativizationOnlyPromotionGate.ClearsAll) ∧
      (currentPNPNaturalProofOnlyBarrierStatus.naturalProof = .cleared ∧
        ¬ currentPNPNaturalProofOnlyPromotionGate.ClearsAll) ∧
      (currentPNPAlgebrizationOnlyBarrierStatus.algebrization = .cleared ∧
        ¬ currentPNPAlgebrizationOnlyPromotionGate.ClearsAll) ∧
      (currentPNPRelativizationNaturalProofBarrierStatus.relativization =
          .cleared ∧
        currentPNPRelativizationNaturalProofBarrierStatus.naturalProof =
          .cleared ∧
        ¬ currentPNPRelativizationNaturalProofPromotionGate.ClearsAll) ∧
      (currentPNPRelativizationAlgebrizationBarrierStatus.relativization =
          .cleared ∧
        currentPNPRelativizationAlgebrizationBarrierStatus.algebrization =
          .cleared ∧
        ¬ currentPNPRelativizationAlgebrizationPromotionGate.ClearsAll) ∧
      (currentPNPNaturalProofAlgebrizationBarrierStatus.naturalProof =
          .cleared ∧
        currentPNPNaturalProofAlgebrizationBarrierStatus.algebrization =
          .cleared ∧
        ¬ currentPNPNaturalProofAlgebrizationPromotionGate.ClearsAll) := by
  exact currentPNPProperSubsetBarrierFrontier_all_strict_subsets_fail_promotion

theorem currentPNPBarrierSubsetFrontierLabCanaries_node :
    pnpBarrierSubsetAllThreeCanaryAudit.clearsGlobalPromotionGate = true ∧
      pnpBarrierSubsetCurrentLocalLedgerCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetRelativizationOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetNaturalProofOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetAlgebrizationOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetRelativizationNaturalProofCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetRelativizationAlgebrizationCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetNaturalProofAlgebrizationCanaryAudit.clearsGlobalPromotionGate =
        false := by
  exact pnpBarrierSubsetFrontierCanaries_guardrails
end Mettapedia.Computability.PNP
