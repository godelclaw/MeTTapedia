import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryConcentrationObstruction
import Mettapedia.Computability.PNP.ClockedKpolyActualGapClosure
import Mettapedia.Computability.PNP.CruxKpolyBridgeCurrentStatus
import Mettapedia.Computability.PNP.CruxKpolyPromotedPacket
import Mettapedia.Computability.PNP.CruxSynthesisRegression
import Mettapedia.Computability.PNP.CoarseProjectionObstruction
import Mettapedia.Computability.PNP.KpolyPolynomialFunctorAgreementObstruction
import Mettapedia.Computability.PNP.KpolyQuantaleShortcutRemovalCanary
import Mettapedia.Computability.PNP.Barriers.ReplacementOpened
import Mettapedia.Computability.PNP.PNPv13AtomicBudgetLedgerAuditorCanaries
import Mettapedia.Computability.PNP.PNPv13CDENFNormalizerCanaries
import Mettapedia.Computability.PNP.PNPv13FiniteGibbsDobrushinCanaries
import Mettapedia.Computability.PNP.PNPv13LockedCoreLabCanaries
import Mettapedia.Computability.PNP.PNPv13SwitchedHistoryProductAuditorCanaries
import Mettapedia.Computability.PNP.PNPv13TraceFactorizationCanaries
import Mettapedia.Computability.PNP.PNPSteelmanConditional
import Mettapedia.Computability.PNP.PostSwitchInputObstruction
import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListStructuralObstructionExactZAB
import Mettapedia.Computability.PNP.V13CDENF
import Mettapedia.Computability.PNP.V13ConditionalClash
import Mettapedia.Computability.PNP.V13EvidenceSpine
import Mettapedia.Computability.PNP.V13FaithfulnessAudit
import Mettapedia.Computability.PNP.V13GaugeBufferedLockedInterface
import Mettapedia.Computability.PNP.V13ObserverLadder
import Mettapedia.Computability.PNP.V13PhaseEConcrete
import Mettapedia.Computability.PNP.V13PhaseEScaled
import Mettapedia.Computability.PNP.V13RealRungOneAdaptiveRows
import Mettapedia.Computability.PNP.V13RealRungOneLinear
import Mettapedia.Computability.PNP.V13RealRungOneQRowBound
import Mettapedia.Computability.PNP.V13RealRungOneRowObservers
import Mettapedia.Computability.PNP.V13RealRungOneStaticRows
import Mettapedia.Computability.PNP.WeaknessCalculus
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
  | replacementOpened
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
  sourceFiles := 948
  sourceLines := 125688
  internalImportEdges := 2294
  regressionFiles := 295
  filesOverSevenHundredFiftyLines := 2
  zeroInternalImporterEntrypoints := 256
  noDeclarationCompatibilityHubs := 128

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
    evidence := "The lane currently has 948 Lean files, 125688 lines, 2294 internal import edges, and two files over the split threshold.",
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
    key := "pnp.goertzel-calibration-success-domination-break",
    status := .blockedByCounterexample,
    truthValue := ⟨100, 98⟩,
    evidence := "calibrationFullInputPreservation_fails_of_nonzeroColumn proves that the post-switch involution preserves only `(z,a)` while changing `b` and the full `(z,a,b)` input on every nonzero VV column. finite_successDomination_counterexample proves a two-point finite local/global domination counterexample: the global decoder succeeds on both full instances, while every decoder depending only on the shared local input succeeds on at most one. Lab pnp-calibration-success-domination-break-lab-20260630.json tabulates the parity-USAT/VV instance where all nonzero columns move `b`, global exact success is 1, best local bit success is 1/2, and best local exact success falls as 2^(1-m).",
    nextObligation := "Do not use Ben Goertzel's A.17 calibration or Proposition A.5 success-domination step as stated; any replacement must condition on an actually invariant input or supply a new domination theorem that survives global decoders."
  },
  {
    key := "pnp.steelman.kernel-flip-no-threading-star-sw-conditional",
    status := .checked,
    truthValue := ⟨100, 92⟩,
    evidence := "KernelFlipInvolution proves the finite ZMod 2 kernel-flip pairing `kernelFlip_exactNeutrality_card`, with `toyKernelFlip_exactNeutrality_card` as an inhabited model. NoThreadingLemma proves `noThreading_neutral_sufficient_blocks_nontrivial_bit`, showing a neutral local statistic cannot also be sufficient for a nontrivial deterministic witness bit. PNPSteelmanConditional proves `pnp_steelman_conditional`: KernelFlipNeutrality plus the explicit open StarSWAverageCaseWitnessBitHardness input implies the abstract PNP endpoint through the non-SW chain.",
    nextObligation := "The exact remaining input is StarSWAverageCaseWitnessBitHardness for Ben's masked isolated ensemble; no concentration/log-Sobolev replacement and no unconditional separation is asserted by this node."
  },
  {
    key := "pnp.coarse-projection-repair-obstruction",
    status := .checked,
    truthValue := ⟨100, 93⟩,
    evidence := "CoarseProjectionObstruction proves `uCoarse_comp_T` and `uFull_T_moves_at`, the neutral-interface half-bound theorem `bestLocalSuccess_eq_half_of_neutral`, the domination equivalence `coarseDominationAll_iff_starSW_of_neutral`, the two-point failure `coarseProjectionToy_not_dominates`, the no-threading instance `coarseProjectionToy_not_sufficient`, and the conditional `coarseProjectionRepair_obstruction_conditional` with explicit hypotheses `EnsembleCoarseNeutral` and `StarSWImpliesSeparation`.",
    nextObligation := "Do not treat the coarse `(z,a_i)` repair as an unconditional domination theorem: on a neutral interface it is exactly the StarSW half-bound, and neutrality on Ben's ensemble plus StarSW-to-separation remain open hypotheses."
  },
  {
    key := "pnp.v13.phase-a.finite-evidence-spine",
    status := .checked,
    truthValue := ⟨100, 91⟩,
    evidence := "V13EvidenceSpine defines finite rational laws, conditional target gaps, static pairwise-capture certificates, derivative-telescoping certificates, and the combined `phaseA_gap_le_half_derivative_sum`; `toyV13_phaseA_gap_le_half_derivative_sum` gives a two-point inhabited model.",
    nextObligation := "Feed the finite derivative sum through CD-ENF safe/gauge normalization rather than treating observer output as an opaque atom."
  },
  {
    key := "pnp.v13.phase-b.cd-enf-normalization",
    status := .checked,
    truthValue := ⟨100, 91⟩,
    evidence := "V13CDENF defines RawEvidence without observer-output atoms, NormalEvidence with exactly neutral/safe/gauge leaf constructors, proves `CDENF_semantics`, and routes observers through `observerToEvidence_sat` plus `observerToCDENF_sat`; the toy observer interface inhabits the discipline.",
    nextObligation := "Use the normalized safe/gauge leaves as the ledger surface for Phase C, including the joint nine-field inhabitation test."
  },
  {
    key := "pnp.v13.phase-c.gauge-buffered-ledger",
    status := .checked,
    truthValue := ⟨100, 90⟩,
    evidence := "V13GaugeBufferedLockedInterface packages the nine ledger fields as propositions over Phase A/B objects and proves red-team coherence theorems for admissible histories, boundary mixing, and neutral skeleton non-sufficiency. `toyLockedInterface_jointly_inhabits_all_nine` checks that a two-point toy jointly inhabits all nine fields.",
    nextObligation := "Use every ledger field explicitly in the Phase D conditional upper/lower clash record; any unused field is an architectural finding."
  },
  {
    key := "pnp.v13.phase-d.conditional-upper-lower-clash",
    status := .checked,
    truthValue := ⟨100, 89⟩,
    evidence := "V13ConditionalClash defines `ParameterRecord`, `LedgerFieldUseCertificate`, and `UpperLowerClash`; `v13_upperLowerClash` consumes Phase A, observer CD-ENF normalization, and all nine GaugeBufferedLockedInterface fields. The second-round version derives the lower consequence by `compressionLower_of_budget_machine`, isolates the upper side as one `SelfReductionUpperHypothesis`, and records the seven-field parameter audit in `v13ParameterRecordAudit`.",
    nextObligation := "Keep the concrete ensemble outside this artifact; any concrete instantiation must supply the external ParameterRecord rather than weakening the ledger fields."
  },
  {
    key := "pnp.v13.faithfulness-audit",
    status := .checked,
    truthValue := ⟨100, 88⟩,
    evidence := "V13FaithfulnessAudit records 20 rows mapping Phase A definitions, Phase B definitions, and all nine GaugeBufferedLockedInterface fields to v13 note sections, with explicit faithful/weaker/stronger mismatch verdicts and no reportable-finding row.",
    nextObligation := "Use the weaker-than-note rows as Phase E obligations rather than treating the abstract ledger as a concrete ensemble proof."
  },
  {
    key := "pnp.v13.phase-e.small-locked-sat-smoke",
    status := .checked,
    truthValue := ⟨100, 86⟩,
    evidence := "V13PhaseEConcrete instantiates GaugeBufferedLockedInterface on a four-world one-variable locked CNF family with a VV-style isolation row and hidden gauge bit. It proves the locked-CNF uniqueness lemma, discharges the nine obligations individually in the requested order, and records a nine-row obligation map with no checked failures.",
    nextObligation := "Do not generalize the zero-cost safeQSSM and Unit-pivot boundaryMixing smoke proofs to the scaled ensemble; those remain the hard scaled obligations."
  },
  {
    key := "pnp.weakness-calculus.finite-spectrum-gap",
    status := .checked,
    truthValue := ⟨100, 93⟩,
    evidence := "WeaknessCalculus proves the finite budget-lattice spectrum, the gap identity `spectrumGap_eq_zero_iff_domination`, budget monotonicity, data-processing monotonicity, no-threading-to-positive-gap, split-budget tensor additivity, independent-value tensor multiplicativity, sequential chain-rule availability with an explicit finite defect, additive gap laws for tensor/split sequential composition, and the product cross-term law for independent-value gaps. The two-point toy has local spectrum 1, poly spectrum 2, gap 1, additive tensor gap 2, multiplicative tensor gap 3, and sequential split gap 2.",
    nextObligation := "Keep `StarSWDominationHypothesis` explicit: domination/average-case witness-bit hardness is not proved by the calculus, and no final separation is asserted."
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
    status := .checked,
    truthValue := ⟨100, 98⟩,
    evidence := "pnpBarrierSubsetFrontierCanaries_guardrails records the finite lab-backed Boolean gate: a toy all-three-barrier route clears, every proper subset of the barrier layers fails promotion, and the current local Kpoly promotion gate remains blocked.",
    nextObligation := "Use only the all-three represented barrier gate as the entry condition for the replacement route."
  },
  {
    key := "pnp.replacement-route.opened-barrier-gate",
    status := .replacementOpened,
    truthValue := ⟨100, 99⟩,
    evidence := "currentPNPBarrierRouteDecision_verdict_packet records the decided barrier verdict: the current local Kpoly promotion gate remains blocked, while currentPNPAllBarrierCandidatePromotionGate_clears represents the all-three replacement barrier gate with every required challenge-world interface and positive escape witness.",
    nextObligation := "First concrete obligation: formalize the global complexity-class interface linking the barrier-cleared replacement gate to actual language, uniformity, reduction, and nonmembership data; no final separation theorem is asserted here."
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
    nextObligation := "Discharge currentPNPBarrierRouteDecision_first_obligation by formalizing the missing global complexity-class interface before introducing any final separation statement."
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

theorem currentPNPReplacementRouteOpenedBarrierGate_node :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll ∧
      currentPNPBarrierRouteDecision.barrierGate.ClearsAll ∧
      currentPNPBarrierRouteDecision.firstObligation =
        .globalComplexityClassInterface ∧
      currentPNPBarrierRouteDecision.claimsFinalSeparation = false := by
  exact currentPNPBarrierRouteDecision_verdict_packet

theorem currentPNPGoertzelCalibrationBreak_node :
    (∀ {Z : Type*} {k : Nat} (u : PostSwitchInput Z k),
        nonzeroColumn u.a ->
          invariantProjection (tiInputMap u) = invariantProjection u ∧
            tiInputMap u ≠ u ∧ (tiInputMap u).b ≠ u.b) ∧
      twoPointGlobalSuccessCount = 2 ∧
        (∀ guess : Bool, twoPointLocalSuccessCount guess ≤ 1) ∧
          (∀ guess : Bool, twoPointLocalSuccessCount guess < twoPointGlobalSuccessCount) := by
  exact ⟨fun u ha => calibrationFullInputPreservation_fails_of_nonzeroColumn u ha,
    finite_successDomination_counterexample⟩

theorem currentPNPSteelmanConditional_node :
    Nonempty
        (KernelBitFiber toyKernelA toyKernelB 0 0 ≃
          KernelBitFiber toyKernelA toyKernelB 0 1) ∧
      ¬ (Neutral noThreadingToyStatistic noThreadingToyWitness ∧
          Sufficient noThreadingToyStatistic noThreadingToyWitness) ∧
      (∀ {F : PNPConditionalFramework},
        KernelFlipNeutrality F ->
          StarSWAverageCaseWitnessBitHardness F -> F.pNeNPClaim) ∧
      toyPNPConditionalFramework.pNeNPClaim := by
  exact
    ⟨⟨kernelFlipZeroOneEquiv toyKernelW_isKernel toyKernelW_hits_zero⟩,
      noThreadingToy_obstruction,
      fun hKernel hSW => pnp_steelman_conditional hKernel hSW,
      toy_pnp_steelman_conditional_nonvacuous⟩

theorem currentPNPWeaknessCalculus_node :
    toyWeaknessTask.localSpectrum = 1 ∧
      toyWeaknessTask.polySpectrum = 2 ∧
      toyWeaknessTask.spectrumGap = 1 ∧
      0 < toyWeaknessTask.spectrumGap ∧
      DataProcessing toyWeaknessTask toyWeaknessPostProcessedTask ∧
      ¬ (Neutral noThreadingToyStatistic noThreadingToyWitness ∧
          Sufficient noThreadingToyStatistic noThreadingToyWitness) ∧
      (∀ {budgetTop : Nat} {T : WeaknessTask budgetTop},
        StarSWDominationHypothesis T -> T.spectrumGap = 0) := by
  exact
    ⟨toyWeaknessTask_localSpectrum,
      toyWeaknessTask_polySpectrum,
      toyWeaknessTask_spectrumGap,
      toyWeakness_noThreading_forces_gap,
      toyWeakness_dataProcessing,
      noThreadingToy_obstruction,
      fun h => spectrumGap_zero_of_starSWDomination h⟩

theorem currentPNPWeaknessCompositional_node :
    tensorSpectrumGap toyWeaknessTask toyWeaknessTask = 2 ∧
      tensorValueSpectrumGap toyWeaknessTask toyWeaknessTask = 3 ∧
      sequentialSplitSpectrumGap toyWeaknessTask toyWeaknessTask = 2 ∧
      sequentialSplitLocalSpectrum toyWeaknessTask toyWeaknessTask ≤
        sequentialSpectrum toyWeaknessTask toyWeaknessTask toySequentialDefect
          (sequentialSplitBudget toyWeaknessTask.localBudget
            toyWeaknessTask.localBudget toySequentialDefect) ∧
      sequentialSplitPolySpectrum toyWeaknessTask toyWeaknessTask ≤
        sequentialSpectrum toyWeaknessTask toyWeaknessTask toySequentialDefect
          (sequentialSplitBudget toyWeaknessTask.polyBudget
            toyWeaknessTask.polyBudget toySequentialDefect) ∧
      (∀ {leftTop rightTop : Nat}
        {T : WeaknessTask leftTop} {U : WeaknessTask rightTop},
        BudgetOrdered T -> BudgetOrdered U ->
          tensorSpectrumGap T U = T.spectrumGap + U.spectrumGap) ∧
      (∀ {leftTop rightTop : Nat}
        {T : WeaknessTask leftTop} {U : WeaknessTask rightTop},
        BudgetOrdered T -> BudgetOrdered U ->
          tensorValueSpectrumGap T U =
            T.spectrumGap * U.polySpectrum +
              T.localSpectrum * U.spectrumGap) ∧
      (∀ {leftTop rightTop : Nat}
        {T : WeaknessTask leftTop} {U : WeaknessTask rightTop},
        BudgetOrdered T -> BudgetOrdered U ->
          sequentialSplitSpectrumGap T U =
            T.spectrumGap + U.spectrumGap) := by
  exact
    ⟨toyWeakness_tensor_spectrumGap,
      toyWeakness_tensorValue_spectrumGap,
      toyWeakness_sequential_splitGap,
      toyWeakness_sequential_local_chainRule,
      toyWeakness_sequential_poly_chainRule,
      fun hT hU => tensorSpectrumGap_eq_add hT hU,
      fun hT hU => tensorValueSpectrumGap_eq_crossTerms hT hU,
      fun hT hU => sequentialSplitSpectrumGap_eq_add hT hU⟩

theorem currentPNPV13EvidenceSpine_node :
    Gap toyV13Law toyV13Phase toyV13Transcript toyV13Observer =
        (1 / 2 : Rat) ∧
      toyV13StaticCapture.CapturesGap ∧
      1 - toyV13Telescoping.finalWeight =
        toyV13Telescoping.derivativeSum ∧
      Gap toyV13Law toyV13Phase toyV13Transcript toyV13Observer ≤
        (1 / 2 : Rat) * toyV13Telescoping.derivativeSum := by
  exact
    ⟨toyV13_gap_eq_half,
      toyV13StaticCapture_capturesGap,
      toyV13Telescoping.derivative_telescoping,
      toyV13_phaseA_gap_le_half_derivative_sum⟩

theorem currentPNPV13CDENF_node :
    toyCDENFSemantics.SatNormal (CDENF toyCDENFRaw) =
        toyCDENFSemantics.SatRaw toyCDENFRaw ∧
      (∀ output : Bool,
        toyObserverEvidenceInterface.semantics.SatNormal
            (CDENF
              (toyObserverEvidenceInterface.observerToEvidence () output)) =
          fun omega =>
            toyObserverEvidenceInterface.evalObserver ()
              (toyObserverEvidenceInterface.publicInput omega) = output) := by
  exact ⟨toyCDENF_semantics, toy_observerToCDENF_sat⟩

theorem currentPNPV13GaugeBufferedLedger_node :
    Nonempty
        (GaugeBufferedLockedInterface
          Bool Bool toyCDENFNeutral toyCDENFSafe toyCDENFGauge Bool Unit Unit
          Unit Unit Unit Unit Bool Unit) ∧
      ¬ MeasurableWrt toyLockedInterface.historyField toyLockedInterface.target ∧
      ¬ ∃ h0 : Unit -> Bool,
        ∀ omega, toyLockedInterface.target omega =
          h0 (toyLockedInterface.pivotSummary omega) := by
  exact
    ⟨⟨toyLockedInterface⟩,
      toyLockedInterface_history_not_target_measurable,
      toyLockedInterface_pivot_not_sufficient⟩

theorem currentPNPV13ConditionalClash_node :
    (∀ P : ParameterRecord toyLockedInterface,
      Nonempty (UpperLowerClash toyLockedInterface P)) ∧
      (∀ P : ParameterRecord toyLockedInterface,
        Nonempty (LedgerFieldUseCertificate toyLockedInterface P)) ∧
      v13ParameterRecordAudit.length = 7 := by
  constructor
  · intro P
    exact ⟨toyLockedInterface_conditional_clash P⟩
  · constructor
    · intro P
      exact ⟨(toyLockedInterface_conditional_clash P).fieldUse⟩
    · exact v13ParameterRecordAudit_length

theorem currentPNPV13FaithfulnessAudit_node :
    v13PhaseAFaithfulnessRows.length = 5 ∧
      v13PhaseBFaithfulnessRows.length = 6 ∧
        v13LedgerFaithfulnessRows.length = 9 ∧
          v13FaithfulnessAudit.length = 20 ∧
            (∀ row ∈ v13FaithfulnessAudit,
              row.verdict ≠ .reportableFinding) := by
  exact
    ⟨v13PhaseAFaithfulnessRows_length,
      v13PhaseBFaithfulnessRows_length,
      v13LedgerFaithfulnessRows_length,
      v13FaithfulnessAudit_length,
      v13FaithfulnessAudit_has_no_reportable_findings⟩

theorem currentPNPV13PhaseEConcrete_node :
    Nonempty
        (GaugeBufferedLockedInterface
          PhaseEWorld PhaseEPublic PhaseENeutral PhaseESafe PhaseEGauge Bool
          Bool Unit Unit Unit Unit Unit Unit Unit) ∧
      phaseEObligationMap.length = 9 ∧
        (∀ row ∈ phaseEObligationMap, row.status ≠ .failed) ∧
          PhaseEAllNineObligations := by
  exact
    ⟨⟨phaseELockedInterface⟩,
      phaseEObligationMap_length,
      phaseEObligationMap_has_no_failures,
      phaseE_all_nine_obligations⟩

theorem currentPNPV13PhaseEScaled_node :
    (∀ m k : Nat,
      Nonempty
        (GaugeBufferedLockedInterface
          (PhaseEScaledWorld m k) (PhaseEScaledPublic m k)
          PhaseEScaledNeutral (PhaseEScaledSafe m k) (PhaseEScaledGauge m)
          Unit Unit Unit Unit Unit (PhaseEScaledPayload m k) Unit Unit Unit)) ∧
      phaseEScaledObligationMap.length = 9 ∧
        (∀ row ∈ phaseEScaledObligationMap, row.status ≠ .failed) ∧
          (∀ row ∈ phaseEScaledObligationMap,
            row.status = .familyInadmissible) ∧
            (∀ m k : Nat, PhaseEScaledPublicTargetTagViolation m k) ∧
              (∀ m k : Nat, PhaseEScaledAllMappedObligations m k) := by
  exact
    ⟨fun m k => ⟨phaseEScaledLockedInterface m k⟩,
      phaseEScaledObligationMap_length,
      phaseEScaledObligationMap_has_no_failures,
      phaseEScaledObligationMap_all_familyInadmissible,
      phaseEScaled_familyInadmissible_publicTargetTag,
      phaseEScaled_all_mapped_obligations⟩

theorem currentPNPV13RealRungOneLinear_node :
    (∀ {m : Nat} (i₀ : Fin m) (omega : V13RealLinearWorld m),
      v13RealLinearFullDecoder i₀ (v13RealLinearPublicInput omega) =
        v13RealLinearTarget i₀ omega) ∧
      (∀ {m : Nat} (i₀ : Fin m)
        (omega₀ omega₁ : V13RealLinearWorld m),
        v13RealLinearPublicInput omega₀ =
          v13RealLinearPublicInput omega₁ →
        v13RealLinearTarget i₀ omega₀ =
          v13RealLinearTarget i₀ omega₁) ∧
        (∀ {m : Nat} (i₀ spare : Fin m), spare ≠ i₀ →
          ∀ coordinate : V13RealLinearPublicCoordinate m,
            ¬ V13RealLinearCoordinateDeterminesTarget i₀ coordinate) := by
  exact
    ⟨fun i₀ omega =>
        v13RealLinear_fullPublic_decodes_target i₀ omega,
      fun i₀ omega₀ omega₁ hpublic =>
        v13RealLinear_fullPublic_determines_target i₀ omega₀ omega₁ hpublic,
      fun i₀ spare hspare =>
        v13RealLinear_no_single_public_coordinate_determines_target_of_spare
          i₀ spare hspare⟩

theorem currentPNPV13RealRungOneRowObservers_node :
    (∀ {m : Nat} {A : V13F2LinearEquiv m}
      {rows : Finset (Fin m)} {i₀ : Fin m},
      ¬ V13RealLinearRowsBlockTarget A rows i₀ →
        ∃ w : F2Vec m,
          w i₀ = 1 ∧
            ∀ row : Fin m, row ∈ rows → A.toEquiv w row = 0) ∧
      (∀ {m : Nat} (A : V13F2LinearEquiv m)
        (rows : Finset (Fin m)) (i₀ : Fin m),
        ¬ V13RealLinearRowsBlockTarget A rows i₀ →
          ∃ omega₀ omega₁ : V13RealLinearWorld m,
            v13RealLinearRowsTranscript rows
                (v13RealLinearPublicInput omega₀) =
              v13RealLinearRowsTranscript rows
                (v13RealLinearPublicInput omega₁) ∧
            v13RealLinearTarget i₀ omega₀ ≠
              v13RealLinearTarget i₀ omega₁) := by
  exact
    ⟨fun hnot =>
        v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget hnot,
      fun A rows i₀ hnot =>
        v13RealLinear_opposite_targets_same_rowsTranscript_of_not_blocked
          A rows i₀ hnot⟩

theorem currentPNPV13RealRungOneStaticRows_node :
    ∀ {m q : Nat} (observer : V13RealLinearStaticRowObserver m q)
      (A : V13F2LinearEquiv m) (i₀ : Fin m),
      ¬ V13RealLinearRowsBlockTarget A observer.rows i₀ →
        Fintype.card (V13RealLinearFixedCorrect observer A i₀) =
          Fintype.card (V13RealLinearFixedIncorrect observer A i₀) := by
  intro m q observer A i₀ hnot
  exact
    v13RealLinear_staticRows_correct_card_eq_incorrect_card_of_not_blocked
      observer A i₀ hnot

theorem currentPNPV13RealRungOneAdaptiveRows_node :
    ∀ {m q : Nat} (observer : V13RealLinearAdaptiveRowObserver m q)
      (A : V13F2LinearEquiv m) (i₀ : Fin m) (b : observer.Branch),
      ¬ V13RealLinearRowsBlockTarget A (observer.staticBranch b).rows i₀ →
        Fintype.card
            (V13RealLinearAdaptiveBranchCorrect observer A i₀ b) =
          Fintype.card
            (V13RealLinearAdaptiveBranchIncorrect observer A i₀ b) := by
  intro m q observer A i₀ b hnot
  exact
    v13RealLinear_adaptiveBranch_correct_card_eq_incorrect_card_of_not_blocked
      observer A i₀ b hnot

theorem currentPNPV13RealRungOneQRowBound_node :
    (∀ {m : Nat} (rows : Finset (Fin m)),
      Fintype.card (V13RealLinearRowCombination rows) = 2 ^ rows.card) ∧
      (∀ {m q : Nat} {rows : Finset (Fin m)}, rows.card ≤ q →
        Fintype.card (V13RealLinearRowCombination rows) ≤ 2 ^ q) ∧
      (∀ {m q : Nat} {Seed : Type*}
        (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
        (omega : V13RealLinearAdaptiveQRowWorld m Seed),
        (E.branchRows omega).card ≤ q) ∧
      (∀ {m : Nat} (A : V13F2LinearEquiv m) (rows : Finset (Fin m))
        (i₀ : Fin m),
        V13RealLinearRowsBlockTarget A rows i₀ ↔
          V13RealLinearRowsGenerateTarget A rows i₀) ∧
      (∀ {m : Nat} (A : V13F2LinearEquiv m) (row i₀ : Fin m),
        V13RealLinearRowsGenerateTarget A ({row} : Finset (Fin m)) i₀ ↔
          ∀ w : F2Vec m, A.toEquiv w row = w i₀) ∧
      (∀ {m : Nat} (A : V13F2LinearEquiv m) (i₀ : Fin m),
        (V13RealLinearTargetRows A i₀).card ≤ 1) ∧
      (∀ {m : Nat} {Seed : Type*}
        (E : V13RealLinearAdaptiveQRowExperiment m 1 Seed) (i₀ : Fin m)
        (omega : V13RealLinearAdaptiveQRowWorld m Seed),
        E.generated i₀ omega →
          ∃ row : Fin m,
            row ∈ E.branchRows omega ∧
              ∀ w : F2Vec m, (E.sampleA omega.1).toEquiv w row = w i₀) ∧
      (∀ {m : Nat} {Seed : Type*}
        (E : V13RealLinearAdaptiveQRowExperiment m 1 Seed) (i₀ : Fin m)
        (omega : V13RealLinearAdaptiveQRowWorld m Seed),
        E.generated i₀ omega →
          (V13RealLinearTargetRows (E.sampleA omega.1) i₀).Nonempty) ∧
      (∀ {m : Nat} (i₀ : Fin m) (A : V13F2LinearEquiv m) (x : F2Vec m),
        (v13RealLinearUniformQRowExperiment
          (v13RealLinearTargetRowObserver i₀)).generated i₀ (A, x) ↔
          (V13RealLinearTargetRows A i₀).Nonempty) ∧
      (∀ {m : Nat} (i₀ : Fin m),
        v13RealLinearAdaptiveQRowGeneratedMass
          (v13RealLinearUniformQRowExperiment
            (v13RealLinearTargetRowObserver i₀)) i₀ =
        v13RealLinearUniformTargetRowOccurrenceMass i₀) ∧
      (4 ≤
        Fintype.card
          (V13RealLinearUniformTargetRowOccurrence (0 : Fin 2))) ∧
      (Fintype.card (V13F2LinearEquiv 2) ≤ 6 →
        (1 / 2 : Rat) <
          v13RealLinearUniformTargetRowOccurrenceMass (0 : Fin 2)) ∧
      (Fintype.card (V13F2LinearEquiv 2) ≤ 6 →
        ¬ V13RealLinearUniformInvertibleRowSpanCountingBound
          (v13RealLinearTargetRowObserver (0 : Fin 2)) (0 : Fin 2)) ∧
      (Fintype.card (V13F2LinearEquiv 2) ≤ 6) ∧
      ((1 / 2 : Rat) <
        v13RealLinearUniformTargetRowOccurrenceMass (0 : Fin 2)) ∧
      (¬ V13RealLinearUniformInvertibleRowSpanCountingBound
        (v13RealLinearTargetRowObserver (0 : Fin 2)) (0 : Fin 2)) ∧
      (∀ {m q : Nat} {Seed : Type*} [Fintype Seed]
        (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m),
        v13RealLinearAdaptiveQRowBlockedMass E i₀ =
          v13RealLinearAdaptiveQRowGeneratedMass E i₀) ∧
      (∀ {m q : Nat} {Seed : Type*} [Fintype Seed]
        (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m),
        v13RealLinearAdaptiveQRowGeneratedMass E i₀ ≤ 1) ∧
      (∀ {m q : Nat}, m ≤ q →
        (1 : Rat) ≤ v13RealLinearQRowEpsilon q m) ∧
      (∀ {m : Nat} {Seed : Type*} [Fintype Seed]
        (E : V13RealLinearAdaptiveQRowExperiment m 0 Seed) (i₀ : Fin m),
        V13RealLinearAdaptiveRowSpanCountingBound E i₀) ∧
      (∀ {m q : Nat} {Seed : Type*} [Fintype Seed]
        (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m),
        m ≤ q →
          V13RealLinearAdaptiveRowSpanCountingBound E i₀) ∧
      (∀ {m q : Nat} {Seed : Type*} [Fintype Seed]
      (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m),
      V13RealLinearAdaptiveKernelFlipSurchargeBound E i₀) ∧
      (∀ {m q : Nat} {Seed : Type*} [Fintype Seed]
        (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m),
        V13RealLinearAdaptiveRowSpanCountingBound E i₀ →
            v13RealLinearAdaptiveQRowSuccess E i₀ ≤
              (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m) ∧
      (∀ {m q : Nat} (observer : V13RealLinearAdaptiveRowObserver m q)
        (i₀ : Fin m),
        V13RealLinearUniformInvertibleRowSpanCountingBound observer i₀ →
          v13RealLinearUniformAdaptiveQRowSuccess observer i₀ ≤
            (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m) ∧
      (∀ q m : Nat, 0 ≤ v13RealLinearQRowEpsilon q m) := by
  exact
    ⟨v13RealLinear_rowCombination_card,
      fun hrows =>
        v13RealLinear_rowCombination_card_le_of_rows_card_le hrows,
      fun E omega =>
        E.branchRows_card_le omega,
      fun A rows i₀ =>
        v13RealLinear_rowsBlockTarget_iff_rowsGenerateTarget A rows i₀,
      fun A row i₀ =>
        v13RealLinear_rowsGenerateTarget_singleton_iff A row i₀,
      fun A i₀ =>
        v13RealLinear_targetRows_card_le_one A i₀,
      fun E i₀ omega hgen =>
        E.generated_one_budget_exists_target_row i₀ omega hgen,
      fun E i₀ omega hgen =>
        E.targetRows_nonempty_of_generated_one_budget i₀ omega hgen,
      fun i₀ A x =>
        v13RealLinear_targetRowObserver_generated_iff_targetRows_nonempty
          i₀ A x,
      fun i₀ =>
        v13RealLinear_targetRowObserverGeneratedMass_eq_occurrenceMass i₀,
      v13RealLinearUniformTargetRowOccurrence_card_four_le,
      fun hcard =>
        v13RealLinearUniformTargetRowOccurrenceMass_two_zero_gt_half hcard,
      fun hcard =>
        v13RealLinear_targetRowObserver_spanCountingBound_fails_two_zero hcard,
      v13RealLinear_f2_equiv_two_card_le_six,
      v13RealLinearUniformTargetRowOccurrenceMass_two_zero_gt_half_unconditional,
      v13RealLinear_targetRowObserver_spanCountingBound_fails_two_zero_unconditional,
      fun E i₀ =>
        v13RealLinearAdaptiveQRowBlockedMass_eq_generatedMass E i₀,
      fun E i₀ =>
        v13RealLinearAdaptiveQRowGeneratedMass_le_one E i₀,
      fun hmq =>
        v13RealLinear_qrow_one_le_epsilon_of_m_le_q hmq,
      fun E i₀ =>
        v13RealLinearAdaptiveRowSpanCountingBound_of_zero_budget E i₀,
      fun E i₀ hmq =>
        v13RealLinearAdaptiveRowSpanCountingBound_of_m_le_q E i₀ hmq,
      fun E i₀ =>
        v13RealLinear_adaptiveKernelFlipSurchargeBound E i₀,
      fun E i₀ hcount =>
        v13RealLinear_adaptive_qrow_success_bound_of_spanCounting
          E i₀ hcount,
      fun observer i₀ hcount =>
        v13RealLinear_uniform_adaptive_qrow_success_bound_of_spanCounting
          observer i₀ hcount,
      v13RealLinear_qrow_epsilon_nonnegative⟩

theorem currentPNPV13ObserverLadder_node :
    PhaseEScaledObserverLadderMark ∧
      phaseEScaledObserverLadderMap.length = 4 ∧
        (∀ row ∈ phaseEScaledObserverLadderMap,
          row.status = .exactHalf ∨ row.status = .checkedCounterexample ∨
            row.status = .pinnedHypothesis ∨ row.status = .iffHardCore) := by
  exact
    ⟨phaseEScaled_observer_ladder_mark,
      phaseEScaledObserverLadderMap_length,
      phaseEScaledObserverLadderMap_has_no_unlabeled_stop⟩
end Mettapedia.Computability.PNP
