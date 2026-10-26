import Mettapedia.OSLF.MeTTaIL.CollectionExecutionAdmission
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherCompatibility
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend
import Mettapedia.OSLF.MeTTaIL.CollectionRootSearch
import Mettapedia.OSLF.MeTTaIL.CollectionRootCoverage
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceAdmission
import Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionInterpretation
import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionCodec

/-!
# Collection compiler contract inventory

This inventory is executable metadata. `derived` capabilities are established
by the current admission or execution theorems. `certificate` capabilities are
accepted only through a separately proved language profile. `unsupported`
capabilities keep an admission obligation and are not silently approximated.

The shared driver consumes lawful, stable realizations and their readiness
invariants. Raw matches enter the typed continuation before a reduct exists.
Retained batches conserve full receipt multiplicity. Recognized canonical
root profiles have source soundness and completeness in the existing
presented GSLT, and use the common emitter's four entries. These profiles
require unconditional root rules with set-free element schemas, suitable
capture spines, no equations or additional collection laws, root-only sites
and a finite provider. The executable recognizer checks every authored
variable spine's index order, without a dependency-count bound. Noninjective
and nonvariable substitutions supply no recoverable variable-spine capture.
Those restrictions describe the root profile. The separately checked
occurrence profile has recursive native matching, typed set contexts and
finite nullary or mixed input/output queries with checked object input templates
and canonical provider values. Its source and
settled outgoing coverage are `CollectionOccurrenceAdmission.source_exact`
and `settled_edges_cover_steps`; the common emitter selects it from its
certificate. Ordinary traced output matching, including nested collection schemas, retains
its exact allocation choices. Quantified guards, child-step premises and
additional equations are not licensed by that certificate.
The default class matcher retains its set admission restriction.

Quantified bodies return to their enclosing assignment, as established by
`GeneralPremise.QuantifiedElements.final_eq_initial`. Finite carrier
rearrangement has a separate query-validation transport theorem,
`canonical_query_validation`: each retained event cites its original body
witness. It does not identify raw histories across set contraction or license
quotient-aware quantified collection execution.

`GeneralPremise.Interpreted` supplies one premise and firing family with
explicit input and matching interpretations. The ordinary executor is its
structural specialization, including every child and quantified body.
`Interpreted.PremiseHolds.transport` lifts a primitive interpretation map
through the full AST, carrying the mapped matcher traces and the complete
event tree. It fixes assignments and object values; it is not a theorem of
canonical-assignment transport. `RecursiveCollectionHandoff.matchingInterpretation`
uses allocation evidence and an explicit repeated-body comparison. Its
source controls derive the conditional child at both singleton and duplicate
set presentations. The native matching component realizes its `Matches`
judgment; the full retained premise machine is not yet qualified for that interpretation,
and the admission restrictions remain in force.

`MatchingExecution` now parameterizes the existing retained query, root and
child-target frames. Its ordinary instance keeps the structural representation.
The canonical collection instance retains its normalized request with the
allocation machine. `canonical_firing_iff` preserves the entire firing payload
across equivalent sources in that interpretation, including all premise forms.
Native request normalization, initialization, transition, completion, readout
and input comparison realize this matching service. These primitive bridges
do not wire the whole interpreted premise machine into emission or establish
agreement with the existing presented GSLT's ordinary primitive receipts.

`ReferenceStep` now indexes its existing source family by an explicit internal
boundary policy. The presentation policy preserves the original witnesses,
checker and literal provider-output and child-target matching. The declared
equational policy uses the language's actual `ReferenceStep.Equivalent` and
ordinary matches at related presentations. Its child boundary closes both
step endpoints and the target match. The initial declared-policy selector
requires unconditional authored equations. Equation-free languages have the same
full recursive witnesses under both policies, including quantified bodies.
The declared policy is not admitted by this inventory. Provider-input
compatibility, typed roles and capture transport remain separate obligations;
freshness retains its existing literal interpretation.

The retained source-measure certificate bounds recursive premise depth from
actual child sources, including quantified histories. The actual canonical
parallel and sum rules discharge it by a strict decrease in canonical source
size. Their receipt-support theorem does not establish multiplicity or
settlement. It also does not cover firing origins introduced by additional
authored equations: the actual sum singleton equation supplies a separating
example that intrinsic collection canonicalization cannot recover.

The retained query and scheduled coverage proofs now use primitive cursor
laws and represented matching witnesses for both concrete backends. Their
work proofs use the backend's actual unread-answer and transition costs.
`Query.completedEventually` drains each finite query; `Scheduled.finiteDrain`
drains the full premise AST at a fixed child depth. Fixed-depth drainage does
not establish that the chosen depth covers every source firing. Primitive
free-name support lifts through captures, queries and scheduled continuations.
Constructor and binder-display names remain additional native table obligations.

Input equality is part of the matching interpretation. The two-input control
in `GeneralPremise.SharedOutputControls.RetainedCollections.InputBoundary`
distinguishes literal provider equality from collection equality using the
same retained capture. Generic machine coverage does not authorize replacing
one interpretation by the other. Source agreement still needs primitive
provider, matching and child-step transport certificates.

Replacement typing and first-order fold interpretation are component
theorems. They do not by themselves establish equation extraction, firing
coherence or a logical derivation observation. `BinaryCollectionLowering`
uses the actual replacement and unwrapping operations and checks the local
representation table. `BinaryCollectionInterpretation.replacement_model`
derives the fold from source equations and uses the existing collection
arrangement, including the canonical form of the actual lowered pattern.
`read_lawNormal` and its native normalizer correspondence retain that value
under flattening and compatible declared units. These are interpretation
results; source-theory reflection, firing coverage and independent
collection-data observations remain separate obligations.
-/

namespace Mettapedia.OSLF.MeTTaIL.CollectionCompilerContracts

inductive Status where
  | derived
  | certificate
  | unsupported
  deriving DecidableEq, Repr

inductive Capability where
  | authoredModuleAndBinding
  | finiteBagMultiplicity
  | finiteSetReuseAndOverlap
  | recursiveLeanMatching
  | recursiveReceiptSemantics
  | ordinaryPresentationSoundness
  | ordinaryMatcherBackendAdapter
  | completeMatcherStrategyEquality
  | sharedPostMatchContinuation
  | nativePostMatchContinuation
  | certifiedPublishedHandoff
  | nativeScheduledConsumerRun
  | genericCompleteExploration
  | arrangedRootRuntime
  | planOrderedRootRuntime
  | receiptReplayAndResumption
  | typedResidualContextTransport
  | finiteSetContextEnumeration
  | repeatedCaptureComparison
  | modelNormalizationCoherence
  | dynamicPremiseProvider
  | scopeExtrusion
  | recursiveMeTTaMatching
  | emittedSetContextEnumeration
  | matchingInsideSetPremises
  | matchingInsideSetEquations
  | genericAllocationScheduling
  | nativeLoggedCollectionSearch
  | sharedNativeSearchDriver
  | chronologicalPostMatchHandoff
  | finiteLoggedReceiptCoverage
  | boundedPostMatchSourceCoverage
  | retainedRawNativeContinuation
  | retainedContinuationConservation
  | rawRootSourcePacketCoverage
  | rootPresentedSoundness
  | rootPresentedCompleteness
  | compositeTypedCollectionSearch
  | completeMachineEmission
  | nestedPresentedSoundness
  | nestedPresentedCompleteness
  | canonicalWholeCollectionInputs
  | objectTemplateQueryInputs
  | collectionValuedQueryOutputs
  | namedReplacementTyping
  | binaryCollectionLoweringTyping
  | sourceEquationFoldInterpretation
  | canonicalFoldInterpretation
  | lawFoldInterpretation
  | lexicalQuantifierScope
  | canonicalQuantifierValidation
  | sharedPremiseInterpretation
  | primitivePremiseInterpretationTransport
  | allocationPremiseInterpretation
  | nativeAllocationInterpretation
  | retainedInterpretedFrames
  | canonicalInterpretedRootCoherence
  | nativeCanonicalMatchingService
  | nativeInterpretedPremises
  | interpretedPresentedAgreement
  | generalPremiseCanonicalTransport
  | declaredDerivationObservation
  deriving DecidableEq, Repr

def status : Capability → Status
  | .authoredModuleAndBinding => .derived
  | .finiteBagMultiplicity => .derived
  | .finiteSetReuseAndOverlap => .derived
  | .recursiveLeanMatching => .derived
  | .recursiveReceiptSemantics => .derived
  | .ordinaryPresentationSoundness => .derived
  | .ordinaryMatcherBackendAdapter => .derived
  | .completeMatcherStrategyEquality => .derived
  | .sharedPostMatchContinuation => .derived
  | .nativePostMatchContinuation => .derived
  | .certifiedPublishedHandoff => .derived
  | .nativeScheduledConsumerRun => .derived
  | .genericCompleteExploration => .derived
  | .arrangedRootRuntime => .derived
  | .planOrderedRootRuntime => .derived
  | .receiptReplayAndResumption => .derived
  | .typedResidualContextTransport => .derived
  | .finiteSetContextEnumeration => .derived
  | .repeatedCaptureComparison => .certificate
  | .modelNormalizationCoherence => .certificate
  | .dynamicPremiseProvider => .certificate
  | .scopeExtrusion => .certificate
  | .recursiveMeTTaMatching => .certificate
  | .emittedSetContextEnumeration => .certificate
  | .matchingInsideSetPremises => .certificate
  | .matchingInsideSetEquations => .unsupported
  | .genericAllocationScheduling => .derived
  | .nativeLoggedCollectionSearch => .derived
  | .sharedNativeSearchDriver => .derived
  | .chronologicalPostMatchHandoff => .derived
  | .finiteLoggedReceiptCoverage => .derived
  | .boundedPostMatchSourceCoverage => .derived
  | .retainedRawNativeContinuation => .derived
  | .retainedContinuationConservation => .derived
  | .rawRootSourcePacketCoverage => .derived
  | .rootPresentedSoundness => .derived
  | .rootPresentedCompleteness => .certificate
  | .compositeTypedCollectionSearch => .certificate
  | .completeMachineEmission => .certificate
  | .nestedPresentedSoundness => .certificate
  | .nestedPresentedCompleteness => .certificate
  | .canonicalWholeCollectionInputs => .certificate
  | .objectTemplateQueryInputs => .certificate
  | .collectionValuedQueryOutputs => .certificate
  | .namedReplacementTyping => .derived
  | .binaryCollectionLoweringTyping => .derived
  | .sourceEquationFoldInterpretation => .derived
  | .canonicalFoldInterpretation => .derived
  | .lawFoldInterpretation => .certificate
  | .lexicalQuantifierScope => .derived
  | .canonicalQuantifierValidation => .certificate
  | .sharedPremiseInterpretation => .derived
  | .primitivePremiseInterpretationTransport => .derived
  | .allocationPremiseInterpretation => .derived
  | .nativeAllocationInterpretation => .certificate
  | .retainedInterpretedFrames => .derived
  | .canonicalInterpretedRootCoherence => .derived
  | .nativeCanonicalMatchingService => .certificate
  | .nativeInterpretedPremises => .unsupported
  | .interpretedPresentedAgreement => .unsupported
  | .generalPremiseCanonicalTransport => .unsupported
  | .declaredDerivationObservation => .unsupported

def all : List Capability :=
  [.authoredModuleAndBinding, .finiteBagMultiplicity, .finiteSetReuseAndOverlap,
   .recursiveLeanMatching, .recursiveReceiptSemantics, .ordinaryPresentationSoundness,
   .ordinaryMatcherBackendAdapter, .completeMatcherStrategyEquality,
   .sharedPostMatchContinuation, .nativePostMatchContinuation,
   .certifiedPublishedHandoff, .nativeScheduledConsumerRun,
   .genericCompleteExploration,
   .arrangedRootRuntime,
   .planOrderedRootRuntime,
   .receiptReplayAndResumption,
   .typedResidualContextTransport, .finiteSetContextEnumeration, .repeatedCaptureComparison,
   .modelNormalizationCoherence, .dynamicPremiseProvider, .scopeExtrusion,
   .recursiveMeTTaMatching, .emittedSetContextEnumeration,
   .matchingInsideSetPremises, .matchingInsideSetEquations,
   .genericAllocationScheduling, .nativeLoggedCollectionSearch,
   .sharedNativeSearchDriver, .chronologicalPostMatchHandoff,
   .finiteLoggedReceiptCoverage, .boundedPostMatchSourceCoverage,
   .retainedRawNativeContinuation, .retainedContinuationConservation,
   .rawRootSourcePacketCoverage, .rootPresentedSoundness, .rootPresentedCompleteness,
   .compositeTypedCollectionSearch, .completeMachineEmission,
   .nestedPresentedSoundness, .nestedPresentedCompleteness,
   .canonicalWholeCollectionInputs, .objectTemplateQueryInputs, .collectionValuedQueryOutputs, .namedReplacementTyping,
   .binaryCollectionLoweringTyping, .sourceEquationFoldInterpretation,
   .canonicalFoldInterpretation, .lawFoldInterpretation,
   .lexicalQuantifierScope, .canonicalQuantifierValidation,
   .sharedPremiseInterpretation, .primitivePremiseInterpretationTransport,
   .allocationPremiseInterpretation, .nativeAllocationInterpretation,
   .retainedInterpretedFrames, .canonicalInterpretedRootCoherence,
   .nativeCanonicalMatchingService, .nativeInterpretedPremises, .interpretedPresentedAgreement,
   .generalPremiseCanonicalTransport, .declaredDerivationObservation]

def inventory : List (Capability × Status) := all.map fun capability => (capability, status capability)

example : all.Nodup := by decide
theorem all_complete (capability : Capability) : capability ∈ all := by
  cases capability <;> decide
example : status .finiteSetReuseAndOverlap = .derived := rfl
example : status .modelNormalizationCoherence = .certificate := rfl
example : status .nativePostMatchContinuation = .derived := rfl
example : status .nativeScheduledConsumerRun = .derived := rfl
example : status .genericAllocationScheduling = .derived := rfl
example : status .nativeLoggedCollectionSearch = .derived := rfl
example : status .completeMachineEmission = .certificate := rfl
example : status .recursiveMeTTaMatching = .certificate := rfl
example : status .emittedSetContextEnumeration = .certificate := rfl
example : status .generalPremiseCanonicalTransport = .unsupported := rfl
example : status .declaredDerivationObservation = .unsupported := rfl

end Mettapedia.OSLF.MeTTaIL.CollectionCompilerContracts
