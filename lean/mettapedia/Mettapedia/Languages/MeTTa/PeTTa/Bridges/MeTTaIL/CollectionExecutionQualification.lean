import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionOccurrence
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceDiscoveryExecution
import Mettapedia.GSLT.LanguageDef.CollectionOccurrenceRootComparisonControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution
import Mettapedia.GSLT.LanguageDef.CollectionNestedBatchControls
import Mettapedia.GSLT.LanguageDef.CollectionOccurrenceMachineControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution
import Mettapedia.OSLF.MeTTaIL.LawNormalRepresentationControls
import Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionHandoffExecution
import Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationRenaming
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceHandoff
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentationControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionStateExecution
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionControls
import Mettapedia.OSLF.MeTTaIL.CollectionContextCoverage
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContextExecution
import Mettapedia.OSLF.MeTTaIL.CollectionContextVariantsControls
import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatchingNormalization
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPlanExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionSearch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionPostMatch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RootCollection
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionRootCoverageExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionRoot
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionOccurrence
import Mettapedia.GSLT.LanguageDef.CollectionOccurrenceAdmissionControls
import Mettapedia.GSLT.LanguageDef.CollectionInputGuardControls
import Mettapedia.OSLF.MeTTaIL.CollectionInputFiring
import Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTransportControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchGraph
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionCodec
import Mettapedia.GSLT.LanguageDef.CollectionConsumerControls
import Mettapedia.OSLF.MeTTaIL.CollectionCompilerContracts
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherCompatibility
import Mettapedia.OSLF.MeTTaIL.CollectionPlanMachineControls
import Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearchStable
import Mettapedia.OSLF.MeTTaIL.CollectionRootSearch
import Mettapedia.OSLF.MeTTaIL.EquationalScopedReceiptControls

/-!
# Qualified collection execution surface

One import exposes source-derived requests, the shared native search interface
and driver, exact receipt codecs, chronological publication and its typed
handoff, authored consumers, and the contract inventory used by the gate.
Canonical root profiles connect this execution surface to source successor
coverage and the common emitter. The default class matcher retains its set
restriction. Nested occurrences with nullary guards or whole-capture input
guards over canonical finite provider rows have source-to-retained-search
coverage. The native joint loop realizes the retained machine, including current-source typed job discovery, binding elaboration and
residual context variants. Native retained Search operations include exact
resumption, completion/blocked status, canonical targets and cached finished
receipts while retaining the complete raw machine. The admission-independent dictionary realization uses the existing generic
runner, explorer and graph readout. The canonical occurrence profile is selected
by its checked admission conditions, with source-to-emitted graph correspondence
and settled outgoing successor coverage. Richer equations and premise transport
require additional profiles; logical derivation identity and aggregation remain
separate observation obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionExecutionQualification.GraphObservation
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionCommittedObservation GeneralPremise
open Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls
open SpaceSemantics Eval WireKit
open CollectionOccurrenceSearchExecution.Declared
open InferenceCettaWire.AuthoredRule (contextualValueTerm)

/-- Faithful wire of the existing one-step graph key, including ordered child evidence. -/
def logicalKeyTerm {Choice : Type} (choiceTerm : Choice → Term) (key : LogicalKey Choice) : Term :=
  .application "DeclaredFiringKey" [.natural key.selectedRule,.natural key.authoredRule,
    .application "LogicalSiteShape" [encodeList Term.natural key.siteShape.address,
      encodeList InferenceCettaWire.AuthoredRule.typeTerm key.siteShape.bound,
      InferenceCettaWire.AuthoredRule.typeTerm key.siteShape.type,
      encodeList ScopedRuleJobReadoutExecution.typingFrameTerm key.siteShape.typingFrames],
    encodeList (encodeOption contextualValueTerm) [key.first,key.intermediate,key.last],
    RetainedMatchingWire.eventsTerm choiceTerm key.childHistory]

private def keyNatural? : Term → Option Nat
  | .natural value => some value
  | _ => none

private def optionalValue? : Term → Option (Option RuleBinding.ContextualValue)
  | .symbol "None" => some none
  | .application "Some" [value] => some <$> InferenceCettaWire.AuthoredRule.decodeContextualValue? value
  | _ => none

private theorem optionalValue?_encodeOption (value : Option RuleBinding.ContextualValue) :
    optionalValue? (encodeOption contextualValueTerm value) = some value := by
  cases value <;> simp [optionalValue?,encodeOption]

def decodeLogicalKey? {Choice : Type} (decodeChoice : Term → Option Choice) : Term → Option (LogicalKey Choice)
  | .application "DeclaredFiringKey" [.natural selected,.natural authored,
      .application "LogicalSiteShape" [address,bound,type,frames],values,history] => do
      let address ← decodeList keyNatural? address
      let bound ← decodeList InferenceCettaWire.AuthoredRule.decodeType? bound
      let type ← InferenceCettaWire.AuthoredRule.decodeType? type
      let frames ← decodeList ScopedRuleJobReadoutExecution.decodeTypingFrame? frames
      let values ← decodeList optionalValue? values
      let history ← ScopedRuleJobReadoutExecution.decodeEventsWith? decodeChoice history
      match values with
      | [first,intermediate,last] => pure ⟨selected,authored,⟨address,bound,type,frames⟩,first,intermediate,last,history⟩
      | _ => none
  | _ => none

theorem decodeLogicalKey?_logicalKeyTerm {Choice : Type} (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (key : LogicalKey Choice) :
    decodeLogicalKey? decodeChoice (logicalKeyTerm choiceTerm key) = some key := by
  rcases key with ⟨selected,authored,site,first,intermediate,last,history⟩
  rcases site with ⟨address,bound,type,frames⟩
  have naturals : decodeList keyNatural? (encodeList Term.natural address) = some address :=
    decodeList_encodeList keyNatural? Term.natural (fun _ => rfl) address
  simp [logicalKeyTerm,decodeLogicalKey?,optionalValue?_encodeOption,naturals,
    decodeList_encodeList,ScopedRuleJobReadoutExecution.decodeEventsWith?_eventsTerm choiceTerm decodeChoice inverse,
    ]

theorem logicalKeyTerm_injective {Choice : Type} (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice) :
    Function.Injective (logicalKeyTerm choiceTerm) := by
  intro first second same
  have decoded := congrArg (decodeLogicalKey? decodeChoice) same
  simpa only [decodeLogicalKey?_logicalKeyTerm choiceTerm decodeChoice inverse,Option.some.injEq] using decoded

theorem decodeLogicalKey?_wrong_constructor {Choice : Type} (decodeChoice : Term → Option Choice) :
    decodeLogicalKey? decodeChoice (.application "CommittedOccurrence" []) = none := rfl

theorem actual_key_coordinates {Choice : Type} (choiceTerm : Choice → Term) (pair : Committed Choice) :
    committedKeyTerm choiceTerm ["x","y","z"] pair = logicalKeyTerm choiceTerm (logicalKey pair) := rfl

variable (program : Program) (agreement : ProgramAgreementOn keyHeads keyLibrary.runtime program)

include agreement in
theorem logical_key_returns {Choice : Type} (choiceTerm : Choice → Term)
    (table : List String) (operations : CanonOperations program table) (host : Effects.State)
    (pair : Committed Choice)
    (covered : ∀ name ∈ ["x","y","z"], ∀ value,
      ScopedRuleMatching.lookup pair.2.completed name = some value → CanonicalCompare.Covered table value.body) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-extract"
        [CompleteExecution.tableValue table,encoded (encodeList Term.string ["x","y","z"]),
          encoded (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm pair)])
      host (encoded (logicalKeyTerm choiceTerm (logicalKey pair))) := by
  simpa only [actual_key_coordinates] using
    key_extract_returns program agreement choiceTerm table operations ["x","y","z"] host pair covered

include agreement in
theorem logical_keys_returns {Choice : Type} [DecidableEq Choice] (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (table : List String) (operations : CanonOperations program table) (host : Effects.State)
    (pairs : List (Committed Choice))
    (covered : ∀ pair ∈ pairs, ∀ name ∈ ["x","y","z"], ∀ value,
      ScopedRuleMatching.lookup pair.2.completed name = some value → CanonicalCompare.Covered table value.body) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-unique"
        [CompleteExecution.tableValue table,encoded (encodeList Term.string ["x","y","z"]),
          encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) pairs)])
      host (encoded (encodeList (logicalKeyTerm choiceTerm) (orderedCommittedKeys logicalKey pairs))) := by
  have projected := key_unique_returns program agreement choiceTerm table operations ["x","y","z"] host pairs covered
  have encodedKeys : pairs.map (committedKeyTerm choiceTerm ["x","y","z"]) =
      (pairs.map logicalKey).map (logicalKeyTerm choiceTerm) := by
    simp only [List.map_map]
    exact List.map_congr_left (fun pair _ => actual_key_coordinates choiceTerm pair)
  rw [encodedKeys, encoded_eraseDups (logicalKeyTerm choiceTerm)
    (logicalKeyTerm_injective choiceTerm decodeChoice inverse)] at projected
  simpa only [encodeList_map,Function.id_comp,orderedCommittedKeys] using projected

include agreement in
theorem logical_keys_replay_returns {Choice : Type} [DecidableEq Choice] (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (table : List String) (operations : CanonOperations program table) (host : Effects.State)
    (earlier replay : List (Committed Choice))
    (seen : committedKeys logicalKey replay ⊆ committedKeys logicalKey earlier)
    (covered : ∀ pair ∈ earlier ++ replay, ∀ name ∈ ["x","y","z"], ∀ value,
      ScopedRuleMatching.lookup pair.2.completed name = some value → CanonicalCompare.Covered table value.body) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-unique"
        [CompleteExecution.tableValue table,encoded (encodeList Term.string ["x","y","z"]),
          encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) (earlier ++ replay))])
      host (encoded (encodeList (logicalKeyTerm choiceTerm) (orderedCommittedKeys logicalKey earlier))) := by
  simpa only [orderedCommittedKeys_replay logicalKey earlier replay seen] using
    logical_keys_returns program agreement choiceTerm decodeChoice inverse table operations host (earlier ++ replay) covered

include agreement in
theorem logical_binary_returns {Choice : Type} (choiceTerm : Choice → Term)
    (host : Effects.State) (key : LogicalKey Choice) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-binary" [encoded (.string "Edge"),encoded (logicalKeyTerm choiceTerm key)])
      host (encoded (encodeOption InferenceCettaWire.encodePattern (logicalEdge? key))) :=
  key_binary_returns program agreement host "Edge" key.selectedRule key.authoredRule _ _
    key.first key.intermediate key.last

include agreement in
theorem logical_bag_returns {Choice : Type} [DecidableEq Choice] (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (table : List String) (operations : CanonOperations program table) (host : Effects.State)
    (pairs : List (Committed Choice))
    (covered : ∀ pair ∈ pairs, ∀ name ∈ ["x","y","z"], ∀ value,
      ScopedRuleMatching.lookup pair.2.completed name = some value → CanonicalCompare.Covered table value.body) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-bag"
        [CompleteExecution.tableValue table,encoded (encodeList Term.string ["x","y","z"]),encoded (.string "Edge"),
          encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) pairs)])
      host (encoded (encodeList InferenceCettaWire.encodePattern
        ((orderedCommittedKeys logicalKey pairs).filterMap logicalEdge?))) :=
  key_bag_returns program agreement choiceTerm table operations ["x","y","z"] "Edge"
    (logicalKeyTerm choiceTerm) logicalKey (logicalKeyTerm_injective choiceTerm decodeChoice inverse)
    (actual_key_coordinates choiceTerm) logicalEdge? host pairs covered
    (fun key _ => logical_binary_returns program agreement choiceTerm host key)

include agreement in
theorem logical_facts_returns {Choice : Type} [DecidableEq Choice] (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (table : List String) (operations : CanonOperations program table) (host : Effects.State)
    (pairs : List (Committed Choice))
    (covered : ∀ pair ∈ pairs, ∀ name ∈ ["x","y","z"], ∀ value,
      ScopedRuleMatching.lookup pair.2.completed name = some value → CanonicalCompare.Covered table value.body) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-facts"
        [CompleteExecution.tableValue table,encoded (encodeList Term.string ["x","y","z"]),encoded (.string "Edge"),
          encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) pairs)])
      host (encoded (encodeList InferenceCettaWire.encodePattern
        ((orderedCommittedKeys logicalKey pairs).filterMap logicalEdge?).eraseDups)) :=
  key_facts_returns program agreement choiceTerm table operations ["x","y","z"] "Edge"
    (logicalKeyTerm choiceTerm) logicalKey (logicalKeyTerm_injective choiceTerm decodeChoice inverse)
    (actual_key_coordinates choiceTerm) logicalEdge? host pairs covered
    (fun key _ => logical_binary_returns program agreement choiceTerm host key)

/-- Every completed body contributes its actual constructor, free and display names. -/
def observationNameTable {Choice : Type} (pairs : List (Committed Choice)) : List String :=
  CanonicalCompare.nameTable (pairs.flatMap fun pair =>
    pair.2.completed.flatMap fun entry => CanonicalCompare.names entry.2.body)

theorem observationNameTable_ordered {Choice : Type} (pairs : List (Committed Choice)) :
    CanonicalCompare.NameOrdered (observationNameTable pairs) :=
  CanonicalCompare.nameTable_ordered _

theorem observationNameTable_covers {Choice : Type} (pairs : List (Committed Choice))
    (pair : Committed Choice) (member : pair ∈ pairs) (name : String) (value : RuleBinding.ContextualValue)
    (found : ScopedRuleMatching.lookup pair.2.completed name = some value) :
    CanonicalCompare.Covered (observationNameTable pairs) value.body := by
  intro label named
  apply CanonicalCompare.mem_nameTable.mpr
  exact List.mem_flatMap.mpr ⟨pair,member,List.mem_flatMap.mpr
    ⟨(name,value),ScopedRuleMatching.lookup_member pair.2.completed name value found,named⟩⟩

include agreement in
theorem logical_keys_automatic_returns {Choice : Type} [DecidableEq Choice] (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (host : Effects.State) (pairs : List (Committed Choice))
    (operations : CanonOperations program (observationNameTable pairs)) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-unique"
        [CompleteExecution.tableValue (observationNameTable pairs),encoded (encodeList Term.string ["x","y","z"]),
          encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) pairs)])
      host (encoded (encodeList (logicalKeyTerm choiceTerm) (orderedCommittedKeys logicalKey pairs))) :=
  logical_keys_returns program agreement choiceTerm decodeChoice inverse _ operations host pairs
    (fun pair member name _ value found => observationNameTable_covers pairs pair member name value found)

include agreement in
theorem logical_bag_automatic_returns {Choice : Type} [DecidableEq Choice] (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (host : Effects.State) (pairs : List (Committed Choice))
    (operations : CanonOperations program (observationNameTable pairs)) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-bag"
        [CompleteExecution.tableValue (observationNameTable pairs),encoded (encodeList Term.string ["x","y","z"]),
          encoded (.string "Edge"),encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) pairs)])
      host (encoded (encodeList InferenceCettaWire.encodePattern
        ((orderedCommittedKeys logicalKey pairs).filterMap logicalEdge?))) :=
  logical_bag_returns program agreement choiceTerm decodeChoice inverse _ operations host pairs
    (fun pair member name _ value found => observationNameTable_covers pairs pair member name value found)

include agreement in
theorem logical_facts_automatic_returns {Choice : Type} [DecidableEq Choice] (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (host : Effects.State) (pairs : List (Committed Choice))
    (operations : CanonOperations program (observationNameTable pairs)) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:key-facts"
        [CompleteExecution.tableValue (observationNameTable pairs),encoded (encodeList Term.string ["x","y","z"]),
          encoded (.string "Edge"),encoded (encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) pairs)])
      host (encoded (encodeList InferenceCettaWire.encodePattern
        ((orderedCommittedKeys logicalKey pairs).filterMap logicalEdge?).eraseDups)) :=
  logical_facts_returns program agreement choiceTerm decodeChoice inverse _ operations host pairs
    (fun pair member name _ value found => observationNameTable_covers pairs pair member name value found)

/-- Expose the real ordinary choice decoder through the authoritative trace decoder. -/
def ordinaryChoice? (wire : Term) : Option GeneralScopedMatchMachine.BagChoice :=
  (ScopedRuleJobReadoutExecution.decodeTrace? (encodeList id [wire])).bind List.head?

theorem ordinaryChoice?_choiceTerm (choice : GeneralScopedMatchMachine.BagChoice) :
    ordinaryChoice? (RuleInstantiationExecution.GeneralExecution.bagChoiceTerm choice) = some choice := by
  unfold ordinaryChoice?
  change (ScopedRuleJobReadoutExecution.decodeTrace?
    (PremiseOperationsExecution.GeneralExecution.traceTerm [choice])).bind List.head? = some choice
  rw [ScopedRuleJobReadoutExecution.decodeTrace?_traceTerm]
  rfl

theorem canonicalChoice_inverse (choice : EquationalScopedReceipts.Event) :
    RecursiveCollectionExecution.decodeEvent? (RecursiveCollectionExecution.eventTerm choice) = some choice :=
  RecursiveCollectionExecution.decodeEvent?_eventTerm choice

theorem ordinary_logicalKeyTerm_injective :
    Function.Injective (logicalKeyTerm RuleInstantiationExecution.GeneralExecution.bagChoiceTerm) :=
  logicalKeyTerm_injective _ ordinaryChoice? ordinaryChoice?_choiceTerm

theorem canonical_logicalKeyTerm_injective :
    Function.Injective (logicalKeyTerm RecursiveCollectionExecution.eventTerm) :=
  logicalKeyTerm_injective _ RecursiveCollectionExecution.decodeEvent? canonicalChoice_inverse

#print axioms ordinaryChoice?_choiceTerm
#print axioms canonicalChoice_inverse
#print axioms ordinary_logicalKeyTerm_injective
#print axioms canonical_logicalKeyTerm_injective

#print axioms observationNameTable_ordered
#print axioms observationNameTable_covers
#print axioms logical_keys_automatic_returns
#print axioms logical_bag_automatic_returns
#print axioms logical_facts_automatic_returns

#print axioms decodeLogicalKey?_logicalKeyTerm
#print axioms logicalKeyTerm_injective
#print axioms decodeLogicalKey?_wrong_constructor
#print axioms actual_key_coordinates
#print axioms logical_key_returns
#print axioms logical_keys_returns
#print axioms logical_keys_replay_returns
#print axioms logical_binary_returns
#print axioms logical_bag_returns
#print axioms logical_facts_returns

theorem canonical_native_logical_keys_returns (host : Effects.State)
    (pairs : List (Committed EquationalScopedReceipts.Event)) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-search:key-unique"
        [CompleteExecution.tableValue (observationNameTable pairs),
          encoded (encodeList Term.string ["x", "y", "z"]),
          encoded (encodeList
            (CollectionOccurrenceBatchExecution.committedTermWith RecursiveCollectionExecution.eventTerm) pairs)])
      host (encoded (encodeList (logicalKeyTerm RecursiveCollectionExecution.eventTerm)
        (orderedCommittedKeys logicalKey pairs))) :=
  logical_keys_automatic_returns _ key_metadata_agreement
    RecursiveCollectionExecution.eventTerm RecursiveCollectionExecution.decodeEvent?
    canonicalChoice_inverse host pairs
    (selected_canon_operations _ (observationNameTable_ordered pairs))

theorem canonical_native_logical_bag_returns (host : Effects.State)
    (pairs : List (Committed EquationalScopedReceipts.Event)) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-search:key-bag"
        [CompleteExecution.tableValue (observationNameTable pairs),
          encoded (encodeList Term.string ["x", "y", "z"]), encoded (.string "Edge"),
          encoded (encodeList
            (CollectionOccurrenceBatchExecution.committedTermWith RecursiveCollectionExecution.eventTerm) pairs)])
      host (encoded (encodeList InferenceCettaWire.encodePattern
        ((orderedCommittedKeys logicalKey pairs).filterMap logicalEdge?))) :=
  logical_bag_automatic_returns _ key_metadata_agreement
    RecursiveCollectionExecution.eventTerm RecursiveCollectionExecution.decodeEvent?
    canonicalChoice_inverse host pairs
    (selected_canon_operations _ (observationNameTable_ordered pairs))

theorem canonical_native_logical_facts_returns (host : Effects.State)
    (pairs : List (Committed EquationalScopedReceipts.Event)) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-search:key-facts"
        [CompleteExecution.tableValue (observationNameTable pairs),
          encoded (encodeList Term.string ["x", "y", "z"]), encoded (.string "Edge"),
          encoded (encodeList
            (CollectionOccurrenceBatchExecution.committedTermWith RecursiveCollectionExecution.eventTerm) pairs)])
      host (encoded (encodeList InferenceCettaWire.encodePattern
        ((orderedCommittedKeys logicalKey pairs).filterMap logicalEdge?).eraseDups)) :=
  logical_facts_automatic_returns _ key_metadata_agreement
    RecursiveCollectionExecution.eventTerm RecursiveCollectionExecution.decodeEvent?
    canonicalChoice_inverse host pairs
    (selected_canon_operations _ (observationNameTable_ordered pairs))

#print axioms canonical_native_logical_keys_returns
#print axioms canonical_native_logical_bag_returns
#print axioms canonical_native_logical_facts_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionExecutionQualification.GraphObservation

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionExecutionQualification.RetainedGraph

open Mettapedia.OSLF.MeTTaIL Syntax CollectionCommittedObservation
open Mettapedia.Machines.ResumableSearchRunner (Status)

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr}

abbrev Explorer (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr) :=
  Complete.Explore.Explorer Pattern (CollectionOccurrenceSearch.Run plan bound expected) GeneralRuleJobs.Receipt

def nodeEdges (node : Complete.Explore.Node Pattern
    (CollectionOccurrenceSearch.Run plan bound expected) GeneralRuleJobs.Receipt) :
    List (Pattern × Committed × Pattern) :=
  (CollectionOccurrenceSearch.publicationWithPackets node.run).map fun pair =>
    (node.state, pair, CanonicalBags.canon pair.2.target)

/-- Full committed pairs retain allocation origins beside the public receipt edges. -/
def edges (explorer : Explorer plan bound expected) : List (Pattern × Committed × Pattern) :=
  explorer.nodes.flatMap nodeEdges

def forget (edge : Pattern × Committed × Pattern) : Pattern × GeneralRuleJobs.Receipt × Pattern :=
  (edge.1, edge.2.1.2, edge.2.2)

theorem nodeEdges_forget (depth : Nat) (node : Complete.Explore.Node Pattern
    (CollectionOccurrenceSearch.Run plan bound expected) GeneralRuleJobs.Receipt) :
    (nodeEdges node).map forget =
      Complete.Graph.nodeEdges (CollectionOccurrenceSearch.search plan bound expected depth) node := by
  have same := congrArg
    (List.map fun receipt : GeneralRuleJobs.Receipt =>
      (node.state, receipt, CanonicalBags.canon receipt.target))
    (CollectionOccurrenceSearch.publicationWithPackets_forgets depth node.run)
  simpa only [nodeEdges, forget, List.map_map, Function.comp_def, Complete.Graph.nodeEdges,
    CollectionOccurrenceSearch.search] using same

theorem edges_forget (depth : Nat) (explorer : Explorer plan bound expected) :
    (edges explorer).map forget =
      Complete.Graph.edges (CollectionOccurrenceSearch.search plan bound expected depth) explorer := by
  simp only [edges, List.map_flatMap, Complete.Graph.edges]
  apply congrArg (fun f => explorer.nodes.flatMap f)
  funext node
  exact nodeEdges_forget depth node

theorem every_public_edge_has_pair (depth : Nat) (explorer : Explorer plan bound expected)
    (edge : Pattern × GeneralRuleJobs.Receipt × Pattern)
    (published : edge ∈ Complete.Graph.edges
      (CollectionOccurrenceSearch.search plan bound expected depth) explorer) :
    ∃ rich ∈ edges explorer, forget rich = edge := by
  rw [← edges_forget depth explorer] at published
  exact List.mem_map.mp published

/-- Retained nodes expose pending agendas and blocked work through their actual runs. -/
def unfinished (depth : Nat) (explorer : Explorer plan bound expected) :=
  explorer.nodes.filter fun node =>
    !Complete.Settled.nodeSettled (CollectionOccurrenceSearch.search plan bound expected depth) node

theorem unfinished_eq_nil_iff (depth : Nat) (explorer : Explorer plan bound expected) :
    unfinished depth explorer = [] ↔
      Complete.Settled.settled (CollectionOccurrenceSearch.search plan bound expected depth) explorer = true := by
  simp only [unfinished, List.filter_eq_nil_iff, Complete.Settled.settled, List.all_eq_true]
  constructor
  · intro none node member
    have absent := none node member
    cases status : Complete.Settled.nodeSettled
        (CollectionOccurrenceSearch.search plan bound expected depth) node <;> simp_all
  · intro all node member
    rw [all node member]
    decide

#print axioms nodeEdges_forget
#print axioms edges_forget
#print axioms every_public_edge_has_pair
#print axioms unfinished_eq_nil_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionExecutionQualification.RetainedGraph
