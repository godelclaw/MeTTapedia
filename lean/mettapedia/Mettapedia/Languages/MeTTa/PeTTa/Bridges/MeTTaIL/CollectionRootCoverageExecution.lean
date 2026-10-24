import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RootCollection
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionCodec
import Mettapedia.OSLF.MeTTaIL.CollectionRootCoverage

/-!
# Native root frontiers and their source meaning

The native search dictionary computes the same retained frontier as Lean.
For a recognized root profile, a complete frontier is exactly the successor
relation of the independently defined presented GSLT. The actual output is
the full ordered receipt list, including equal targets from distinct origins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RootCollection

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit

/-- Decode against the request derived from the actual source and authored
declaration position. Arbitrary wire requests do not acquire source authority. -/
def decodeReceiptFor? (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan) (source : Pattern) :
    Term → Option CollectionRootSearch.Receipt
  | .application "CollectionRootReceipt" [.natural ordinal, query, raw, completed, history, target] => do
      let request ← CollectionExecutionAdmission.requestForSource? plan certificate ordinal source
      guard (ScopedCollectionExecution.requestTerm request == query)
      pure ⟨⟨ordinal, request, ← ScopedCollectionCodec.receipt? raw⟩,
        ← ScopedRuleJobReadoutExecution.decodeAssignment? completed,
        ← ScopedRuleJobReadoutExecution.decodeEvents? history,
        ← InferenceCettaWire.decodePattern target⟩
  | _ => none

theorem decodeReceiptFor?_receiptTerm
    {plan : GeneralExecutionAdmission.Plan} {profile : CollectionRootSearch.Profile plan}
    {expected : TypeExpr} {source : Pattern} {receipt : CollectionRootSearch.Receipt}
    (valid : receipt.Valid (profile := profile) expected source) :
    decodeReceiptFor? plan profile.collection source (receiptTerm receipt) = some receipt := by
  have selected := CollectionExecutionAdmission.requestsForSource_selected valid.1.origin
  obtain ⟨⟨ordinal, request, raw⟩, completed, history, target⟩ := receipt
  simp [receiptTerm, decodeReceiptFor?, selected]

/-- Valid packet identities survive serialization, including their raw
allocation origin, captures, premise history and target. -/
theorem receiptTerm_injective_valid
    {plan : GeneralExecutionAdmission.Plan} {profile : CollectionRootSearch.Profile plan}
    {expected : TypeExpr} {source : Pattern} {left right : CollectionRootSearch.Receipt}
    (validLeft : left.Valid (profile := profile) expected source)
    (validRight : right.Valid (profile := profile) expected source)
    (same : receiptTerm left = receiptTerm right) : left = right := by
  have decoded := congrArg (decodeReceiptFor? plan profile.collection source) same
  simpa only [decodeReceiptFor?_receiptTerm validLeft,
    decodeReceiptFor?_receiptTerm validRight, Option.some.injEq] using decoded

/-- Source-valid packet lists round-trip with their order and multiplicity.
This decoder is a representation check, not a new firing-validity checker. -/
theorem decodeReceiptList_encoded
    {plan : GeneralExecutionAdmission.Plan} {profile : CollectionRootSearch.Profile plan}
    (expected : TypeExpr) (source : Pattern) (receipts : List CollectionRootSearch.Receipt)
    (valid : ∀ receipt ∈ receipts, receipt.Valid (profile := profile) expected source) :
    decodeList (decodeReceiptFor? plan profile.collection source) (encodeList receiptTerm receipts) = some receipts := by
  induction receipts with
  | nil => simp [encodeList, decodeList]
  | cons receipt receipts ih =>
    have first := decodeReceiptFor?_receiptTerm (valid receipt List.mem_cons_self)
    have rest := ih (fun other member => valid other (List.mem_cons_of_mem _ member))
    simp [encodeList, decodeList, first, rest]

theorem receiptList_encoding_injective_valid
    {plan : GeneralExecutionAdmission.Plan} {profile : CollectionRootSearch.Profile plan}
    (expected : TypeExpr) (source : Pattern) {left right : List CollectionRootSearch.Receipt}
    (validLeft : ∀ receipt ∈ left, receipt.Valid (profile := profile) expected source)
    (validRight : ∀ receipt ∈ right, receipt.Valid (profile := profile) expected source)
    (same : encodeList receiptTerm left = encodeList receiptTerm right) : left = right := by
  have decoded := congrArg (decodeList (decodeReceiptFor? plan profile.collection source)) same
  simpa only [decodeReceiptList_encoded expected source left validLeft,
    decodeReceiptList_encoded expected source right validRight, Option.some.injEq] using decoded

theorem published_packets_roundtrip
    {plan : GeneralExecutionAdmission.Plan} {profile : CollectionRootSearch.Profile plan}
    (expected : TypeExpr) (run : CollectionRootSearch.Run (profile := profile) expected) :
    decodeList (decodeReceiptFor? plan profile.collection run.source)
      (encodeList receiptTerm (CollectionRootSearch.publication expected run)) =
        some (CollectionRootSearch.publication expected run) :=
  decodeReceiptList_encoded expected run.source _ (fun _ member =>
    CollectionRootSearch.publication_sound expected run member)

/-- The execution refinement and the source interpretation meet at the same
frontier. Readiness comes from source names and canonicalization; source
coverage comes from rule and algebra conditions in the recognized profile. -/
theorem complete_source_frontier
    {plan : GeneralExecutionAdmission.Plan} (certificate : CollectionRootSearch.CoverageProfile plan)
    (expected : TypeExpr) (names footprint : List String)
    (scope : Complete.Footprint.Scope plan footprint) (state : Effects.State)
    (source : Pattern) (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) (work : Nat)
    (complete : (CollectionRootSearch.search (profile := certificate.profile) expected).status
      ((CollectionRootSearch.search (profile := certificate.profile) expected).run
        (CanonicalBags.canon source) work) = .complete) :
    let run := (CollectionRootSearch.search (profile := certificate.profile) expected).run
      (CanonicalBags.canon source) work
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:run"
        [encoded (backendTerm names), planValue plan (plan.snapshot.free.entriesOn footprint) [] expected,
          patternValue (CanonicalBags.canon source), number work])
      state (encoded (runTerm run)) ∧
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:publication" [encoded (backendTerm names), encoded (runTerm run)])
      state (encoded (encodeList receiptTerm (CollectionRootSearch.publication expected run))) ∧
    PureReturns runnerLibrary.runtime [] state
      (apply "gslt:search:status" [encoded (backendTerm names),
        planValue plan (plan.snapshot.free.entriesOn footprint) [] expected, encoded (runTerm run)])
      state (.symbol "SearchComplete") ∧
    ∀ target, (Complete.Presented.gslt plan [] expected).Step source (CanonicalBags.canon target) ↔
      ∃ receipt, receipt ∈ CollectionRootSearch.publication expected run ∧
        CanonicalBags.canon receipt.target = CanonicalBags.canon target := by
  dsimp only
  have readyNames : ∀ name ∈ (CanonicalBags.canon source).freeFvarNames, name ∈ footprint :=
    fun name member => inside name ((CanonicalBags.canon_freeFvarNames source name).mp member)
  refine ⟨search_run_returns state names footprint scope _ readyNames
    (CollectionRequestExecution.arrangedRoot_canon source) work,
    search_publication_returns state names _, ?_, ?_⟩
  · have native := search_status_returns state names
      (planValue plan (plan.snapshot.free.entriesOn footprint) [] expected)
      ((CollectionRootSearch.search (profile := certificate.profile) expected).run
        (CanonicalBags.canon source) work)
    have done : CollectionRootSearch.status expected
        ((CollectionRootSearch.search (profile := certificate.profile) expected).run
          (CanonicalBags.canon source) work) = .complete := complete
    simpa only [done, SearchRunner.statusAtom] using native
  · intro target
    exact CollectionRootSearch.presented_iff_complete_publication certificate expected source target work complete

/-- The actual native dictionary publishes exactly the source-derived
finite continuation-account multiset. Its chronological order may interleave
origins; no occurrence is dropped or multiplied by that interleaving. -/
theorem source_packet_multiset_returns
    {plan : GeneralExecutionAdmission.Plan} (profile : CollectionRootSearch.Profile plan)
    (expected : TypeExpr) (names footprint : List String)
    (scope : Complete.Footprint.Scope plan footprint) (state : Effects.State)
    (source : Pattern)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free [] expected source)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint)
    (arranged : CollectionRequestExecution.ArrangedRoot source) :
    ∃ matching : CollectionRootSearch.Matching plan profile source,
      CollectionPlanMachine.complete matching.state = true ∧
      ∃ work,
        (CollectionRootSearch.search (profile := profile) expected).status
          ((CollectionRootSearch.search (profile := profile) expected).run source work) = .complete ∧
        PureReturns runnerLibrary.runtime [] state
          (apply "gslt:search:run"
            [encoded (backendTerm names), planValue plan (plan.snapshot.free.entriesOn footprint) [] expected,
              patternValue source, number work])
          state (encoded (runTerm ((CollectionRootSearch.search (profile := profile) expected).run source work))) ∧
        PureReturns runnerLibrary.runtime [] state
          (apply "gslt:search:publication" [encoded (backendTerm names),
            encoded (runTerm ((CollectionRootSearch.search (profile := profile) expected).run source work))])
          state (encoded (encodeList receiptTerm (CollectionRootSearch.publication expected
            ((CollectionRootSearch.search (profile := profile) expected).run source work)))) ∧
        (CollectionRootSearch.publication expected
          ((CollectionRootSearch.search (profile := profile) expected).run source work)).Perm
          ((matching.matches.flatMap fun origin => CollectionRootSearch.continuationPackets
            origin.val origin.property typed (CollectionRootSearch.depth origin.val)).map CollectionRootSearch.observe) := by
  obtain ⟨matching, matched, work, complete, accounted⟩ :=
    CollectionRootSearch.root_publication_multiset_exact source typed
  exact ⟨matching, matched, work, complete,
    search_run_returns state names footprint scope source inside arranged work,
    search_publication_returns state names _, accounted⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RootCollection
