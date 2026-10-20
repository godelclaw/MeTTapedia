import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPlanExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Candidates
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend

/-!
# Native collection matcher backend

The backend turns one checked collection allocation into an ordinary scoped
matcher request.  Its returned answers are therefore suitable for the shared
typed/premise/reduct continuation.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionSelection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_backend.metta"
    sha256 "e401dcd56c3e456ecf28547ee295a67683b5ee59af7134bfc7ce5499d471a31e"

def collectionBaseSource : SpaceSemantics.Program :=
  CollectionSelectionExecution.source.program.append ScopedCollectionExecution.source.program

def collectionBaseLibrary : BridgeKit.Library :=
  ⟨CompleteExecution.completeLibrary.runtime, collectionBaseSource,
    ["gslt:collection:", "gslt:collection-machine:", "gslt:collection-plan:"]⟩

theorem collectionBase_checked : collectionBaseLibrary.check = true := by decide +kernel

def library : BridgeKit.Library :=
  ⟨collectionBaseLibrary.runtime, source.program, ["gslt:collection-backend:"]⟩

theorem checked : library.check = true := by decide +kernel

private abbrev patternValue (pattern : Pattern) : Atom :=
  encoded (InferenceCettaWire.encodePattern pattern)

def rawOrdinaryTarget (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) : Pattern :=
  .collection request.kind
    (receipt.allocation.values ++ receipt.allocation.residual) none

theorem rawOrdinaryTarget_eq (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt)
    (fixed : CanonicalBags.arrange request.kind receipt.allocation.residual =
      receipt.allocation.residual) :
    rawOrdinaryTarget request receipt =
      CollectionMatcherCompatibility.ordinaryTarget request receipt := by
  simp [rawOrdinaryTarget, CollectionMatcherCompatibility.ordinaryTarget, fixed]

syntax "collection_backend_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| collection_backend_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        $extra,*]))

theorem backend_append_returns (state : State) : ∀ (left right : List Pattern),
    PureReturns library.runtime [] state
      (apply "gslt:automata:append"
        [encoded (encodeList InferenceCettaWire.encodePattern left),
          encoded (encodeList InferenceCettaWire.encodePattern right)])
      state (encoded (encodeList InferenceCettaWire.encodePattern (left ++ right)))
  | left, right => by
      have atCollectionBase : PureReturns collectionBaseLibrary.runtime [] state
          (apply "gslt:automata:append"
            [encoded (encodeList InferenceCettaWire.encodePattern left),
              encoded (encodeList InferenceCettaWire.encodePattern right)])
          state (encoded (encodeList InferenceCettaWire.encodePattern (left ++ right))) := by
        metta_lift collectionBase_checked ["left", "right"]
          (CompleteExecution.complete_append_returns InferenceCettaWire.encodePattern state left right)
      metta_lift checked ["left", "right"] atCollectionBase

private theorem pcollection_template :
    PureData.Template library.runtime
      (a "PCollection" [v "kind", v "presented", .symbol "RNone"]) := by
  apply PureData.Template.constructor "PCollection" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .captured _
  · exact .captured _
  · exact .symbol _

@[metta_head "gslt:collection-backend:ordinary-target"]
theorem ordinary_target_returns (state : State)
    (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:ordinary-target"
        [encoded (InferenceCettaWire.encodeCollectionType request.kind),
          encoded (encodeList InferenceCettaWire.encodePattern receipt.allocation.values),
          encoded (encodeList InferenceCettaWire.encodePattern receipt.allocation.residual)])
      state (patternValue (rawOrdinaryTarget request receipt)) := by
  have joined := backend_append_returns state receipt.allocation.values receipt.allocation.residual
  let caller :=
    ("presented", encoded (encodeList InferenceCettaWire.encodePattern
      (receipt.allocation.values ++ receipt.allocation.residual))) ::
    Library.bind ["kind", "values", "residual"]
      [encoded (InferenceCettaWire.encodeCollectionType request.kind),
        encoded (encodeList InferenceCettaWire.encodePattern receipt.allocation.values),
        encoded (encodeList InferenceCettaWire.encodePattern receipt.allocation.residual)]
  have returned := PureData.template_return library.runtime caller state
    (a "PCollection" [v "kind", v "presented", .symbol "RNone"])
    pcollection_template
  cases kind : request.kind <;> all_goals
    have returned' : PureReturns library.runtime caller state
        (a "PCollection" [v "kind", v "presented", .symbol "RNone"]) state
        (patternValue (rawOrdinaryTarget request receipt)) := by
      simpa [caller, patternValue, rawOrdinaryTarget, kind, Library.bind, encoded,
        CettaWireAtom.encode, CettaWireAtom.encodeMany,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
        InferenceCettaWire.encodePattern, InferenceCettaWire.encodeCollectionType,
        InferenceCettaWire.encodeRest,
        InferenceCettaWire.encodePatterns_eq_encodeList, encodeList] using returned
    metta_call checked
    apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
    · metta_capture_any joined unfolding [InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodeCollectionType, kind, encodeList]
    · simpa only [caller, kind] using returned'

def rawOrdinaryRequest (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) : GeneralScopedMatchMachine.Request :=
  { request.machine with target := rawOrdinaryTarget request receipt }

@[metta_head "gslt:collection-backend:ordinary-request"]
theorem ordinary_request_returns (state : State)
    (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:ordinary-request"
        [encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.machine.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.machine.spec),
          number request.machine.ambient,
          encoded (InferenceCettaWire.AuthoredRule.siteTerm request.machine.site),
          encoded (encodeList Term.natural request.machine.path),
          number request.machine.depth,
          encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
            request.machine.initial),
          patternValue request.machine.schema,
          patternValue (rawOrdinaryTarget request receipt)])
      state (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (rawOrdinaryRequest request receipt))) := by
  cases kind : request.kind <;>
    collection_backend_eval unfolding [patternValue,
      ScopedCollectionMachine.Request.machine, rawOrdinaryRequest, rawOrdinaryTarget,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      InferenceCettaWire.AuthoredRule.rewriteTerm,
      InferenceCettaWire.AuthoredRule.bindingSpecTerm,
      InferenceCettaWire.AuthoredRule.siteTerm,
      MatchAutomataBindingExecution.patternsTerm, InferenceCettaWire.encodePattern,
      InferenceCettaWire.encodePatterns_eq_encodeList, InferenceCettaWire.encodeRest,
      InferenceCettaWire.encodeCollectionType, kind, encodeList, patternValue]

/-- Keep every ordinary matcher answer with the allocation's assignment.  The
trace remains untouched, so multiple origins for the same assignment remain
distinct answer occurrences. -/
def filterAnswers (assignment : ScopedRuleMatching.Assignment) :
    List GeneralScopedMatchMachine.Answer → List GeneralScopedMatchMachine.Answer
  | answers => answers.filter fun answer => answer.assignment == assignment

@[metta_head "gslt:collection-backend:filter-assignment"]
theorem filter_assignment_returns (state : State)
    (assignment : ScopedRuleMatching.Assignment) :
    ∀ answers : List GeneralScopedMatchMachine.Answer,
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:filter-assignment"
        [encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment),
          encoded (encodeList RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm answers)])
      state (encoded (encodeList RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm
        (filterAnswers assignment answers)))
  | [] => by
      collection_backend_eval unfolding [filterAnswers]
  | answer :: rest => by
      have later := filter_assignment_returns state assignment rest
      by_cases same : answer.assignment = assignment
      · metta_call checked
        all_goals simp [filterAnswers, same,
          RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
          RuleInstantiationExecution.GeneralExecution.traceTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList, Library.bind]
        metta_eval [later] with checked unfolding [filterAnswers, same,
          RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
          RuleInstantiationExecution.GeneralExecution.traceTerm,
          RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective.eq_iff,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList]
      · have wire_ne :
            RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm answer.assignment ≠
              RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment :=
          fun equal => same
            (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective equal)
        metta_call checked
        all_goals simp [filterAnswers, same,
          RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
          RuleInstantiationExecution.GeneralExecution.traceTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList, Library.bind]
        metta_eval [later] with checked unfolding [filterAnswers, same, wire_ne,
          RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
          RuleInstantiationExecution.GeneralExecution.traceTerm,
          RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective.eq_iff,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList]

/-- The complete ordinary matcher answers selected by one collection
allocation.  This is the executable counterpart of the proof-relevant
`adaptations` list. -/
def backendAnswers (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) :
    List GeneralScopedMatchMachine.Answer :=
  filterAnswers receipt.matching.assignment
    (CompleteExecution.finishedAnswers (rawOrdinaryRequest request receipt))

@[metta_head "gslt:collection-backend:answers"]
theorem answers_returns (state : State)
    (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-backend:answers"
        [encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
            (rawOrdinaryRequest request receipt)),
          encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
            receipt.matching.assignment)])
      state (encoded (encodeList RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm
        (backendAnswers request receipt))) := by
  have answeredAtBase : PureReturns collectionBaseLibrary.runtime [] state
      (apply "gslt:complete:matcher-answers"
        [encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
          (rawOrdinaryRequest request receipt))])
      state (encoded (encodeList RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm
        (CompleteExecution.finishedAnswers (rawOrdinaryRequest request receipt)))) := by
    metta_lift collectionBase_checked ["request"]
      (CompleteExecution.matcher_answers_returns state (rawOrdinaryRequest request receipt))
  have answered : PureReturns library.runtime [] state
      (apply "gslt:complete:matcher-answers"
        [encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
          (rawOrdinaryRequest request receipt))])
      state (encoded (encodeList RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm
        (CompleteExecution.finishedAnswers (rawOrdinaryRequest request receipt)))) := by
    metta_lift checked ["request"] answeredAtBase
  have filtered := filter_assignment_returns state receipt.matching.assignment
    (CompleteExecution.finishedAnswers (rawOrdinaryRequest request receipt))
  metta_call checked
  metta_eval [answered, filtered] with checked unfolding [backendAnswers]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution
