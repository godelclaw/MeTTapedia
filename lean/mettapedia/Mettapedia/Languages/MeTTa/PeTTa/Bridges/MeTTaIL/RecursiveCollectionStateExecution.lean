import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionTraceAccounting
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionHandoff

/-!
# Native retained states for recursive collection matching

The checked expansion feeds the retained task scheduler. Resuming carries the
same agenda, assignments and full allocation histories. The finite input's
name-table coverage is preserved by every transition.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RecursiveCollectionMachine CanonicalCompare
open RuleInstantiationExecution.GeneralExecution
open RuleInstantiationExecution.ScopedCapture (scopedAssignmentTerm)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit

@[metta_head "gslt:recursive-collection:advance"]
theorem advance_returns (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request) (work : Work)
    (covered : WorkCovered names work) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:advance" [encoded (encodeList Term.string names),
        encoded (matcherRequestTerm request), encoded (workTerm work)])
      state (encoded (encodeList workTerm (advance request work))) := by
  cases taskList : work.tasks with
  | nil =>
    recursive_collection_eval unfolding [RecursiveCollectionMachine.advance, taskList]
  | cons task remaining =>
    have expanded := expand_returns state names ordered request work.assignment task
      (covered task (by simp [taskList]))
    have continued := branches_returns state remaining work.trace (expand request work.assignment task)
    simp only [RecursiveCollectionMachine.advance, taskList]
    recursive_collection_eval [expanded, continued]
      unfolding [RecursiveCollectionMachine.advance, taskList]

@[metta_head "gslt:recursive-collection:tick"]
theorem tick_returns (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request) (machine : RecursiveCollectionMachine.State)
    (covered : StateCovered names machine) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:tick" [encoded (encodeList Term.string names),
        encoded (matcherRequestTerm request), encoded (stateTerm machine)])
      state (encoded (stateTerm (tick request machine))) := by
  cases agenda : machine.agenda with
  | nil =>
    recursive_collection_eval unfolding [RecursiveCollectionMachine.tick, agenda]
  | cons work remaining =>
    cases taskList : work.tasks with
    | nil =>
      recursive_collection_eval
        [append_returns answerTerm state machine.answers [⟨work.assignment, work.trace⟩]]
        unfolding [RecursiveCollectionMachine.tick, agenda, taskList]
    | cons task tasks =>
      recursive_collection_eval
        [advance_returns state names ordered request work (covered work (by simp [agenda])),
         append_returns workTerm state (advance request work) remaining]
        unfolding [RecursiveCollectionMachine.tick, agenda, taskList]

/-- Every work allowance has the exact retained state represented in MeTTa.
The theorem includes unfinished branches, rather than only final answers. -/
@[metta_head "gslt:recursive-collection:run"]
theorem run_returns (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request) :
    ∀ (fuel : Nat) (machine : RecursiveCollectionMachine.State), StateCovered names machine →
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:run" [encoded (encodeList Term.string names),
        encoded (matcherRequestTerm request), number fuel, encoded (stateTerm machine)])
      state (encoded (stateTerm (run request fuel machine)))
  | 0, machine, _ => by
    recursive_collection_eval unfolding [RecursiveCollectionMachine.run]
  | fuel + 1, machine, covered => by
    recursive_collection_eval
      [tick_returns state names ordered request machine covered,
       run_returns state names ordered request fuel (tick request machine)
         (tick_covered request names covered)]
      unfolding [RecursiveCollectionMachine.run]

/-- The initial input supplies the finite name support for every resumed run. -/
theorem run_from_start_returns (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request)
    (covered : Covered names request.target) (fuel : Nat) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:run" [encoded (encodeList Term.string names),
        encoded (matcherRequestTerm request), number fuel, encoded (stateTerm (start request))])
      state (encoded (stateTerm (run request fuel (start request)))) :=
  run_returns state names ordered request fuel (start request) (start_covered names request covered)

/-- Native retained execution reaches the entire independently valid trace
reference at some finite allowance. This is local matching exhaustion, not a
termination claim about a source program or its reachable state space. -/
theorem finite_native_receipts (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request) (covered : Covered names request.target) :
    ∃ fuel,
      PureReturns library.runtime [] state
        (apply "gslt:recursive-collection:run" [encoded (encodeList Term.string names),
          encoded (matcherRequestTerm request), number fuel, encoded (stateTerm (start request))])
        state (encoded (stateTerm (run request fuel (start request)))) ∧
      complete (run request fuel (start request)) = true ∧
      ∀ answer, answer ∈ (run request fuel (start request)).answers ↔
        EquationalScopedReceipts.Matches ScopedRuleMatching.literalBodyComparison
          request.rule request.spec request.ambient request.site request.path request.depth
          request.initial request.schema request.target answer.trace answer.assignment := by
  obtain ⟨fuel, finished⟩ := finiteDrain request (start request)
  refine ⟨fuel, run_from_start_returns state names ordered request covered fuel, finished, ?_⟩
  intro answer
  rw [completed_traces request fuel finished]
  exact referenceAt_exact

/-- The native matcher realizes the allocation interpretation used by the
shared premise judgments. Finite local exhaustion supplies every independent
match receipt; it does not assert completion of child-step exploration. -/
theorem finite_interpreted_receipts (state : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request) (covered : Covered names request.target) :
    ∃ fuel,
      PureReturns library.runtime [] state
        (apply "gslt:recursive-collection:run" [encoded (encodeList Term.string names),
          encoded (matcherRequestTerm request), number fuel, encoded (stateTerm (start request))])
        state (encoded (stateTerm (run request fuel (start request)))) ∧
      complete (run request fuel (start request)) = true ∧
      ∀ answer, answer ∈ (run request fuel (start request)).answers ↔
        (RecursiveCollectionHandoff.matchingInterpretation ScopedRuleMatching.literalBodyComparison).Matches
          request answer.trace answer.assignment := by
  obtain ⟨fuel, native, finished, exactReceipts⟩ := finite_native_receipts state names ordered request covered
  exact ⟨fuel, native, finished, exactReceipts⟩

/-- The request's finite name support covers every resumed canonical state. -/
theorem canonical_reachable_covered (names : List String) (ordered : NameOrdered names)
    (request : Request) (machine : Request × RecursiveCollectionMachine.State)
    (reached : RecursiveCollectionHandoff.canonicalMatchingExecution.Reachable request machine)
    (covered : Covered names request.target) : StateCovered names machine.2 := by
  obtain ⟨fuel, rfl⟩ := reached
  exact run_covered (RecursiveCollectionHandoff.canonicalRequest request) names fuel
    (start_covered names (RecursiveCollectionHandoff.canonicalRequest request)
      (canonBy_eq_canon ordered request.target covered).2)

#print axioms canonical_reachable_covered

@[metta_head "gslt:canon:canon"]
theorem canonical_pattern_returns (host : Effects.State) (names : List String)
    (ordered : NameOrdered names) (pattern : Pattern) (covered : Covered names pattern) :
    PureReturns library.runtime [] host
      (apply "gslt:canon:canon" [encoded (encodeList Term.string names),
        encoded (InferenceCettaWire.encodePattern pattern)])
      host (encoded (InferenceCettaWire.encodePattern (CanonicalBags.canon pattern))) := by
  exact CompleteExecution.canon_returns host ordered pattern covered

@[metta_head "gslt:recursive-collection:canonical-request"]
theorem canonical_request_returns (host : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request) (covered : Covered names request.target) :
    PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:canonical-request"
        [encoded (encodeList Term.string names), encoded (matcherRequestTerm request)])
      host (encoded (matcherRequestTerm (RecursiveCollectionHandoff.canonicalRequest request))) := by
  recursive_collection_eval [canonical_pattern_returns host names ordered request.target covered]
    unfolding [RecursiveCollectionHandoff.canonicalRequest, matcherRequestTerm]

@[metta_head "gslt:recursive-collection:canonical-start"]
theorem canonical_start_returns (host : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request) (covered : Covered names request.target) :
    PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:canonical-start"
        [encoded (encodeList Term.string names), encoded (matcherRequestTerm request)])
      host (encoded (canonicalStateTerm
        (RecursiveCollectionHandoff.canonicalMatchingExecution.start request))) := by
  recursive_collection_eval [canonical_request_returns host names ordered request covered,
    start_returns host (RecursiveCollectionHandoff.canonicalRequest request)]
    unfolding [canonicalStateTerm, RecursiveCollectionHandoff.canonicalMatchingExecution]

@[metta_head "gslt:recursive-collection:canonical-tick"]
theorem canonical_tick_returns (host : Effects.State) (names : List String)
    (ordered : NameOrdered names) (request : Request)
    (machine : Request × RecursiveCollectionMachine.State) (covered : StateCovered names machine.2) :
    PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:canonical-tick"
        [encoded (encodeList Term.string names), encoded (canonicalStateTerm machine)])
      host (encoded (canonicalStateTerm
        (RecursiveCollectionHandoff.canonicalMatchingExecution.tick request machine))) := by
  recursive_collection_eval [tick_returns host names ordered machine.1 machine.2 covered]
    unfolding [canonicalStateTerm, RecursiveCollectionHandoff.canonicalMatchingExecution]

@[metta_head "gslt:recursive-collection:canonical-complete"]
theorem canonical_complete_returns (host : Effects.State)
    (machine : Request × RecursiveCollectionMachine.State) :
    PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:canonical-complete" [encoded (canonicalStateTerm machine)])
      host (Effects.boolean (RecursiveCollectionHandoff.canonicalMatchingExecution.complete machine)) := by
  recursive_collection_eval [complete_returns host machine.2]
    unfolding [canonicalStateTerm, RecursiveCollectionHandoff.canonicalMatchingExecution]

@[metta_head "gslt:rule:row-at"]
theorem canonical_row_returns (host : Effects.State) (answers : List RecursiveCollectionMachine.Answer)
    (cursor : Nat) :
    PureReturns library.runtime [] host
      (apply "gslt:rule:row-at" [number cursor, encoded (encodeList answerTerm answers)])
      host (encoded (encodeOption answerTerm answers[cursor]?)) := by
  exact CollectionSelectionExecution.row_returns answerTerm host answers cursor

@[metta_head "gslt:recursive-collection:canonical-answer-at"]
theorem canonical_answer_at_returns (host : Effects.State)
    (machine : Request × RecursiveCollectionMachine.State) (cursor : Nat) :
    PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:canonical-answer-at"
        [encoded (canonicalStateTerm machine), number cursor])
      host (encoded (encodeOption canonicalAnswerTerm machine.2.answers[cursor]?)) := by
  have selected := canonical_row_returns host machine.2.answers cursor
  cases found : machine.2.answers[cursor]? <;>
    recursive_collection_eval [selected]
      unfolding [canonicalStateTerm, canonicalAnswerTerm, found]

@[metta_head "gslt:recursive-collection:canonical-input"]
theorem canonical_input_returns (host : Effects.State) (names : List String)
    (ordered : NameOrdered names) (actual expected : Pattern)
    (actualCovered : Covered names actual) (expectedCovered : Covered names expected) :
    PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:canonical-input"
        [encoded (encodeList Term.string names), encoded (InferenceCettaWire.encodePattern actual),
          encoded (InferenceCettaWire.encodePattern expected)])
      host (Effects.boolean (CanonicalBags.canon actual == CanonicalBags.canon expected)) := by
  have left := canonical_pattern_returns host names ordered actual actualCovered
  have right := canonical_pattern_returns host names ordered expected expectedCovered
  recursive_collection_eval [left, right]
  have encoding : decide (InferenceCettaWire.encodePattern (CanonicalBags.canon actual) =
      InferenceCettaWire.encodePattern (CanonicalBags.canon expected)) =
      (CanonicalBags.canon actual == CanonicalBags.canon expected) := by
    by_cases same : CanonicalBags.canon actual = CanonicalBags.canon expected
    · rw [same]
      simp [BEq.beq]
    · have different : InferenceCettaWire.encodePattern (CanonicalBags.canon actual) ≠
        InferenceCettaWire.encodePattern (CanonicalBags.canon expected) :=
        fun equal => same (InferenceCettaWire.encodePattern_injective equal)
      simp [BEq.beq, same, different]
  rw [← encoding]
  exact term_equal_returns library.runtime _ host (.var "left") (.var "right") _ _
    (by apply bound_returns; simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup])
    (by apply bound_returns; simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup])

syntax "matching_dispatch_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| matching_dispatch_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, RetainedMatchingWire.interpretedEnvironmentTerm,
        encodeList, encodeOption, $extra,*]))

@[metta_head "gslt:premise:matching-environment"]
theorem matching_environment_returns (host : Effects.State) (names : List String) (core : Term) :
    PureReturns library.runtime [] host
      (apply "gslt:premise:matching-environment" [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names core)])
      host (encoded core) := by
  matching_dispatch_eval

@[metta_head "gslt:premise:matching-start"]
theorem matching_start_returns (host : Effects.State) (names : List String) (core : Term)
    (ordered : NameOrdered names) (request : Request) (covered : Covered names request.target) :
    PureReturns library.runtime [] host
      (apply "gslt:premise:matching-start" [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names core),
        encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm request)])
      host (encoded (RecursiveCollectionExecution.canonicalStateTerm
        (RecursiveCollectionHandoff.canonicalMatchingExecution.start request))) := by
  have started : PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:canonical-start" [encoded (encodeList Term.string names),
        encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm request)])
      host (encoded (RecursiveCollectionExecution.canonicalStateTerm
        (RecursiveCollectionHandoff.canonicalMatchingExecution.start request))) := by
    exact RecursiveCollectionExecution.canonical_start_returns host names ordered request covered
  matching_dispatch_eval [started]

@[metta_head "gslt:premise:matching-tick"]
theorem matching_tick_returns (host : Effects.State) (names : List String) (core : Term)
    (ordered : NameOrdered names) (request : Request)
    (machine : Request × RecursiveCollectionMachine.State)
    (covered : StateCovered names machine.2) :
    PureReturns library.runtime [] host
      (apply "gslt:premise:matching-tick" [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names core),
        encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm request),
        encoded (RecursiveCollectionExecution.canonicalStateTerm machine)])
      host (encoded (RecursiveCollectionExecution.canonicalStateTerm
        (RecursiveCollectionHandoff.canonicalMatchingExecution.tick request machine))) := by
  have stepped : PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:canonical-tick" [encoded (encodeList Term.string names),
        encoded (RecursiveCollectionExecution.canonicalStateTerm machine)])
      host (encoded (RecursiveCollectionExecution.canonicalStateTerm
        (RecursiveCollectionHandoff.canonicalMatchingExecution.tick request machine))) := by
    exact RecursiveCollectionExecution.canonical_tick_returns host names ordered request machine covered
  matching_dispatch_eval [stepped]

@[metta_head "gslt:premise:matching-complete"]
theorem matching_complete_returns (host : Effects.State) (names : List String) (core : Term)
    (machine : Request × RecursiveCollectionMachine.State) :
    PureReturns library.runtime [] host
      (apply "gslt:premise:matching-complete" [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names core),
        encoded (RecursiveCollectionExecution.canonicalStateTerm machine)])
      host (Effects.boolean (RecursiveCollectionHandoff.canonicalMatchingExecution.complete machine)) := by
  have completed : PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:canonical-complete"
        [encoded (RecursiveCollectionExecution.canonicalStateTerm machine)])
      host (Effects.boolean (RecursiveCollectionHandoff.canonicalMatchingExecution.complete machine)) := by
    exact RecursiveCollectionExecution.canonical_complete_returns host machine
  matching_dispatch_eval [completed]

@[metta_head "gslt:premise:matching-answer-at"]
theorem matching_answer_at_returns (host : Effects.State) (names : List String) (core : Term)
    (machine : Request × RecursiveCollectionMachine.State) (cursor : Nat) :
    PureReturns library.runtime [] host
      (apply "gslt:premise:matching-answer-at" [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names core),
        encoded (RecursiveCollectionExecution.canonicalStateTerm machine), number cursor])
      host (encoded (encodeOption RecursiveCollectionExecution.canonicalAnswerTerm machine.2.answers[cursor]?)) := by
  have readout : PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:canonical-answer-at"
        [encoded (RecursiveCollectionExecution.canonicalStateTerm machine), number cursor])
      host (encoded (encodeOption RecursiveCollectionExecution.canonicalAnswerTerm machine.2.answers[cursor]?)) := by
    exact RecursiveCollectionExecution.canonical_answer_at_returns host machine cursor
  matching_dispatch_eval [readout]

@[metta_head "gslt:premise:matching-input"]
theorem matching_input_returns (host : Effects.State) (names : List String) (core : Term)
    (ordered : NameOrdered names) (actual expected : Pattern)
    (actualCovered : Covered names actual) (expectedCovered : Covered names expected) :
    PureReturns library.runtime [] host
      (apply "gslt:premise:matching-input" [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names core),
        encoded (InferenceCettaWire.encodePattern actual), encoded (InferenceCettaWire.encodePattern expected)])
      host (Effects.boolean (CanonicalBags.canon actual == CanonicalBags.canon expected)) := by
  have compared : PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:canonical-input" [encoded (encodeList Term.string names),
        encoded (InferenceCettaWire.encodePattern actual), encoded (InferenceCettaWire.encodePattern expected)])
      host (Effects.boolean (CanonicalBags.canon actual == CanonicalBags.canon expected)) := by
    exact RecursiveCollectionExecution.canonical_input_returns host names ordered actual expected
        actualCovered expectedCovered
  matching_dispatch_eval [compared]


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL CanonicalCompare RecursiveCollectionMachine

theorem canonical_operations (names : List String) (ordered : NameOrdered names) (core : Term) :
    MatchingOperations RuleExecutionProgram.interpretedPremiseProgram RecursiveCollectionHandoff.canonicalMatchingExecution RetainedMatchingWire.canonicalCodec
      (interpretedEnvironmentTerm names core)
      (fun query => Covered names query.target) (fun machine => StateCovered names machine.2) (Covered names) where
  start := by
    intro host query covered
    exact RecursiveCollectionExecution.matching_start_returns host names core ordered query covered
  tick := by
    intro host query machine covered
    exact RecursiveCollectionExecution.matching_tick_returns host names core ordered query machine covered
  complete := by
    intro host machine
    exact RecursiveCollectionExecution.matching_complete_returns host names core machine
  answer := by
    intro host machine cursor
    exact RecursiveCollectionExecution.matching_answer_at_returns host names core machine cursor
  input := by
    intro host query actual targetCovered actualCovered
    exact RecursiveCollectionExecution.matching_input_returns host names core ordered actual query.target
      actualCovered targetCovered


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.advance_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.tick_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.run_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.run_from_start_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.finite_native_receipts
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.finite_interpreted_receipts
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.canonical_reachable_covered
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.canonical_pattern_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.canonical_request_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.canonical_start_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.canonical_tick_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.canonical_complete_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.canonical_row_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.canonical_answer_at_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.canonical_input_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.matching_environment_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.matching_start_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.matching_tick_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.matching_complete_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.matching_answer_at_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution.matching_input_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.canonical_operations
