import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.BridgeCoverage
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseSchedulerExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMachineExecution.Core

/-!
# Scoped library operations, proved with the bridge kit

Operations of `gslt_scoped_execution.metta` that the descent machine calls, proved directly in the
scoped library's own runtime.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL GeneralPremise ScopedRuleMatching RuleBinding
open Effects (State)
open Eval
open BridgeKit WireKit
open PremiseSchedulerExecution (schedulerStateTerm schedulerExpansionTerm)

/-- `gslt:automata:append` is list append, for any element encoding. -/
@[metta_head "gslt:automata:append"]
theorem automata_append_returns {α : Type} (element : α → Term) (state : State) :
    ∀ left right : List α,
      PureReturns scopedLibrary.runtime [] state
        (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)]) state
        (encoded (encodeList element (left ++ right)))
  | [], right => by
    metta_call scoped_checked
    metta_eval unfolding [encodeList]
  | first :: rest, right => by
    metta_call scoped_checked
    metta_eval [automata_append_returns element state rest right] with scoped_checked unfolding [encodeList]

/-- `gslt:premise:machine-commit` is the scheduler's tick. -/
@[metta_head "gslt:premise:machine-commit"]
theorem machine_commit_returns {Task Answer Obligation : Type} (state : State)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (scheduler : Scheduler.State Task Answer Obligation) :
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:premise:machine-commit" [encoded (schedulerStateTerm task answer obligation scheduler),
        encoded (encodeOption (schedulerExpansionTerm task answer obligation) (scheduler.agenda.head?.map expand))])
      state (encoded (encodeOption (schedulerStateTerm task answer obligation) (some (Scheduler.tick expand scheduler)))) := by
  obtain ⟨agenda, answers, unresolved, work⟩ := scheduler
  metta_call scoped_checked
  cases agenda with
  | nil =>
    metta_eval unfolding [schedulerStateTerm, schedulerExpansionTerm, encodeList, encodeOption, Scheduler.tick]
  | cons first rest =>
    metta_eval [automata_append_returns task state (expand first).tasks rest,
        automata_append_returns answer state answers (expand first).answers,
        automata_append_returns obligation state unresolved (expand first).unresolved] with scoped_checked
      unfolding [schedulerStateTerm, schedulerExpansionTerm, encodeList, encodeOption, Scheduler.tick]

abbrev assignmentValue (assignment : Assignment) : Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment)

abbrev contextualValue (value : ContextualValue) : Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  encoded (InferenceCettaWire.AuthoredRule.contextualValueTerm value)

/-- `gslt:premise:context-next` is `Context.next`. -/
@[metta_head "gslt:premise:context-next"]
theorem context_next_returns (state : State) (context : Context) :
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:premise:context-next" [encoded (PremiseOperationsExecution.GeneralExecution.contextTerm context)]) state
      (encoded (PremiseOperationsExecution.GeneralExecution.contextTerm context.next)) := by
  metta_call scoped_checked
  metta_eval unfolding [PremiseOperationsExecution.GeneralExecution.contextTerm, Context.next]

/-- `gslt:premise:scope-remove` is `removeParameter`. -/
@[metta_head "gslt:premise:scope-remove"]
theorem scope_remove_returns (state : State) (parameter : String) :
    ∀ assignment : Assignment,
      PureReturns scopedLibrary.runtime [] state
        (apply "gslt:premise:scope-remove" [encoded (.string parameter), assignmentValue assignment]) state
        (assignmentValue (removeParameter parameter assignment))
  | [] => by
    metta_call scoped_checked
    metta_eval unfolding [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      MatchAutomataBindingExecution.payloadBindingsTerm, encodeList, removeParameter]
  | (key, value) :: rest => by
    metta_call scoped_checked
    by_cases same : key = parameter
    · metta_eval [scope_remove_returns state parameter rest] with scoped_checked
        unfolding [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
          MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm,
          encodeList, removeParameter, same]
    · metta_eval [scope_remove_returns state parameter rest] with scoped_checked
        unfolding [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
          MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm,
          encodeList, removeParameter, same, assignmentValue]

/-- `gslt:premise:scope-bind` is `bindParameter`. -/
@[metta_head "gslt:premise:scope-bind"]
theorem scope_bind_returns (state : State) (parameter : String) (value : ContextualValue) (assignment : Assignment) :
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:premise:scope-bind" [encoded (.string parameter), contextualValue value, assignmentValue assignment])
      state (assignmentValue (bindParameter parameter value assignment)) := by
  metta_call scoped_checked
  metta_eval [scope_remove_returns state parameter assignment] with scoped_checked
    unfolding [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm,
      encodeList, bindParameter, assignmentValue, contextualValue]

/-- `gslt:automata:binding` on an assignment is `lookup`. -/
@[metta_head "gslt:automata:binding"]
theorem automata_binding_returns (state : State) (name : String) :
    ∀ assignment : Assignment,
      PureReturns scopedLibrary.runtime [] state
        (apply "gslt:automata:binding" [encoded (.string name), assignmentValue assignment]) state
        (encoded (encodeOption InferenceCettaWire.AuthoredRule.contextualValueTerm (lookup assignment name)))
  | [] => by
    metta_call scoped_checked
    metta_eval unfolding [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      MatchAutomataBindingExecution.payloadBindingsTerm, encodeList, encodeOption, lookup]
  | (key, value) :: rest => by
    metta_call scoped_checked
    by_cases same : name = key
    · metta_eval [automata_binding_returns state name rest] with scoped_checked
        unfolding [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
          MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm,
          encodeList, encodeOption, lookup, same, assignmentValue]
    · have differ : (key == name) = false := by simpa [beq_eq_false_iff_ne] using Ne.symm same
      metta_eval [automata_binding_returns state name rest] with scoped_checked
        unfolding [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
          MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm,
          encodeList, encodeOption, lookup, same, differ, assignmentValue]

/-- `gslt:premise:scope-restore` is `restoreParameter`. -/
@[metta_head "gslt:premise:scope-restore"]
theorem scope_restore_returns (state : State) (parameter : String) (initial final : Assignment) :
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:premise:scope-restore" [encoded (.string parameter), assignmentValue initial, assignmentValue final])
      state (assignmentValue (restoreParameter parameter initial final)) := by
  metta_call scoped_checked
  cases found : lookup initial parameter with
  | none =>
    metta_eval [automata_binding_returns state parameter initial, scope_remove_returns state parameter final]
      with scoped_checked unfolding [encodeOption, restoreParameter, found]
  | some value =>
    metta_eval [automata_binding_returns state parameter initial, scope_bind_returns state parameter value final]
      with scoped_checked unfolding [encodeOption, restoreParameter, found, bindParameter]

/-- `gslt:automata:length` is `List.length`, for any element encoding. -/
@[metta_head "gslt:automata:length"]
theorem automata_length_returns {α : Type} (element : α → Term) (state : State) :
    ∀ items : List α,
      PureReturns scopedLibrary.runtime [] state (apply "gslt:automata:length" [encoded (encodeList element items)])
        state (number items.length)
  | [] => by
    metta_call scoped_checked
    metta_eval unfolding [encodeList]
  | first :: rest => by
    rw [show (first :: rest).length = 1 + rest.length by simp only [List.length_cons]; omega]
    metta_call scoped_checked
    metta_eval [automata_length_returns element state rest] with scoped_checked unfolding [encodeList]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
