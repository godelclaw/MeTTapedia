import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentReadout
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Scoped

/-!
# The descent machine's environment and commit

The environment value every descent head receives, and `gslt:premise:machine-commit` in the
descent machine's runtime: the step that `gslt:descent:tick` takes after expanding a task.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open StructuralDescent.Scheduled (Goal Result Task Obligation)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open PremiseSchedulerExecution (schedulerStateTerm schedulerExpansionTerm)

/-- `gslt:premise:machine-commit`, in the descent machine's runtime. -/
theorem descent_commit_returns {Task Answer Obligation : Type} (state : State)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (scheduler : Scheduler.State Task Answer Obligation) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:machine-commit" [encoded (schedulerStateTerm task answer obligation scheduler),
        encoded (encodeOption (schedulerExpansionTerm task answer obligation) (scheduler.agenda.head?.map expand))])
      state (encoded (encodeOption (schedulerStateTerm task answer obligation) (some (Scheduler.tick expand scheduler)))) := by
  exact machine_commit_returns state task answer obligation expand scheduler

abbrev environmentValue (environment : Environment) (free : List (String × TypeExpr)) : Atom :=
  encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)

namespace Interpreted

/-- Completion requires both a drained agenda and no unresolved obligations. -/
theorem descent_complete_returns (state : State) (matcher : MatchingExecution)
    (codec : RetainedMatchingWire.MatchingCodec matcher) {environment : Environment} {goal : Goal}
    (search : StructuralDescent.Scheduled.State environment goal matcher) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:premise:machine-complete"
      [encoded (RetainedMatchingWire.Scheduled.stateTerm codec search)]) state
      (Effects.boolean (StructuralDescent.Scheduled.complete environment goal search)) := by
  obtain ⟨agenda, answers, unresolved, work⟩ := search
  cases agenda <;> cases unresolved <;>
    (metta_call descent_checked
     metta_eval unfolding [RetainedMatchingWire.Scheduled.stateTerm, schedulerStateTerm,
       StructuralDescent.Scheduled.complete, Scheduler.complete, encodeList, Effects.boolean])

theorem unresolved_incomplete_returns (state : State) (matcher : MatchingExecution)
    (codec : RetainedMatchingWire.MatchingCodec matcher) {environment : Environment} {goal : Goal}
    (search : StructuralDescent.Scheduled.State environment goal matcher)
    (pending : search.unresolved ≠ []) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:premise:machine-complete"
      [encoded (RetainedMatchingWire.Scheduled.stateTerm codec search)]) state (Effects.boolean false) := by
  simpa only [StructuralDescent.Scheduled.complete, Scheduler.unresolved_not_complete search pending] using
    descent_complete_returns state matcher codec search

theorem agenda_incomplete_returns (state : State) (matcher : MatchingExecution)
    (codec : RetainedMatchingWire.MatchingCodec matcher) {environment : Environment} {goal : Goal}
    (search : StructuralDescent.Scheduled.State environment goal matcher)
    (pending : search.agenda ≠ []) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:premise:machine-complete"
      [encoded (RetainedMatchingWire.Scheduled.stateTerm codec search)]) state (Effects.boolean false) := by
  simpa only [StructuralDescent.Scheduled.complete, Scheduler.pending_not_complete search pending] using
    descent_complete_returns state matcher codec search

end Interpreted

theorem descent_complete_returns (state : State) {environment : Environment} {goal : Goal}
    (search : StructuralDescent.Scheduled.State environment goal) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:premise:machine-complete"
      [descentStateValue search]) state
      (Effects.boolean (StructuralDescent.Scheduled.complete environment goal search)) := by
  simpa only [descentStateValue, RetainedMatchingWire.Scheduled.ordinary_state] using
    Interpreted.descent_complete_returns state MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec search

#print axioms Interpreted.descent_complete_returns
#print axioms Interpreted.unresolved_incomplete_returns
#print axioms Interpreted.agenda_incomplete_returns
#print axioms descent_complete_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
