import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecution
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCertified

/-!
# Resumable execution of an authored equation job

The machine advances the actual scoped matcher and ordered premise scheduler.
Both cursors survive a pause. A successful answer carries its independent
local-completion proof and the complete matching/premise origins; failures of
typing or target checks are rejected branches. Unresolved premise work is
retained and prevents an exhaustive result.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution

open Syntax GeneralExecutionAdmission GeneralEquationJobs
open Mettapedia.GSLT.LanguageDef.WellSorted


structure Request where
  plan : Plan
  bound : List TypeExpr
  expected : TypeExpr
  source : Pattern
  job : Job
  deriving Repr

def Request.environment (request : Request) : GeneralPremise.Environment :=
  GeneralPlanEnvironment.environment request.plan

def Request.matcher (request : Request) : GeneralScopedMatchMachine.Request :=
  ⟨request.job.equation.rule, request.job.equation.binding.spec, request.job.site.focusBound.length,
    .left, [], 0, [], request.job.equation.rule.left, request.job.site.focus.eraseBinderMetadata⟩

abbrev Request.premises (request : Request) (captured : ScopedRuleMatching.Assignment) : GeneralPremise.Execution.Goal :=
  .premises (request.job.context request.plan) request.job.equation.rule.premises captured

abbrev Answer (request : Request) :=
  {receipt : Receipt // Completion request.plan request.bound request.expected request.source receipt}

structure MatchFrame (request : Request) where
  licensed : LicensedJob request.plan request.bound request.expected request.source request.job
  sourceTyped : OpenPatternWellSorted request.environment.language request.plan.snapshot.free
    request.bound request.expected request.source
  state : GeneralScopedMatchMachine.State
  reachable : GeneralScopedMatchMachine.Reachable request.matcher state
  cursor : Nat := 0

structure PremiseFrame (request : Request) where
  licensed : LicensedJob request.plan request.bound request.expected request.source request.job
  sourceTyped : OpenPatternWellSorted request.environment.language request.plan.snapshot.free
    request.bound request.expected request.source
  trace : List GeneralScopedMatchMachine.BagChoice
  captured : ScopedRuleMatching.Assignment
  matching : GeneralScopedMatchMachine.TracedMatches request.job.equation.rule request.job.equation.binding.spec
    request.job.site.focusBound.length .left [] 0 [] request.job.equation.rule.left
    request.job.site.focus.eraseBinderMetadata trace captured
  capturedTyped : GeneralPremise.TypedAssignment request.environment
    (request.job.context request.plan) captured
  state : GeneralPremise.Execution.State request.environment (request.premises captured)
  cursor : Nat := 0

inductive Task (request : Request) where
  | matching (frame : MatchFrame request)
  | premises (frame : PremiseFrame request)

inductive Obligation where
  | sourceRejected
  | premise (reason : GeneralPremise.Execution.Obligation)
  deriving Repr, DecidableEq

abbrev State (request : Request) := GeneralPremise.Scheduler.State (Task request) (Answer request) Obligation

def start (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job) :
    State request :=
  if checked : checkOpenPatternWellSorted request.environment.language request.plan.snapshot.free
      request.bound request.expected request.source then
    { agenda := [.matching ⟨licensed, checkOpenPatternWellSorted_sound checked,
      GeneralScopedMatchMachine.start request.matcher, .start, 0⟩] }
  else { unresolved := [.sourceRejected] }

def expandMatching (request : Request) (frame : MatchFrame request) :
    GeneralPremise.Scheduler.Expansion (Task request) (Answer request) Obligation :=
  match found : frame.state.answers[frame.cursor]? with
  | none =>
      if GeneralScopedMatchMachine.complete frame.state then {}
      else { tasks := [.matching { frame with
        state := GeneralScopedMatchMachine.tick request.matcher frame.state
        reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable }] }
  | some answer =>
      let tail := Task.matching {frame with cursor := frame.cursor + 1}
      if checked : GeneralPremise.checkTypedAssignment request.environment
          (request.job.context request.plan) answer.assignment then
        have matching := GeneralScopedMatchMachine.answers_sound frame.reachable (List.mem_of_getElem? found)
        { tasks := [
            .premises ⟨frame.licensed, frame.sourceTyped, answer.trace, answer.assignment, matching,
              GeneralPremise.checkTypedAssignment_sound checked,
              GeneralPremise.Execution.start request.environment (request.premises answer.assignment), 0⟩,
            tail] }
      else { tasks := [tail] }

def expandPremises (request : Request) (frame : PremiseFrame request) :
    GeneralPremise.Scheduler.Expansion (Task request) (Answer request) Obligation :=
  match frame.state.answers[frame.cursor]? with
  | none =>
      if GeneralPremise.Scheduler.settled frame.state then
        { unresolved := frame.state.unresolved.map Obligation.premise }
      else { tasks := [.premises {frame with
        state := GeneralPremise.Execution.tick request.environment (request.premises frame.captured) frame.state}] }
  | some result =>
      let tail := Task.premises {frame with cursor := frame.cursor + 1}
      match result with
      | .premises completed history valid =>
          match finished : finish request.plan request.bound request.expected request.job
              frame.trace frame.captured completed history with
          | none => { tasks := [tail] }
          | some receipt =>
              { tasks := [tail]
                answers := [⟨receipt, finish_sound frame.licensed frame.sourceTyped frame.matching valid finished⟩] }

def expand (request : Request) : Task request → GeneralPremise.Scheduler.Expansion (Task request) (Answer request) Obligation
  | .matching frame => expandMatching request frame
  | .premises frame => expandPremises request frame

def tick (request : Request) (state : State request) : State request := GeneralPremise.Scheduler.tick (expand request) state

def run (request : Request) (fuel : Nat) (state : State request) : State request :=
  GeneralPremise.Scheduler.run (expand request) fuel state

inductive Reachable (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job) :
    State request → Prop where
  | start : Reachable request licensed (start request licensed)
  | tick {state : State request} : Reachable request licensed state →
      Reachable request licensed (tick request state)

theorem reachable_tick {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (reached : Reachable request licensed state) :
    Reachable request licensed (tick request state) := .tick reached

theorem reachable_run {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (fuel : Nat) (reached : Reachable request licensed state) :
    Reachable request licensed (run request fuel state) := by
  induction fuel generalizing state with
  | zero => exact reached
  | succ fuel ih => exact ih (.tick reached)

theorem reachable_from_start {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (reached : Reachable request licensed state) :
    ∃ fuel, state = run request fuel (start request licensed) := by
  induction reached with
  | start => exact ⟨0, rfl⟩
  | tick reached ih =>
      obtain ⟨fuel, same⟩ := ih
      exact ⟨fuel + 1, same ▸ (GeneralPremise.Scheduler.run_add (expand request) fuel 1
        (start request licensed)).symm⟩

def settled {request : Request} (state : State request) : Bool := GeneralPremise.Scheduler.settled state

def complete {request : Request} (state : State request) : Bool := GeneralPremise.Scheduler.complete state

def spent (request : Request) (fuel : Nat) (state : State request) : Nat :=
  GeneralPremise.Scheduler.spent (expand request) fuel state

theorem run_add (request : Request) (first second : Nat) (state : State request) :
    run request (first + second) state = run request second (run request first state) :=
  GeneralPremise.Scheduler.run_add _ _ _ _

theorem work_add (request : Request) (first second : Nat) (state : State request) :
    spent request (first + second) state = spent request first state +
      spent request second (run request first state) := GeneralPremise.Scheduler.spent_add _ _ _ _

theorem answers_prefix (request : Request) (fuel : Nat) (state : State request) :
    GeneralPremise.Scheduler.Prefix state.answers (run request fuel state).answers := GeneralPremise.Scheduler.run_answers_prefix _ _ _

theorem obligations_prefix (request : Request) (fuel : Nat) (state : State request) :
    GeneralPremise.Scheduler.Prefix state.unresolved (run request fuel state).unresolved := GeneralPremise.Scheduler.run_obligations_prefix _ _ _

theorem emitted_sound {request : Request} {state : State request} (answer : Answer request)
    (_member : answer ∈ state.answers) :
    Completion request.plan request.bound request.expected request.source answer.val := answer.property

theorem complete_iff {request : Request} (state : State request) :
    complete state = true ↔ state.agenda = [] ∧ state.unresolved = [] := GeneralPremise.Scheduler.complete_iff state

theorem pending_not_complete {request : Request} (state : State request) (pending : state.agenda ≠ []) :
    complete state = false := GeneralPremise.Scheduler.pending_not_complete state pending

theorem unresolved_not_complete {request : Request} (state : State request) (unresolved : state.unresolved ≠ []) :
    complete state = false := GeneralPremise.Scheduler.unresolved_not_complete state unresolved

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
