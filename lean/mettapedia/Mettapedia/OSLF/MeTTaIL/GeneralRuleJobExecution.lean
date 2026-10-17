import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseOrderedAdmission

/-!
# Resumable execution of a typed rule occurrence

The inner machine executes the selected authored declaration, including its
ordered premises and recursive child searches. The outer cursor reads every
completed branch and checks the actual zipper replacement. Complete receipts
retain the selected and authored indices, matching choices and premise history.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution

open Syntax GeneralExecutionAdmission GeneralRuleJobs
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

def Request.goal (request : Request) : GeneralPremise.Execution.Goal :=
  .root request.job.site.focusBound request.job.site.focusType request.job.site.focus request.job.ordinal

abbrev Answer (request : Request) :=
  {receipt : Receipt // receipt.Valid request.plan request.bound request.expected request.source}

def finishRoot (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound
      request.job.site.focusType request.job.site.focus request.job.ordinal trace captured completed history localTarget) :
    Option (Answer request) :=
  if represented : request.job.site.acceptsReplacementRepresentation request.environment.language localTarget then
    if typed : checkOpenPatternWellSorted request.environment.language request.environment.free
        request.bound request.expected (request.job.site.context.fill localTarget) then
      some ⟨⟨request.job, trace, captured, completed, history, localTarget, request.job.site.context.fill localTarget⟩,
        licensed, valid, represented, rfl, checkOpenPatternWellSorted_sound typed⟩
    else none
  else none

theorem finishRoot_complete {request : Request} {receipt : Receipt}
    (valid : receipt.Valid request.plan request.bound request.expected request.source)
    (job : receipt.job = request.job) :
    ∃ answer, finishRoot request (job ▸ valid.1) receipt.matcherTrace receipt.captured receipt.completed
      receipt.premiseHistory receipt.localTarget (job ▸ valid.2.1) = some answer ∧ answer.val = receipt := by
  have checked := checkOpenPatternWellSorted_complete valid.2.2.2.2
  have represented := valid.2.2.1
  have target := valid.2.2.2.1
  cases receipt with
  | mk found trace captured completed history localTarget endpoint =>
    dsimp only at job target
    cases job
    subst endpoint
    have represented' : request.job.site.acceptsReplacementRepresentation request.environment.language localTarget = true :=
      represented
    have checked' : checkOpenPatternWellSorted request.environment.language request.environment.free
        request.bound request.expected (request.job.site.context.fill localTarget) = true := checked
    unfold finishRoot
    rw [dif_pos represented', dif_pos checked']
    exact ⟨_, rfl, rfl⟩

structure Frame (request : Request) where
  licensed : request.job.Valid request.plan request.bound request.expected request.source
  state : GeneralPremise.Execution.State request.environment request.goal
  cursor : Nat := 0

inductive Task (request : Request) where
  | root (frame : Frame request)

inductive Obligation where
  | premise (reason : GeneralPremise.Execution.Obligation)
  deriving Repr, DecidableEq

abbrev State (request : Request) := GeneralPremise.Scheduler.State (Task request) (Answer request) Obligation

def start (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) : State request :=
  { agenda := [.root ⟨licensed, GeneralPremise.Execution.start request.environment request.goal, 0⟩] }

def expand (request : Request) : Task request →
    GeneralPremise.Scheduler.Expansion (Task request) (Answer request) Obligation
  | .root frame =>
    match frame.state.answers[frame.cursor]? with
    | none =>
      if GeneralPremise.Scheduler.settled frame.state then
        { unresolved := frame.state.unresolved.map Obligation.premise }
      else
        { tasks := [.root { frame with
            state := GeneralPremise.Execution.tick request.environment request.goal frame.state }] }
    | some result =>
      let tail := Task.root { frame with cursor := frame.cursor + 1 }
      match result with
      | .root trace captured completed history target valid =>
        { tasks := [tail]
          answers := (finishRoot request frame.licensed trace captured completed history target valid).toList }

/-- The cursor selects the physical answer occurrence before applying the
replacement and typing checks. Equal answer values do not change the cursor. -/
theorem expand_root_answers_at (request : Request) (frame : Frame request)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound
      request.job.site.focusType request.job.site.focus request.job.ordinal trace captured completed history target)
    (selected : frame.state.answers[frame.cursor]? =
      some (.root trace captured completed history target valid)) :
    (expand request (.root frame)).answers =
      (finishRoot request frame.licensed trace captured completed history target valid).toList := by
  simp only [expand, selected]

theorem expand_root_tasks_at (request : Request) (frame : Frame request)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound
      request.job.site.focusType request.job.site.focus request.job.ordinal trace captured completed history target)
    (selected : frame.state.answers[frame.cursor]? =
      some (.root trace captured completed history target valid)) :
    (expand request (.root frame)).tasks = [.root {frame with cursor := frame.cursor + 1}] := by
  simp only [expand, selected]

/-- Receipt membership at a fixed cursor is precisely successful readout of
that occurrence, including the complete receipt rather than only its target. -/
theorem expand_root_receipt_iff (request : Request) (frame : Frame request)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound
      request.job.site.focusType request.job.site.focus request.job.ordinal trace captured completed history target)
    (selected : frame.state.answers[frame.cursor]? =
      some (.root trace captured completed history target valid)) (receipt : Receipt) :
    (∃ answer ∈ (expand request (.root frame)).answers, answer.val = receipt) ↔
      ∃ answer, finishRoot request frame.licensed trace captured completed history target valid = some answer ∧
        answer.val = receipt := by
  rw [expand_root_answers_at request frame trace captured completed history target valid selected]
  simp only [Option.mem_toList]

theorem expand_root_no_receipt_of_unread (request : Request) (frame : Frame request)
    (unread : frame.state.answers[frame.cursor]? = none) :
    (expand request (.root frame)).answers = [] := by
  simp only [expand, unread]
  split <;> rfl

def tick (request : Request) (state : State request) : State request :=
  GeneralPremise.Scheduler.tick (expand request) state

def run (request : Request) (fuel : Nat) (state : State request) : State request :=
  GeneralPremise.Scheduler.run (expand request) fuel state

def settled {request : Request} (state : State request) : Bool := GeneralPremise.Scheduler.settled state

def complete {request : Request} (state : State request) : Bool := GeneralPremise.Scheduler.complete state

inductive Reachable (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) : State request → Prop where
  | start : Reachable request licensed (start request licensed)
  | tick {state : State request} : Reachable request licensed state →
      Reachable request licensed (tick request state)

theorem reachable_run {request : Request}
    {licensed : request.job.Valid request.plan request.bound request.expected request.source}
    {state : State request} (reachable : Reachable request licensed state) (fuel : Nat) :
    Reachable request licensed (run request fuel state) := by
  induction fuel generalizing state with
  | zero => exact reachable
  | succ fuel ih => exact ih (.tick reachable)

def spent (request : Request) (fuel : Nat) (state : State request) : Nat :=
  GeneralPremise.Scheduler.spent (expand request) fuel state

theorem run_add (request : Request) (first second : Nat) (state : State request) :
    run request (first + second) state = run request second (run request first state) :=
  GeneralPremise.Scheduler.run_add _ _ _ _

theorem answers_prefix (request : Request) (fuel : Nat) (state : State request) :
    GeneralPremise.Scheduler.Prefix state.answers (run request fuel state).answers :=
  GeneralPremise.Scheduler.run_answers_prefix _ _ _

theorem obligations_prefix (request : Request) (fuel : Nat) (state : State request) :
    GeneralPremise.Scheduler.Prefix state.unresolved (run request fuel state).unresolved :=
  GeneralPremise.Scheduler.run_obligations_prefix _ _ _

theorem work_add (request : Request) (first second : Nat) (state : State request) :
    spent request (first + second) state = spent request first state +
      spent request second (run request first state) := GeneralPremise.Scheduler.spent_add _ _ _ _

theorem emitted_sound {request : Request} (answer : Answer request) :
    answer.val.Valid request.plan request.bound request.expected request.source := answer.property

theorem complete_iff {request : Request} (state : State request) :
    complete state = true ↔ state.agenda = [] ∧ state.unresolved = [] :=
  GeneralPremise.Scheduler.complete_iff state

theorem pending_not_complete {request : Request} (state : State request) (pending : state.agenda ≠ []) :
    complete state = false := GeneralPremise.Scheduler.pending_not_complete state pending

theorem unresolved_not_complete {request : Request} (state : State request) (pending : state.unresolved ≠ []) :
    complete state = false := GeneralPremise.Scheduler.unresolved_not_complete state pending

/-- The service argument changes query execution while retaining the actual
selected declarations and complete occurrence request. -/
def Request.environmentWith (request : Request) (dynamic : GeneralPremise.DynamicProvider) :
    GeneralPremise.Environment :=
  GeneralPlanEnvironment.environmentWith request.plan dynamic

abbrev AnswerWith (request : Request) (dynamic : GeneralPremise.DynamicProvider) :=
  {receipt : Receipt // receipt.ValidWith dynamic request.plan request.bound request.expected request.source}

/-- Read one physical root occurrence. The shared finish routine rechecks the
actual replacement, scoped reduct and source/target typing. -/
def readoutWith (request : Request) (dynamic : GeneralPremise.DynamicProvider)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (result : GeneralPremise.Execution.Result (request.environmentWith dynamic) request.goal) :
    Option (AnswerWith request dynamic) :=
  match result with
  | .root trace captured completed history _localTarget valid =>
    match emitted : finishWith? dynamic request.plan request.bound request.expected request.job
        trace captured completed history with
    | none => none
    | some receipt =>
      some ⟨receipt, finishWith_root_sound licensed valid emitted⟩

def answersWith (request : Request) (dynamic : GeneralPremise.DynamicProvider)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (state : GeneralPremise.Execution.State (request.environmentWith dynamic) request.goal) :
    List (AnswerWith request dynamic) :=
  state.answers.filterMap (readoutWith request dynamic licensed)

def runWith (request : Request) (dynamic : GeneralPremise.DynamicProvider) (fuel : Nat)
    (state : GeneralPremise.Execution.State (request.environmentWith dynamic) request.goal) :
    GeneralPremise.Execution.State (request.environmentWith dynamic) request.goal :=
  GeneralPremise.Execution.run (request.environmentWith dynamic) request.goal fuel state

def startWith (request : Request) (dynamic : GeneralPremise.DynamicProvider) :
    GeneralPremise.Execution.State (request.environmentWith dynamic) request.goal :=
  GeneralPremise.Execution.start (request.environmentWith dynamic) request.goal

theorem runWith_add (request : Request) (dynamic : GeneralPremise.DynamicProvider)
    (first second : Nat)
    (state : GeneralPremise.Execution.State (request.environmentWith dynamic) request.goal) :
    runWith request dynamic (first + second) state =
      runWith request dynamic second (runWith request dynamic first state) :=
  GeneralPremise.Execution.run_add _ _ _ _ _

theorem answersWith_sound {request : Request} {dynamic : GeneralPremise.DynamicProvider}
    {licensed : request.job.Valid request.plan request.bound request.expected request.source}
    {state : GeneralPremise.Execution.State (request.environmentWith dynamic) request.goal}
    {receipt : Receipt}
    (emitted : receipt ∈ (answersWith request dynamic licensed state).map Subtype.val) :
    receipt.ValidWith dynamic request.plan request.bound request.expected request.source := by
  obtain ⟨answer, _, same⟩ := List.mem_map.mp emitted
  subst receipt
  exact answer.property

theorem readoutWith_complete {request : Request} {dynamic : GeneralPremise.DynamicProvider}
    {receipt : Receipt}
    (valid : receipt.ValidWith dynamic request.plan request.bound request.expected request.source)
    (job : receipt.job = request.job)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) :
    ∃ answer, readoutWith request dynamic licensed
      (.root receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory
        receipt.localTarget (job ▸ valid.2.1)) = some answer ∧ answer.val = receipt := by
  have emitted := finishWith_complete valid
  rw [job] at emitted
  simp only [readoutWith]
  split
  · rename_i missing
    rw [emitted] at missing
    cases missing
  · rename_i actual selected
    have same : actual = receipt := Option.some.inj (selected.symm.trans emitted)
    subst actual
    exact ⟨_, rfl, rfl⟩

/-- Every independently justified receipt for this occurrence appears at a
finite budget. The declaration-order condition governs recursive child search;
no total-availability assumption is imposed on unrelated native requests. -/
theorem runWith_receipt_complete {request : Request} {dynamic : GeneralPremise.DynamicProvider}
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (checked : GeneralPremise.checkStepStratification (request.environmentWith dynamic).language = true)
    {receipt : Receipt}
    (valid : receipt.ValidWith dynamic request.plan request.bound request.expected request.source)
    (job : receipt.job = request.job) :
    ∃ fuel, receipt ∈ (answersWith request dynamic licensed
      (runWith request dynamic fuel (startWith request dynamic))).map Subtype.val := by
  let wanted : GeneralPremise.Execution.Result (request.environmentWith dynamic) request.goal :=
    .root receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget
      (job ▸ valid.2.1)
  have ordered : wanted.ordered = true := (job ▸ valid.2.1).ordered checked
  have member := GeneralPremise.Execution.finish_contains (request.environmentWith dynamic)
    request.goal wanted ordered
  obtain ⟨answer, projected, same⟩ := readoutWith_complete valid job licensed
  exact ⟨(GeneralPremise.Execution.treeStart (request.environmentWith dynamic) request.goal).cost,
    List.mem_map.mpr ⟨answer, List.mem_filterMap.mpr ⟨wanted, member, projected⟩, same⟩⟩

/-- A complete empty response and an unavailable request remain distinct in
this execution; pending work or unresolved requests cannot certify exhaustion. -/
theorem runWith_complete_iff (request : Request) (dynamic : GeneralPremise.DynamicProvider)
    (fuel : Nat) :
    GeneralPremise.Execution.complete (request.environmentWith dynamic) request.goal
      (runWith request dynamic fuel (startWith request dynamic)) = true ↔
      (runWith request dynamic fuel (startWith request dynamic)).agenda = [] ∧
      (runWith request dynamic fuel (startWith request dynamic)).unresolved = [] :=
  GeneralPremise.Scheduler.complete_iff _

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution
