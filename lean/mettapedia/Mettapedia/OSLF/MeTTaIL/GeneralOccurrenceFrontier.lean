import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceNativeReceipts

/-!
# General typed equation-aware occurrence frontier

Discovery executes actual rule and equation jobs first. Certification also
scans the source-derived finite universe, retaining checked equation edges
and visiting their inverse adjacency. Every pause keeps matcher, premise,
provider and child cursors. An equation path is administrative evidence;
only a completed rule job emits a primitive occurrence receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission GeneralOccurrenceSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted

structure Request where
  plan : Plan
  bound : List TypeExpr
  expected : TypeExpr
  source : Pattern
  deriving Repr

def Request.root (request : Request) : Pattern := request.source.eraseBinderMetadata

def Request.providerTerms (request : Request) : List Pattern :=
  request.plan.snapshot.provider.rows.flatMap fun row => row.values

def Request.universe (request : Request) : List Pattern :=
  Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse.sourceUniverse
    request.plan.snapshot.language request.plan.snapshot.free request.bound request.expected
    request.root request.providerTerms

abbrev Answer (request : Request) :=
  GeneralOccurrenceNativeReceipts.ReceiptFamily request.plan request.bound request.expected request.root

structure Representative (request : Request) where
  pattern : Pattern
  conversions : List Conversion
  justified : ConversionPath request.plan request.bound request.expected request.root pattern conversions

structure Edge (request : Request) where
  source : Pattern
  receipt : GeneralEquationJobs.Receipt
  valid : GeneralEquationJobs.Completion request.plan request.bound request.expected source receipt

def Edge.forward (request : Request) (edge : Edge request) (representative : Representative request)
    (same : representative.pattern = edge.source) : Representative request where
  pattern := edge.receipt.target
  conversions := representative.conversions ++ [.forward edge.receipt]
  justified := by
    apply ConversionPath.append request.plan request.bound request.expected representative.justified
    rw [same]
    exact .cons edge.valid rfl (.nil _)

def Edge.reverse (request : Request) (edge : Edge request) (representative : Representative request)
    (same : representative.pattern = edge.receipt.target) : Representative request where
  pattern := edge.source
  conversions := representative.conversions ++ [.reverse edge.receipt]
  justified := by
    apply ConversionPath.append request.plan request.bound request.expected representative.justified
    rw [same]
    exact .back edge.valid rfl (.nil _)

def equationRequest (request : Request) (source : Pattern) (job : GeneralEquationJobs.Job) :
    GeneralEquationJobExecution.Request :=
  ⟨request.plan, request.bound, request.expected, source, job⟩

def ruleRequest (request : Request) (representative : Representative request) (job : GeneralRuleJobs.Job) :
    GeneralRuleJobExecution.Request :=
  ⟨request.plan, request.bound, request.expected, representative.pattern, job⟩

structure EquationFrame (request : Request) where
  source : Pattern
  job : GeneralEquationJobs.Job
  licensed : GeneralEquationJobs.LicensedJob request.plan request.bound request.expected source job
  state : GeneralEquationJobExecution.State (equationRequest request source job)
  reachable : GeneralEquationJobExecution.Reachable (equationRequest request source job) licensed state
  cursor : Nat := 0

structure RuleFrame (request : Request) where
  representative : Representative request
  job : GeneralRuleJobs.Job
  licensed : job.Valid request.plan request.bound request.expected representative.pattern
  state : GeneralRuleJobExecution.State (ruleRequest request representative job)
  reachable : GeneralRuleJobExecution.Reachable (ruleRequest request representative job) licensed state
  cursor : Nat := 0

structure EquationArchive (request : Request) where
  frame : EquationFrame request
  settled : GeneralEquationJobExecution.settled frame.state = true
  readAll : frame.state.answers[frame.cursor]? = none

structure RuleArchive (request : Request) where
  frame : RuleFrame request
  settled : GeneralRuleJobExecution.settled frame.state = true
  readAll : frame.state.answers[frame.cursor]? = none

inductive Task (request : Request) where
  | visit (representative : Representative request)
  | incoming (representative : Representative request) (edges : List (Edge request))
  | universe
  | scanUniverse (remaining : List Pattern)
  | equation (frame : EquationFrame request)
  | rule (frame : RuleFrame request)

inductive Obligation where
  | admission (reason : GeneralExecutionAdmission.Obligation)
  | sourceRejected
  | equation (reason : GeneralEquationJobExecution.Obligation)
  | rule (reason : GeneralRuleJobExecution.Obligation)
  deriving Repr, DecidableEq

structure State (request : Request) where
  agenda : List (Task request) := []
  visited : List (Representative request) := []
  edges : List (Edge request) := []
  checkedEquations : List (EquationArchive request) := []
  checkedRules : List (RuleArchive request) := []
  answers : List (Answer request) := []
  unresolved : List Obligation := []
  universeScanned : Bool := false
  work : Nat := 0

structure Expansion (request : Request) where
  tasks : List (Task request) := []
  visits : List (Representative request) := []
  edges : List (Edge request) := []
  checkedEquations : List (EquationArchive request) := []
  checkedRules : List (RuleArchive request) := []
  answers : List (Answer request) := []
  unresolved : List Obligation := []
  universeScanned : Bool := false

def equationTasks (request : Request) (source : Pattern) : List (Task request) :=
  (GeneralEquationJobs.jobs request.plan request.bound request.expected source).attach.map fun item =>
    let licensed := (GeneralEquationJobs.jobs_iff _ _ _ _ _).mp item.property
    .equation ⟨source, item.val, licensed,
      GeneralEquationJobExecution.start (equationRequest request source item.val) licensed, .start, 0⟩

def ruleTasks (request : Request) (representative : Representative request) : List (Task request) :=
  (GeneralRuleJobs.jobs request.plan request.bound request.expected representative.pattern).attach.map fun item =>
    let licensed := (GeneralRuleJobs.jobs_spec _ _ _ _ _).mp item.property
    .rule ⟨representative, item.val, licensed,
      GeneralRuleJobExecution.start (ruleRequest request representative item.val) licensed, .start, 0⟩

def visitedAt (request : Request) (state : State request) (pattern : Pattern) :
    Option {representative : Representative request // representative.pattern = pattern} :=
  (state.visited.attach.find? fun representative => representative.val.pattern == pattern).bind fun found =>
    if same : found.val.pattern = pattern then some ⟨found.val, same⟩ else none

def edgeDiscoveries (request : Request) (state : State request) (edge : Edge request) : List (Task request) :=
  (match visitedAt request state edge.source with
    | none => []
    | some found => [.visit (edge.forward request found.val found.property)]) ++
  (match visitedAt request state edge.receipt.target with
    | none => []
    | some found => [.visit (edge.reverse request found.val found.property)])

def expandEquation (request : Request) (state : State request) (frame : EquationFrame request) : Expansion request :=
  match found : frame.state.answers[frame.cursor]? with
  | none =>
    if closed : GeneralEquationJobExecution.settled frame.state then
      { unresolved := frame.state.unresolved.map Obligation.equation
        checkedEquations := [⟨frame, closed, found⟩] }
    else
      { tasks := [.equation { frame with
          state := GeneralEquationJobExecution.tick (equationRequest request frame.source frame.job) frame.state
          reachable := .tick frame.reachable }] }
  | some answer =>
    let edge : Edge request := ⟨frame.source, answer.val, answer.property⟩
    { tasks := edgeDiscoveries request state edge ++ [.equation { frame with cursor := frame.cursor + 1 }]
      edges := [edge] }

def expandRule (request : Request) (frame : RuleFrame request) : Expansion request :=
  match found : frame.state.answers[frame.cursor]? with
  | none =>
    if closed : GeneralRuleJobExecution.settled frame.state then
      { unresolved := frame.state.unresolved.map Obligation.rule
        checkedRules := [⟨frame, closed, found⟩] }
    else
      { tasks := [.rule { frame with
          state := GeneralRuleJobExecution.tick (ruleRequest request frame.representative frame.job) frame.state
          reachable := .tick frame.reachable }] }
  | some answer =>
    { tasks := [.rule { frame with cursor := frame.cursor + 1 }]
      answers := [⟨⟨frame.representative.pattern, frame.representative.conversions, answer.val⟩,
        frame.representative.justified, answer.property⟩] }

def expand (request : Request) (state : State request) : Task request → Expansion request
  | .visit representative =>
    if (state.visited.map Representative.pattern).contains representative.pattern then {}
    else
      { tasks := ruleTasks request representative ++ equationTasks request representative.pattern ++
          [.incoming representative state.edges]
        visits := [representative] }
  | .incoming representative edges =>
    match edges with
    | [] => {}
    | edge :: remaining =>
      if same : representative.pattern = edge.receipt.target then
        { tasks := [.visit (edge.reverse request representative same), .incoming representative remaining] }
      else if same : representative.pattern = edge.source then
        { tasks := [.visit (edge.forward request representative same), .incoming representative remaining] }
      else { tasks := [.incoming representative remaining] }
  | .universe => { tasks := [.scanUniverse request.universe] }
  | .scanUniverse remaining =>
    match remaining with
    | [] => { universeScanned := true }
    | source :: remaining => { tasks := equationTasks request source ++ [.scanUniverse remaining] }
  | .equation frame => expandEquation request state frame
  | .rule frame => expandRule request frame

def tick (request : Request) (state : State request) : State request :=
  match state.agenda with
  | [] => state
  | task :: remaining =>
    let next := expand request state task
    { agenda := next.tasks ++ remaining
      visited := state.visited ++ next.visits
      edges := state.edges ++ next.edges
      checkedEquations := state.checkedEquations ++ next.checkedEquations
      checkedRules := state.checkedRules ++ next.checkedRules
      answers := state.answers ++ next.answers
      unresolved := state.unresolved ++ next.unresolved
      universeScanned := state.universeScanned || next.universeScanned
      work := state.work + 1 }

def start (request : Request) : State request :=
  let obligations := request.plan.obligations.map Obligation.admission
  if checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root then
    { agenda := [.visit ⟨request.root, [], .nil _⟩, .universe]
      unresolved := obligations }
  else { unresolved := obligations ++ [.sourceRejected] }

def run (request : Request) : Nat → State request → State request
  | 0, state => state
  | fuel + 1, state => run request fuel (tick request state)

inductive Reachable (request : Request) : State request → Prop where
  | start : Reachable request (start request)
  | tick {state : State request} : Reachable request state → Reachable request (tick request state)

theorem reachable_run {request : Request} {state : State request}
    (reached : Reachable request state) (fuel : Nat) : Reachable request (run request fuel state) := by
  induction fuel generalizing state with
  | zero => exact reached
  | succ fuel ih => exact ih (.tick reached)

def settled (request : Request) (state : State request) : Bool := state.agenda.isEmpty

def complete (request : Request) (state : State request) : Bool :=
  state.agenda.isEmpty && state.unresolved.isEmpty && state.universeScanned

def spent (request : Request) (fuel : Nat) (state : State request) : Nat :=
  (run request fuel state).work - state.work

theorem run_add (request : Request) (first second : Nat) (state : State request) :
    run request (first + second) state = run request second (run request first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih => simpa only [Nat.succ_add, run] using ih (tick request state)

theorem tick_answers_prefix (request : Request) (state : State request) :
    GeneralPremise.Scheduler.Prefix state.answers (tick request state).answers := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using GeneralPremise.Scheduler.Prefix.refl state.answers
  | cons task remaining => exact ⟨(expand request state task).answers, by simp only [tick, agenda]⟩

theorem answers_prefix (request : Request) (fuel : Nat) (state : State request) :
    GeneralPremise.Scheduler.Prefix state.answers (run request fuel state).answers := by
  induction fuel generalizing state with
  | zero => exact .refl _
  | succ fuel ih => exact (tick_answers_prefix request state).trans (ih (tick request state))

theorem tick_work_bounds (request : Request) (state : State request) :
    state.work ≤ (tick request state).work ∧ (tick request state).work ≤ state.work + 1 := by
  cases agenda : state.agenda <;> simp [tick, agenda]

theorem run_work_bounds (request : Request) (fuel : Nat) (state : State request) :
    state.work ≤ (run request fuel state).work ∧ (run request fuel state).work ≤ state.work + fuel := by
  induction fuel generalizing state with
  | zero => simp [run]
  | succ fuel ih =>
    have front := tick_work_bounds request state
    have back := ih (tick request state)
    constructor
    · exact front.1.trans back.1
    · change (run request fuel (tick request state)).work ≤ state.work + (fuel + 1)
      omega

theorem work_add (request : Request) (first second : Nat) (state : State request) :
    spent request (first + second) state = spent request first state +
      spent request second (run request first state) := by
  unfold spent
  rw [run_add]
  have front := (run_work_bounds request first state).1
  have back := (run_work_bounds request second (run request first state)).1
  omega

theorem complete_iff (request : Request) (state : State request) :
    complete request state = true ↔
      state.agenda = [] ∧ state.unresolved = [] ∧ state.universeScanned = true := by
  simp only [complete, Bool.and_eq_true, List.isEmpty_iff, and_assoc]

theorem pending_not_complete (request : Request) (state : State request) (pending : state.agenda ≠ []) :
    complete request state = false := by
  cases result : complete request state with
  | false => rfl
  | true => exact False.elim (pending ((complete_iff request state).mp result).1)

theorem unresolved_not_complete (request : Request) (state : State request) (unresolved : state.unresolved ≠ []) :
    complete request state = false := by
  cases result : complete request state with
  | false => rfl
  | true => exact False.elim (unresolved ((complete_iff request state).mp result).2.1)

theorem emitted_step (request : Request) (answer : Answer request) :
    (gslt request.plan request.bound request.expected).Step request.root answer.val.target :=
  Receipt.semantic_step request.plan request.bound request.expected answer.property

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
