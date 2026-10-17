import Mettapedia.Machines.Cursor.ProofChecking

/-!
# Checked proof execution as a retained service

The existing proof-checking machine runs inside `Machine.handle`. A request
supplies its actual checked cursor and source schedule. Pausing retains both
the caller and the complete checker state; returning transmits the original
source-indexed report, including a refusal's checked prefix and pending suffix.

The report consumer below is an independent client: each request occurrence
produces a separate delivery, even when its schedule and result equal another
request's. Its reached-state invariant derives report validity from actual
checker execution. It does not authenticate an arbitrary caller-supplied report.
No HE/PeTTa evaluator correspondence, native handle security, physical ownership
or latency bound is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ProofCheckingService

open Mettapedia.Logic Mettapedia.Logic.DerivationGraph
open Mettapedia.Logic.DerivationGraph.BorrowedCursor
open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {J Origin : Type} {rules : List J → J → Prop}

/-- A request occurrence retains its actual source-indexed starting evidence.
The ticket identifies an occurrence; it is not an execution capability. -/
structure Request (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) where
  ticket : Nat
  initial : CheckedCursor interface store
  schedule : List NodeId

def load {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin}
    (request : Request interface store) : ProofChecking.Work interface store :=
  ProofChecking.start request.initial request.schedule

/-- The worker is the original checker, with its observations embedded into
the caller's event type and its genuine report returned as a service reply. -/
def service (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    {Event : Type}
    (emit : ProductiveCoreAdapters.Occurrence (ProofChecking.Work interface store) → Event) :
    Machine (ProofChecking.Work interface store) Event
      (Reply (ProofChecking.Report interface store) Empty) Empty :=
  (ProofChecking.machine interface store).relabel emit Reply.returned Empty.elim

theorem service_run (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    {Event : Type}
    (emit : ProductiveCoreAdapters.Occurrence (ProofChecking.Work interface store) → Event)
    (fuel : Nat) (work : ProofChecking.Work interface store) :
    (service interface store emit).run fuel work =
      (((ProofChecking.machine interface store).run fuel work).1.map emit,
        ((ProofChecking.machine interface store).run fuel work).2.relabel Reply.returned Empty.elim) :=
  (ProofChecking.machine interface store).run_relabel emit Reply.returned Empty.elim fuel work

/-- Finishing the service is exactly finishing the original checker with the
same report. Event relabeling preserves the entire occurrence list. -/
theorem service_finished_iff (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) {Event : Type}
    (emit : ProductiveCoreAdapters.Occurrence (ProofChecking.Work interface store) → Event)
    (fuel : Nat) (work : ProofChecking.Work interface store) (events : List Event)
    (report : ProofChecking.Report interface store) :
    (service interface store emit).run fuel work = (events, .finished (.returned report)) ↔
      ∃ original, (ProofChecking.machine interface store).run fuel work =
        (original, .finished report) ∧ original.map emit = events := by
  rw [service_run]
  cases actual : (ProofChecking.machine interface store).run fuel work with
  | mk original outcome =>
      cases outcome <;> simp [Outcome.relabel, and_comm]

/-- A returned report describes the actual request, not just some derivable
root in the same theory. In particular its counter and suffix are meaningful. -/
theorem service_report_meaning (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) {Event : Type}
    (emit : ProductiveCoreAdapters.Occurrence (ProofChecking.Work interface store) → Event)
    (request : Request interface store) (fuel : Nat) (events : List Event)
    (report : ProofChecking.Report interface store)
    (completed : (service interface store emit).run fuel (load request) =
      (events, .finished (.returned report))) :
    ProofChecking.Meaning request.initial request.schedule report.work := by
  obtain ⟨original, ran, _⟩ :=
    (service_finished_iff interface store emit fuel (load request) events report).mp completed
  apply ProofChecking.check_only_report_meaning interface store request.initial request.schedule fuel report
  simpa only [OutcomeRunner.run_eq, load, ran] using congrArg Prod.snd ran

section Handling

variable {Caller Event Verdict : Type}
variable (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
variable (caller : Machine Caller Event Verdict (Request interface store))
variable (callback : Callback Caller Event (Request interface store) (ProofChecking.Report interface store) Empty)
variable (emit : ProductiveCoreAdapters.Occurrence (ProofChecking.Work interface store) → Event)

def machine : Machine
    (HandledState Caller (ProofChecking.Work interface store) (Request interface store))
    Event Verdict Empty :=
  caller.handle callback (service interface store emit) load

/-- A genuine checker pause preserves its current source cursor and pending
work, together with the exact saved caller and originating request. -/
theorem paused_checker_retains_caller (fuel : Nat) (request : Request interface store)
    (saved : Caller) (work residual : ProofChecking.Work interface store)
    (events : List (ProductiveCoreAdapters.Occurrence (ProofChecking.Work interface store)))
    (paused : (ProofChecking.machine interface store).run fuel work = (events, .exhausted residual)) :
    (machine interface store caller callback emit).run fuel (.handling request saved work) =
      (events.map emit, .exhausted (.handling request saved residual)) := by
  apply caller.handle_run_of_no_reply callback (service interface store emit) load
    fuel request saved work (events.map emit) (.exhausted residual)
  · simp only [service_run, paused, Outcome.relabel]
  · intro reply impossible
    cases impossible

/-- Returning crosses the existing reply boundary exactly once and resumes
the saved caller with the original report. Unused checker fuel stays unused. -/
theorem returned_report_resumes_caller (fuel : Nat) (request : Request interface store)
    (saved : Caller) (work : ProofChecking.Work interface store) (events : List Event)
    (report : ProofChecking.Report interface store)
    (completed : (service interface store emit).run fuel work =
      (events, .finished (.returned report))) :
    ∃ used ≤ fuel,
      (machine interface store caller callback emit).run used (.handling request saved work) =
        (events ++ [callback.replyEvent (.returned report)],
          .exhausted (.running (callback.resume saved (.returned report)))) :=
  caller.handle_run_of_reply callback (service interface store emit) load
    fuel request saved work events (.returned report) completed

theorem run_add (first extra : Nat)
    (state : HandledState Caller (ProofChecking.Work interface store) (Request interface store)) :
    (machine interface store caller callback emit).run (first + extra) state =
      (machine interface store caller callback emit).continueRun extra
        ((machine interface store caller callback emit).run first state) :=
  Machine.run_add _ _ _ _

theorem history_prefix (first extra : Nat)
    (state : HandledState Caller (ProofChecking.Work interface store) (Request interface store)) :
    ((machine interface store caller callback emit).run first state).1 <+:
      ((machine interface store caller callback emit).run (first + extra) state).1 := by
  rw [run_add]
  exact (machine interface store caller callback emit).continueRun_events_prefix _ _

theorem check_only_run_add (first extra : Nat)
    (state : HandledState Caller (ProofChecking.Work interface store) (Request interface store)) :
    OutcomeRunner.run (machine interface store caller callback emit) (first + extra) state =
      OutcomeRunner.resume (machine interface store caller callback emit) extra
        (OutcomeRunner.run (machine interface store caller callback emit) first state) :=
  OutcomeRunner.run_add _ _ _ _

end Handling

/-- Every service transition either advances the original checked work or
returns its original report. Neither cancellation nor an invented reply is
introduced by this adapter. -/
theorem service_step_cases (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) {Event : Type}
    (emit : ProductiveCoreAdapters.Occurrence (ProofChecking.Work interface store) → Event)
    (request : Request interface store) (work : ProofChecking.Work interface store)
    (transition : Transition (ProofChecking.Work interface store) Event
      (Reply (ProofChecking.Report interface store) Empty) Empty)
    (meaning : ProofChecking.Meaning request.initial request.schedule work)
    (stepped : (service interface store emit).step work = some transition) :
    (∃ next, transition = .publish [emit (work, next)] next ∧
      ProofChecking.Meaning request.initial request.schedule next) ∨
    (∃ report, transition = .finish (.returned report) ∧
      ProofChecking.Meaning request.initial request.schedule report.work) := by
  cases observed : ProofChecking.answer work with
  | some report =>
      have same : transition = .finish (.returned report) := by
        simpa [service, Machine.relabel, Transition.relabel, ProofChecking.machine,
          ProductiveCoreAdapters.answerMachine, ProofChecking.answerCore, observed] using stepped.symm
      subst transition
      refine Or.inr ⟨report, rfl, ?_⟩
      rw [(ProofChecking.answer_spec work report observed).1]
      exact meaning
  | none =>
      cases moved : ProofChecking.tick work with
      | none =>
          simp [service, Machine.relabel, ProofChecking.machine,
            ProductiveCoreAdapters.answerMachine, ProofChecking.answerCore, observed, moved] at stepped
      | some next =>
          have same : transition = .publish [emit (work, next)] next := by
            simpa [service, Machine.relabel, Transition.relabel, ProofChecking.machine,
              ProductiveCoreAdapters.answerMachine, ProofChecking.answerCore, observed, moved] using stepped.symm
          subst transition
          exact Or.inl ⟨next, rfl,
            ProofChecking.tick_meaning request.initial request.schedule work next meaning moved⟩

/-! ## An independent report consumer -/

structure Delivery (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin) where
  request : Request interface store
  report : ProofChecking.Report interface store

def Delivery.Valid {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin}
    (delivery : Delivery interface store) : Prop :=
  ProofChecking.Meaning delivery.request.initial delivery.request.schedule delivery.report.work

inductive Consumer (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin) where
  | ready (pending : List (Request interface store)) (delivered : List (Delivery interface store))
  | waiting (request : Request interface store) (pending : List (Request interface store))
      (delivered : List (Delivery interface store))
  | invalidReply

inductive Event (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin) where
  | called (ticket : Nat)
  | checked (occurrence : ProductiveCoreAdapters.Occurrence (ProofChecking.Work interface store))
  | returned (accepted : Bool)
  | protocolError

/-- The client requests each supplied work item and consumes each report.
It does not perform inference or inspect a claimed verdict before requesting. -/
def consumer (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin) :
    Machine (Consumer interface store) (Event interface store)
      (List (Delivery interface store)) (Request interface store) where
  step
    | .ready [] delivered => some (.finish delivered)
    | .ready (request :: later) delivered =>
        some (.call request (.waiting request later delivered))
    | .waiting _ _ _ => none
    | .invalidReply => some (.fail [.protocolError])

def callback (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin) :
    Callback (Consumer interface store) (Event interface store) (Request interface store)
      (ProofChecking.Report interface store) Empty where
  callEvent request := .called request.ticket
  replyEvent
    | .returned report => .returned report.accepted
    | .faulted impossible => impossible.elim
    | .cancelled => .protocolError
  resume
    | .waiting request later delivered, .returned report =>
        .ready later (delivered ++ [⟨request, report⟩])
    | _, _ => .invalidReply

abbrev State (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin) :=
  HandledState (Consumer interface store) (ProofChecking.Work interface store) (Request interface store)

def consumerMachine (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin) :
    Machine (State interface store) (Event interface store) (List (Delivery interface store)) Empty :=
  machine interface store (consumer interface store) (callback interface store) Event.checked

def begin {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin}
    (requests : List (Request interface store)) : State interface store :=
  .running (.ready requests [])

/-- In a running client every delivered report belongs to its own request.
During a service call the exact request is saved in the waiting client and
the active work satisfies the original checker's reached-prefix invariant. -/
def ValidState {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin} :
    State interface store → Prop
  | .running (.ready _ delivered) => ∀ delivery ∈ delivered, delivery.Valid
  | .running _ => False
  | .handling request saved work =>
      ∃ later delivered, saved = .waiting request later delivered ∧
        (∀ delivery ∈ delivered, delivery.Valid) ∧
        ProofChecking.Meaning request.initial request.schedule work

theorem begin_valid {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin}
    (requests : List (Request interface store)) : ValidState (begin requests) := by
  simp [begin, ValidState]

def ValidTransition {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin} :
    Transition (State interface store) (Event interface store) (List (Delivery interface store)) Empty → Prop
  | .silent next | .publish _ next => ValidState next
  | .finish delivered => ∀ delivery ∈ delivered, delivery.Valid
  | .fail _ => False
  | .call impossible _ => impossible.elim

/-- The actual composed transition preserves request-scoped evidence. -/
theorem transition_valid (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    (state : State interface store)
    (transition : Transition (State interface store) (Event interface store) (List (Delivery interface store)) Empty)
    (valid : ValidState state)
    (stepped : (consumerMachine interface store).step state = some transition) :
    ValidTransition transition := by
  cases state with
  | running client =>
      cases client with
      | ready pending delivered =>
          cases pending with
          | nil =>
              have same : transition = .finish delivered := by
                simpa [consumerMachine, machine, Machine.handle, consumer] using stepped.symm
              subst transition
              exact valid
          | cons request later =>
              have same : transition = .publish [.called request.ticket]
                  (.handling request (.waiting request later delivered) (load request)) := by
                simpa [consumerMachine, machine, Machine.handle, consumer, callback] using stepped.symm
              subst transition
              exact ⟨later, delivered, rfl, valid,
                ProofChecking.start_meaning request.initial request.schedule⟩
      | waiting request later delivered =>
          simp [consumerMachine, machine, Machine.handle, consumer] at stepped
      | invalidReply => exact valid.elim
  | handling request saved work =>
      obtain ⟨later, delivered, rfl, prior, meaning⟩ := valid
      cases advanced : (service interface store Event.checked).step work with
      | none => simp [consumerMachine, machine, Machine.handle, advanced] at stepped
      | some event =>
          rcases service_step_cases interface store Event.checked request work event meaning advanced with
            ⟨next, rfl, retained⟩ | ⟨report, rfl, checked⟩
          · have same : transition = .publish [.checked (work, next)]
                (.handling request (.waiting request later delivered) next) := by
              simpa [consumerMachine, machine, Machine.handle, advanced] using stepped.symm
            subst transition
            exact ⟨later, delivered, rfl, prior, retained⟩
          · have same : transition = .publish [.returned report.accepted]
                (.running (.ready later (delivered ++ [⟨request, report⟩]))) := by
              simpa [consumerMachine, machine, Machine.handle, advanced, callback] using stepped.symm
            subst transition
            intro delivery member
            rcases List.mem_append.mp member with old | newest
            · exact prior delivery old
            · have equal := List.mem_singleton.mp newest
              subst delivery
              exact checked

def ValidOutcome {interface : RuleWitness.{0, 0} rules} {store : Store J interface.W Origin} :
    Outcome (State interface store) (List (Delivery interface store)) Empty → Prop
  | .exhausted state | .stuck state => ValidState state
  | .finished delivered => ∀ delivery ∈ delivered, delivery.Valid
  | .faulted => False
  | .suspended impossible _ => impossible.elim

/-- Validity is constructed from actual execution at every budget, including
pauses in the checker. It is not a precondition on the returned report. -/
theorem run_valid (interface : RuleWitness.{0, 0} rules) (store : Store J interface.W Origin)
    (fuel : Nat) (state : State interface store) (valid : ValidState state) :
    ValidOutcome ((consumerMachine interface store).run fuel state).2 := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      cases moved : (consumerMachine interface store).step state with
      | none => simpa only [Machine.run, moved, ValidOutcome] using valid
      | some transition =>
          have preserved := transition_valid interface store state transition valid moved
          cases transition with
          | silent next =>
              simpa only [Machine.run, moved] using ih next preserved
          | publish events next =>
              simpa only [Machine.run, moved] using ih next preserved
          | finish delivered => simpa only [Machine.run, moved, ValidOutcome, ValidTransition] using preserved
          | fail events => exact preserved.elim
          | call impossible saved => exact impossible.elim

theorem finished_deliveries_valid (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) (requests : List (Request interface store))
    (fuel : Nat) (events : List (Event interface store)) (delivered : List (Delivery interface store))
    (completed : (consumerMachine interface store).run fuel (begin requests) =
      (events, .finished delivered)) : ∀ delivery ∈ delivered, delivery.Valid := by
  have valid := run_valid interface store fuel (begin requests) (begin_valid requests)
  simpa only [completed, ValidOutcome] using valid

/-- An accepted delivered report certifies the entire supplied source schedule. -/
theorem accepted_delivery_exact {interface : RuleWitness.{0, 0} rules}
    {store : Store J interface.W Origin} (delivery : Delivery interface store)
    (valid : delivery.Valid) (accepted : delivery.report.accepted = true) :
    delivery.report.work.pending = [] ∧
      delivery.report.work.accepted = delivery.request.schedule.length ∧
      BorrowedCursor.run interface store delivery.request.initial.state delivery.request.schedule =
        some delivery.report.work.cursor.state :=
  ProofChecking.completed_run interface store delivery.request.initial delivery.request.schedule
    delivery.report.work valid (by simpa only [accepted] using delivery.report.valid)

/-- Refusal retains the exact checked prefix, failed head, and following rows
inside the delivered report, independently of the event journal. -/
theorem refused_delivery_retains {interface : RuleWitness.{0, 0} rules}
    {store : Store J interface.W Origin} (delivery : Delivery interface store)
    (valid : delivery.Valid) (refused : delivery.report.accepted = false) :
    ∃ consumed source later,
      delivery.request.schedule = consumed ++ source :: later ∧
      delivery.report.work.pending = source :: later ∧
      BorrowedCursor.run interface store delivery.request.initial.state consumed =
        some delivery.report.work.cursor.state ∧
      delivery.report.work.accepted = consumed.length ∧
      BorrowedCursor.step interface store delivery.report.work.cursor.state source = none := by
  obtain ⟨consumed, partition, executed, count, _, failed⟩ := valid
  have status := ProofChecking.refused_report_status delivery.report refused
  obtain ⟨source, later, pending, rejected⟩ := failed status
  exact ⟨consumed, source, later, by simpa only [pending] using partition,
    pending, executed, count, rejected⟩

theorem check_only_deliveries_valid (interface : RuleWitness.{0, 0} rules)
    (store : Store J interface.W Origin) (requests : List (Request interface store))
    (fuel : Nat) (delivered : List (Delivery interface store))
    (completed : OutcomeRunner.run (consumerMachine interface store) fuel (begin requests) =
      .finished delivered) : ∀ delivery ∈ delivered, delivery.Valid := by
  have same := (OutcomeRunner.run_eq (consumerMachine interface store) fuel (begin requests)).symm.trans completed
  exact finished_deliveries_valid interface store requests fuel _ delivered (Prod.ext rfl same)

namespace Controls

private inductive Rule where
  | seed
  | pair

private def controlRules (premises : List Nat) (conclusion : Nat) : Prop :=
  (premises = [] ∧ conclusion = 7) ∨ (premises = [7, 7] ∧ conclusion = 8)

private def interface : RuleWitness controlRules where
  W := Rule
  isInstance
    | .seed, premises, conclusion => decide (premises = [] ∧ conclusion = 7)
    | .pair, premises, conclusion => decide (premises = [7, 7] ∧ conclusion = 8)
  sound witness _ _ accepted := by
    cases witness with
    | seed => exact Or.inl (of_decide_eq_true accepted)
    | pair => exact Or.inr (of_decide_eq_true accepted)
  complete _ _ valid := by
    rcases valid with seed | pair
    · exact ⟨.seed, decide_eq_true seed⟩
    · exact ⟨.pair, decide_eq_true pair⟩

private def store : Store Nat interface.W String where
  revision := 41
  read source :=
    if source = 0 then some ⟨7, .seed, [], "seed"⟩ else
    if source = 1 then some ⟨8, .pair, [0, 0], "paired"⟩ else
    if source = 2 then some ⟨9, .seed, [], "invalid-unused-row"⟩ else
    if source = 3 then some ⟨7, .seed, [], "second-seed"⟩ else none

private def initial : CheckedCursor interface store := CheckedCursor.begin interface store

private def request (ticket : Nat) (schedule : List NodeId) : Request interface store :=
  ⟨ticket, initial, schedule⟩

private def readDelivered (delivery : Delivery interface store) :
    Nat × Bool × List NodeId × Nat × Option Nat :=
  (delivery.request.ticket, delivery.report.accepted, delivery.report.work.pending,
    delivery.report.work.accepted,
    (delivery.report.work.cursor.root 1).map CheckedJudgment.judgment)

private def readFinished :
    Outcome (State interface store) (List (Delivery interface store)) Empty →
      Option (List (Nat × Bool × List NodeId × Nat × Option Nat))
  | .finished delivered => some (delivered.map readDelivered)
  | _ => none

private def readPaused :
    Outcome (State interface store) (List (Delivery interface store)) Empty →
      Option (Nat × List NodeId × Nat × Nat × List Nat × Option Nat)
  | .exhausted (.handling active (.waiting saved later _) work) =>
      some (active.ticket, work.pending, work.accepted, saved.ticket,
        later.map Request.ticket, (work.cursor.root 0).map CheckedJudgment.judgment)
  | _ => none

theorem pause_retains_real_checker_and_caller :
    readPaused (OutcomeRunner.run (consumerMachine interface store) 2
      (begin [request 11 [0, 1], request 12 [0, 1]])) =
      some (11, [1], 1, 11, [12], some 7) := by
  rfl

theorem two_requests_deliver_two_reports :
    readFinished (OutcomeRunner.run (consumerMachine interface store) 11
      (begin [request 11 [0, 1], request 12 [0, 1]])) =
      some [(11, true, [], 2, some 8), (12, true, [], 2, some 8)] := by
  rfl

/-- Equal tickets and equal payloads still denote two supplied occurrences. -/
theorem identical_requests_remain_two_deliveries :
    readFinished (OutcomeRunner.run (consumerMachine interface store) 11
      (begin [request 11 [0, 1], request 11 [0, 1]])) =
      some [(11, true, [], 2, some 8), (11, true, [], 2, some 8)] := by
  rfl

private def boundaryEvent : Event interface store → Option (Nat × Option Bool)
  | .called ticket => some (ticket, none)
  | .returned accepted => some (0, some accepted)
  | _ => none

theorem repeated_reply_boundaries_are_not_deduplicated :
    (((consumerMachine interface store).run 11
      (begin [request 11 [0, 1], request 12 [0, 1]])).1.filterMap boundaryEvent) =
      [(11, none), (0, some true), (12, none), (0, some true)] := by
  rfl

theorem completed_refusal_retains_unused_bad_row_and_suffix :
    readFinished (OutcomeRunner.run (consumerMachine interface store) 6
      (begin [request 11 [0, 1, 2, 3]])) =
      some [(11, false, [2, 3], 2, some 8)] := by
  rfl

theorem refusal_does_not_drop_the_following_request :
    readFinished (OutcomeRunner.run (consumerMachine interface store) 11
      (begin [request 11 [0, 1, 2, 3], request 12 [0, 1]])) =
      some [(11, false, [2, 3], 2, some 8), (12, true, [], 2, some 8)] := by
  rfl

theorem absent_source_is_refused_and_retained :
    readFinished (OutcomeRunner.run (consumerMachine interface store) 5
      (begin [request 11 [0, 99, 1]])) =
      some [(11, false, [99, 1], 1, none)] := by
  rfl

theorem duplicate_schedule_address_is_not_a_second_valid_row :
    readFinished (OutcomeRunner.run (consumerMachine interface store) 5
      (begin [request 11 [0, 0]])) =
      some [(11, false, [0], 1, none)] := by
  rfl

private def deduplicatedStore : Store Nat interface.W String :=
  { store with read := fun source =>
    if source = 1 then some ⟨8, .pair, [0], "paired"⟩ else store.read source }

private def invalidRequest : Request interface deduplicatedStore :=
  ⟨11, CheckedCursor.begin interface deduplicatedStore, [0, 1]⟩

private def refusalView :
    Outcome (State interface deduplicatedStore) (List (Delivery interface deduplicatedStore)) Empty →
      Option (List (Bool × List NodeId × Nat))
  | .finished delivered => some (delivered.map fun item =>
      (item.report.accepted, item.report.work.pending, item.report.work.accepted))
  | _ => none

theorem deleting_a_repeated_premise_changes_acceptance :
    refusalView (OutcomeRunner.run (consumerMachine interface deduplicatedStore) 5
      (begin [invalidRequest])) = some [(false, [1], 1)] := by
  rfl

private def cacheView :
    Outcome (State interface store) (List (Delivery interface store)) Empty → Option (List (List Nat))
  | .finished delivered => some (delivered.map fun item => item.report.work.cursor.state.cache.toList)
  | _ => none

theorem equal_judgments_at_distinct_sources_survive_return :
    cacheView (OutcomeRunner.run (consumerMachine interface store) 6
      (begin [request 11 [0, 3]])) = some [[7, 7]] := by
  rfl

theorem splitting_inside_service_preserves_complete_history :
    (consumerMachine interface store).continueRun 9
      ((consumerMachine interface store).run 2
        (begin [request 11 [0, 1], request 12 [0, 1]])) =
      (consumerMachine interface store).run 11
        (begin [request 11 [0, 1], request 12 [0, 1]]) := by
  exact ((consumerMachine interface store).run_add 2 9 _).symm

theorem check_only_split_keeps_both_deliveries :
    OutcomeRunner.resume (consumerMachine interface store) 9
      (OutcomeRunner.run (consumerMachine interface store) 2
        (begin [request 11 [0, 1], request 12 [0, 1]])) =
      OutcomeRunner.run (consumerMachine interface store) 11
        (begin [request 11 [0, 1], request 12 [0, 1]]) := by
  exact (OutcomeRunner.run_add (consumerMachine interface store) 2 9 _).symm

theorem completed_calls_never_restart_on_resume :
    OutcomeRunner.resume (consumerMachine interface store) 100
      (OutcomeRunner.run (consumerMachine interface store) 11
        (begin [request 11 [0, 1], request 12 [0, 1]])) =
      OutcomeRunner.run (consumerMachine interface store) 11
        (begin [request 11 [0, 1], request 12 [0, 1]]) := by
  rfl

theorem returned_report_does_not_finish_the_caller :
    readFinished (OutcomeRunner.run (consumerMachine interface store) 5
      (begin [request 11 [0, 1]])) = none := by
  rfl

theorem cancelled_reply_does_not_create_a_delivery :
    (callback interface store).resume (.ready [] []) .cancelled = .invalidReply := by
  rfl

private def producedReport : Option (ProofChecking.Report interface store) :=
  match OutcomeRunner.run (ProofChecking.machine interface store) 4 (load (request 11 [0, 1])) with
  | .finished report => some report
  | _ => none

/-- Even a genuine checked report cannot answer a request this caller never made. -/
theorem unsolicited_checked_report_does_not_create_a_delivery :
    producedReport.map (fun report =>
      (callback interface store).resume (.ready [] []) (.returned report)) = some .invalidReply := by
  rfl

end Controls

end Mettapedia.Machines.Cursor.ProofCheckingService
