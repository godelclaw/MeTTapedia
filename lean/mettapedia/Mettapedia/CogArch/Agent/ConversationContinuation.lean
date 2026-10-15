import Mettapedia.CogArch.Agent.GoalCommitment
import Mettapedia.CogArch.Agent.EffectReceiptProjection

/-!
# Conversational requests across turns and interruptions

This managed-host model joins the existing commitment and effect-receipt
interfaces. Input acknowledgement, turn interruption, provider/tool return,
and request fulfillment are separate transitions. A bounded recent-receipt
view is never the authoritative store of unfinished requests.

Implementation comparison: `openai/codex` at
`1da59ad257115cc5734e6781d5ac0b4f08a6e064`,
`codex-rs/core/src/session/turn.rs`, `tasks/regular.rs`, `tasks/mod.rs`, and
`tools/parallel.rs`; Iter `f4064d97849ecaccac7939315a3f1a68de15c3ef`,
`iter.py:235-334`; Omega `ee0618a293ec3662a32b10b09c6cbb073f59d6b2`,
`src/loop.metta:81-125`. These implementations supply call/result boundaries;
the additional request ledger below is a host contract, not a claim that the
unchanged upstream loops already implement it.

The action phase is the sequential quotient for *dependent* decisions.
Independent calls may be executed by a separately qualified batch/parallel
adapter. A completed broker result must be observed before choosing the next
dependent call. Interruption cannot roll back external effects, and resuming
does not replay a withheld or uncertain call.

Host assumptions: request keys identify accepted obligations, rather than
every conversational utterance; keys and action serials are allocated without
reuse; ledger transitions are atomic and durable; broker outcomes and model
observation acknowledgements are faithfully correlated. `accepts` is a
replaceable task-specific outcome checker, not a model's assertion of success.
The theorems do not establish that checker, a natural-language decoder, the
filesystem, an external tool, or a model's free-form answer correct.
-/

namespace Mettapedia.CogArch.Agent.ConversationContinuation

structure RequestKey where
  owner : Nat
  epoch : Nat
  serial : Nat
deriving Repr, DecidableEq

structure Ticket where
  request : RequestKey
  serial : Nat
deriving Repr, DecidableEq

structure Receipt where
  ticket : Ticket
  outcome : EffectReceiptProjection.Receipt
  payload : Nat
deriving Repr, DecidableEq

/-- Reuse the receipt contract: returning alone is not domain success. -/
def Receipt.successful (receipt : Receipt) : Bool :=
  letI : Decidable (EffectReceiptProjection.Completed
      ⟨receipt.ticket.serial, some receipt.outcome⟩) := by
    unfold EffectReceiptProjection.Completed
    infer_instance
  decide (EffectReceiptProjection.Completed ⟨receipt.ticket.serial, some receipt.outcome⟩)

inductive DischargeEvidence where
  | result (receipt : Receipt)
  | operatorCancellation (input : Nat)
deriving Repr, DecidableEq

abbrev Status := GoalCommitment.Status DischargeEvidence

inductive Phase where
  | ready
  | awaitingBroker (ticket : Ticket)
  | awaitingObservation (receipt : Receipt)
deriving Repr, DecidableEq

structure State where
  commitments : RequestKey → Status
  accepted : List RequestKey
  inbox : List RequestKey
  acknowledged : List RequestKey
  phase : Phase
  issued : List Ticket
  journal : List Receipt
  observed : List Ticket
  recent : List Receipt
  interrupted : Bool

def initial : State :=
  ⟨fun _ => .inactive, [], [], [], .ready, [], [], [], [], false⟩

def setCommitment (state : State) (key : RequestKey) (status : Status) : State :=
  { state with commitments := fun other =>
      if other = key then status else state.commitments other }

/-- Redelivery cannot reopen a completed instance or overwrite another one. -/
def accept (state : State) (key : RequestKey) : State :=
  if key ∈ state.accepted then state
  else
    { setCommitment state key .active with
      accepted := state.accepted ++ [key]
      inbox := state.inbox ++ [key] }

/-- Input delivery is acknowledged independently of the work it requested. -/
def acknowledge (state : State) (key : RequestKey) : State :=
  if key ∈ state.inbox then
    { state with
      inbox := state.inbox.filter (fun other => other != key)
      acknowledged := state.acknowledged ++ [key] }
  else state

def interrupt (state : State) : State :=
  { state with interrupted := true }

/-- An explicit resume authorizes decisions, not replay of physical effects. -/
def resume (state : State) : State :=
  { state with interrupted := false }

/-- Read-only context selection cannot write the commitment or receipt store. -/
def compact (state : State) (select : List Receipt → List Receipt) : State :=
  { state with recent := select state.journal }

/-- Reserve a unique dependent call only after input/result observation. -/
def propose (state : State) (ticket : Ticket) : State :=
  if !state.interrupted && state.inbox.isEmpty &&
      decide (state.phase = .ready) &&
      decide (state.commitments ticket.request = .active) &&
      decide (ticket ∉ state.issued) then
    { state with
      phase := .awaitingBroker ticket
      issued := state.issued ++ [ticket] }
  else state

/-- Even withheld, deferred and failed results cross the observation barrier. -/
def brokerResult (state : State) (receipt : Receipt) : State :=
  match state.phase with
  | .awaitingBroker ticket =>
      if receipt.ticket = ticket then
        { state with
          phase := .awaitingObservation receipt
          journal := state.journal ++ [receipt] }
      else state
  | _ => state

def observeResult (state : State) (ticket : Ticket) : State :=
  match state.phase with
  | .awaitingObservation receipt =>
      if ticket = receipt.ticket then
        { state with
          phase := .ready
          observed := state.observed ++ [ticket] }
      else state
  | _ => state

/-- A broker success still needs the task's own completion criterion. -/
def canComplete (accepts : RequestKey → Receipt → Bool)
    (state : State) (key : RequestKey) (receipt : Receipt) : Bool :=
  decide (state.commitments key = .active) &&
  decide (receipt.ticket.request = key) &&
  decide (receipt ∈ state.journal) &&
  decide (receipt.ticket ∈ state.observed) &&
  receipt.successful && accepts key receipt

def complete (accepts : RequestKey → Receipt → Bool)
    (state : State) (key : RequestKey) (receipt : Receipt) : State :=
  if canComplete accepts state key receipt then
    setCommitment state key
      (GoalCommitment.step (state.commitments key)
        (.discharge ⟨.achieved, .result receipt⟩))
  else state

/-- The caller must verify operator authority before invoking cancellation.
Cancellation is retained as an explicit discharge, never labeled achieved. -/
def cancel (state : State) (key : RequestKey) (operatorInput : Nat) : State :=
  setCommitment state key
    (GoalCommitment.step (state.commitments key)
      (.discharge ⟨.justificationEnded, .operatorCancellation operatorInput⟩))

/-- This permits claiming there is *no* pending work. It does not forbid
operator pause, budget cooldown or explicit waiting with work retained. -/
def idleAllowed (state : State) : Bool :=
  state.inbox.isEmpty && decide (state.phase = .ready) &&
  state.accepted.all (fun key => decide (state.commitments key ≠ .active))

structure View where
  focus : RequestKey
  commitment : Status
  phase : Phase
  receipts : List Receipt
deriving Repr, DecidableEq

/-- A selected obligation is read from the durable ledger, independently of
how much historical evidence fits in the prompt. -/
def view (state : State) (focus : RequestKey) : View :=
  ⟨focus, state.commitments focus, state.phase, state.recent⟩

theorem acknowledgement_preserves_work (state : State) (input key : RequestKey) :
    (acknowledge state input).commitments key = state.commitments key := by
  unfold acknowledge
  split <;> rfl

theorem interruption_preserves_work (state : State) (key : RequestKey) :
    (interrupt state).commitments key = state.commitments key := rfl

theorem resume_does_not_replay (state : State) :
    (resume state).issued = state.issued ∧
    (resume state).journal = state.journal ∧
    (resume state).phase = state.phase := ⟨rfl, rfl, rfl⟩

theorem compaction_preserves_work_and_evidence (state : State)
    (select : List Receipt → List Receipt) (key : RequestKey) :
    (compact state select).commitments key = state.commitments key ∧
    (compact state select).journal = state.journal := ⟨rfl, rfl⟩

theorem focused_work_survives_empty_history (state : State) (key : RequestKey) :
    (view (compact state (fun _ => [])) key).commitment =
      state.commitments key ∧
    (view (compact state (fun _ => [])) key).receipts = [] := ⟨rfl, rfl⟩

theorem accept_redelivery_is_stutter (state : State) (key : RequestKey)
    (already : key ∈ state.accepted) : accept state key = state := by
  simp [accept, already]

theorem accept_preserves_other_work (state : State) (key other : RequestKey)
    (different : other ≠ key) :
    (accept state key).commitments other = state.commitments other := by
  unfold accept
  split
  · rfl
  · simp [setCommitment, different]

theorem awaiting_broker_blocks_dependent_call
    (state : State) (pending next : Ticket) :
    propose { state with phase := .awaitingBroker pending } next =
      { state with phase := .awaitingBroker pending } := by
  simp [propose]

theorem unobserved_result_blocks_dependent_call
    (state : State) (receipt : Receipt) (next : Ticket) :
    propose { state with phase := .awaitingObservation receipt } next =
      { state with phase := .awaitingObservation receipt } := by
  simp [propose]

theorem wrong_ticket_cannot_record_result
    (state : State) (pending : Ticket) (receipt : Receipt)
    (different : receipt.ticket ≠ pending) :
    brokerResult { state with phase := .awaitingBroker pending } receipt =
      { state with phase := .awaitingBroker pending } := by
  simp [brokerResult, different]

theorem broker_return_does_not_complete_work
    (state : State) (receipt : Receipt) (key : RequestKey) :
    (brokerResult state receipt).commitments key = state.commitments key := by
  cases phase : state.phase <;> simp [brokerResult, phase]
  split <;> rfl

theorem observed_result_does_not_complete_work
    (state : State) (ticket : Ticket) (key : RequestKey) :
    (observeResult state ticket).commitments key = state.commitments key := by
  cases phase : state.phase <;> simp [observeResult, phase]
  split <;> rfl

theorem completion_requires_matching_observed_success
    (accepts : RequestKey → Receipt → Bool) (state : State)
    (key : RequestKey) (receipt : Receipt)
    (admitted : canComplete accepts state key receipt = true) :
    state.commitments key = .active ∧
    receipt.ticket.request = key ∧ receipt ∈ state.journal ∧
    receipt.ticket ∈ state.observed ∧ receipt.successful = true ∧
    accepts key receipt = true := by
  simpa [canComplete, Bool.and_eq_true, and_assoc] using admitted

theorem missing_observation_cannot_complete
    (accepts : RequestKey → Receipt → Bool) (state : State)
    (key : RequestKey) (receipt : Receipt)
    (unseen : receipt.ticket ∉ state.observed) :
    complete accepts state key receipt = state := by
  simp [complete, canComplete, unseen]

theorem wrong_request_cannot_complete
    (accepts : RequestKey → Receipt → Bool) (state : State)
    (key : RequestKey) (receipt : Receipt)
    (different : receipt.ticket.request ≠ key) :
    complete accepts state key receipt = state := by
  simp [complete, canComplete, different]

theorem unsuccessful_receipt_cannot_complete
    (accepts : RequestKey → Receipt → Bool) (state : State)
    (key : RequestKey) (receipt : Receipt)
    (unsuccessful : receipt.successful = false) :
    complete accepts state key receipt = state := by
  simp [complete, canComplete, unsuccessful]

theorem withheld_is_not_success (ticket : Ticket) (payload : Nat) :
    (Receipt.mk ticket ⟨.withheld, .unknown⟩ payload).successful = false := by
  simp [Receipt.successful, EffectReceiptProjection.Completed]

theorem returned_failure_is_not_success (ticket : Ticket) (payload : Nat) :
    (Receipt.mk ticket ⟨.returned, .failure⟩ payload).successful = false := by
  simp [Receipt.successful, EffectReceiptProjection.Completed]

theorem active_request_blocks_idle (state : State) (key : RequestKey)
    (accepted : key ∈ state.accepted) (active : state.commitments key = .active) :
    idleAllowed state = false := by
  apply Bool.eq_false_iff.mpr
  intro allowed
  simp only [idleAllowed, Bool.and_eq_true] at allowed
  have atKey := (List.all_eq_true.mp allowed.2) key accepted
  simp [active] at atKey

theorem issued_ticket_cannot_be_replayed (state : State) (ticket : Ticket)
    (issued : ticket ∈ state.issued) : propose state ticket = state := by
  simp [propose, issued]

theorem completed_request_is_not_rewritten
    (accepts : RequestKey → Receipt → Bool) (state : State)
    (key : RequestKey) (first : GoalCommitment.DropWitness DischargeEvidence)
    (receipt : Receipt) (done : state.commitments key = .discharged first) :
    complete accepts state key receipt = state := by
  simp [complete, canComplete, done]

theorem complete_preserves_other_work
    (accepts : RequestKey → Receipt → Bool) (state : State)
    (key other : RequestKey) (receipt : Receipt) (different : other ≠ key) :
    (complete accepts state key receipt).commitments other =
      state.commitments other := by
  unfold complete
  split
  · simp [setCommitment, different]
  · rfl

theorem accept_preserves_active_work (state : State) (input key : RequestKey)
    (active : state.commitments key = .active) :
    (accept state input).commitments key = .active := by
  unfold accept
  split
  · exact active
  · simp [setCommitment, active]

theorem proposal_preserves_work (state : State) (ticket : Ticket) (key : RequestKey) :
    (propose state ticket).commitments key = state.commitments key := by
  unfold propose
  split <;> rfl

/-- These are operational events, not fulfillment or cancellation witnesses. -/
inductive ControlEvent where
  | accepted (key : RequestKey)
  | acknowledged (key : RequestKey)
  | interrupted
  | resumed
  | compacted (budget : Nat)
  | proposed (ticket : Ticket)
  | returned (receipt : Receipt)
  | observed (ticket : Ticket)
deriving Repr, DecidableEq

def controlStep (state : State) : ControlEvent → State
  | .accepted key => accept state key
  | .acknowledged key => acknowledge state key
  | .interrupted => interrupt state
  | .resumed => resume state
  | .compacted budget => compact state (fun log => log.drop (log.length - budget))
  | .proposed ticket => propose state ticket
  | .returned receipt => brokerResult state receipt
  | .observed ticket => observeResult state ticket

def controlTrace : State → List ControlEvent → State
  | state, [] => state
  | state, event :: events => controlTrace (controlStep state event) events

theorem control_step_preserves_active_work (state : State)
    (event : ControlEvent) (key : RequestKey)
    (active : state.commitments key = .active) :
    (controlStep state event).commitments key = .active := by
  cases event with
  | accepted input => exact accept_preserves_active_work state input key active
  | acknowledged input => simpa [controlStep, acknowledgement_preserves_work] using active
  | interrupted => exact active
  | resumed => exact active
  | compacted budget => exact active
  | proposed ticket => simpa [controlStep, proposal_preserves_work] using active
  | returned receipt => simpa [controlStep, broker_return_does_not_complete_work] using active
  | observed ticket => simpa [controlStep, observed_result_does_not_complete_work] using active

/-- Arbitrarily many deliveries, interruptions, tool returns and context
changes cannot stand in for a task's discharge witness. -/
theorem control_trace_preserves_active_work (state : State)
    (events : List ControlEvent) (key : RequestKey)
    (active : state.commitments key = .active) :
    (controlTrace state events).commitments key = .active := by
  induction events generalizing state with
  | nil => exact active
  | cons event events ih =>
      exact ih (controlStep state event)
        (control_step_preserves_active_work state event key active)

theorem control_step_preserves_accepted_request (state : State)
    (event : ControlEvent) (key : RequestKey) (present : key ∈ state.accepted) :
    key ∈ (controlStep state event).accepted := by
  cases event with
  | accepted input =>
      change key ∈ (accept state input).accepted
      unfold accept
      split
      · exact present
      · simp [present]
  | acknowledged input =>
      change key ∈ (acknowledge state input).accepted
      unfold acknowledge
      split <;> exact present
  | interrupted => exact present
  | resumed => exact present
  | compacted budget => exact present
  | proposed ticket =>
      change key ∈ (propose state ticket).accepted
      unfold propose
      split <;> exact present
  | returned receipt =>
      change key ∈ (brokerResult state receipt).accepted
      cases phase : state.phase with
      | ready => simpa [brokerResult, phase] using present
      | awaitingBroker pending =>
          by_cases sameTicket : receipt.ticket = pending <;>
            simpa [brokerResult, phase, sameTicket] using present
      | awaitingObservation result => simpa [brokerResult, phase] using present
  | observed ticket =>
      change key ∈ (observeResult state ticket).accepted
      cases phase : state.phase with
      | ready => simpa [observeResult, phase] using present
      | awaitingBroker pending => simpa [observeResult, phase] using present
      | awaitingObservation receipt =>
          by_cases sameTicket : ticket = receipt.ticket <;>
            simpa [observeResult, phase, sameTicket] using present

theorem control_trace_preserves_accepted_request (state : State)
    (events : List ControlEvent) (key : RequestKey)
    (present : key ∈ state.accepted) :
    key ∈ (controlTrace state events).accepted := by
  induction events generalizing state with
  | nil => exact present
  | cons event events ih =>
      exact ih (controlStep state event)
        (control_step_preserves_accepted_request state event key present)

theorem unfinished_request_blocks_idle_after_any_control_trace
    (state : State) (events : List ControlEvent) (key : RequestKey)
    (accepted : key ∈ state.accepted) (active : state.commitments key = .active) :
    idleAllowed (controlTrace state events) = false :=
  active_request_blocks_idle _ key
    (control_trace_preserves_accepted_request state events key accepted)
    (control_trace_preserves_active_work state events key active)

/-! A finite incident replay: delivery and interruption leave the inquiry open. -/

def exampleRequest : RequestKey := ⟨1, 1, 7⟩
def exampleTicket : Ticket := ⟨exampleRequest, 1⟩
def exampleSuccess : Receipt := ⟨exampleTicket, ⟨.returned, .success⟩, 42⟩
def exampleWithheld : Receipt := ⟨exampleTicket, ⟨.withheld, .unknown⟩, 0⟩

def pendingExample : State :=
  acknowledge (accept initial exampleRequest) exampleRequest

def afterWithheld : State :=
  observeResult
    (brokerResult (propose pendingExample exampleTicket) exampleWithheld)
    exampleTicket

theorem delivered_interrupted_compacted_request_still_blocks_idle :
    let state := compact (interrupt pendingExample) (fun _ => [])
    state.commitments exampleRequest = .active ∧
    idleAllowed state = false := by decide

theorem withheld_observed_request_remains_pending :
    (complete (fun _ _ => true) afterWithheld exampleRequest
      exampleWithheld).commitments exampleRequest = .active ∧
    idleAllowed afterWithheld = false := by decide

theorem successful_but_unobserved_result_does_not_discharge :
    let state := brokerResult (propose pendingExample exampleTicket) exampleSuccess
    (complete (fun _ _ => true) state exampleRequest exampleSuccess).commitments
      exampleRequest = .active := by decide

theorem checked_observed_success_discharges :
    let returned := brokerResult (propose pendingExample exampleTicket) exampleSuccess
    let observed := observeResult returned exampleTicket
    (complete (fun _ _ => true) observed exampleRequest exampleSuccess).commitments
      exampleRequest = .discharged ⟨.achieved, .result exampleSuccess⟩ := by decide

theorem domain_success_without_task_acceptance_remains_pending :
    let returned := brokerResult (propose pendingExample exampleTicket) exampleSuccess
    let observed := observeResult returned exampleTicket
    (complete (fun _ _ => false) observed exampleRequest exampleSuccess).commitments
      exampleRequest = .active := by decide

end Mettapedia.CogArch.Agent.ConversationContinuation

#print axioms Mettapedia.CogArch.Agent.ConversationContinuation.completion_requires_matching_observed_success
#print axioms Mettapedia.CogArch.Agent.ConversationContinuation.active_request_blocks_idle
#print axioms Mettapedia.CogArch.Agent.ConversationContinuation.compaction_preserves_work_and_evidence
#print axioms Mettapedia.CogArch.Agent.ConversationContinuation.delivered_interrupted_compacted_request_still_blocks_idle
#print axioms Mettapedia.CogArch.Agent.ConversationContinuation.unfinished_request_blocks_idle_after_any_control_trace
