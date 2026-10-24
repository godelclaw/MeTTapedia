import Std

/-!
# Recover a local completion write without another provider request

The provider and local storage have different failure boundaries. Once an
answer is received, the owned continuation retains it while recording retries.
An ambiguous local commit is inspected through a fresh connection: a matching
owned receipt authorizes publication, an active pending row permits another
local write, and an unavailable read permits neither publication nor another
provider request.

The model assumes SQLite's transaction/read observations are faithful and that
the continuation remains alive during local retries. A crash before any durable
write cannot preserve an answer held only in memory; recovery reports unknown
and does not automatically replay that provider call. It does not establish
exactly-once external execution or make failed storage readable.
-/

namespace PettaClaw.LlmCompletionRecovery

structure Identity where
  call : String
  epoch : String
  deriving DecidableEq, Repr

structure Answer where
  identity : Identity
  value : String
  deriving DecidableEq, Repr

inductive Phase where
  | ready | submitted | received | readback | retryLocal | committed
  | published | conflict | unknown
  deriving DecidableEq, Repr

inductive WriteResult where
  | committed | rolledBack | unknownLanded | unknownRolledBack
  deriving DecidableEq, Repr

inductive RequestState where
  | pending | completed | other
  deriving DecidableEq, Repr

inductive CallState where
  | active | completed | other
  deriving DecidableEq, Repr

inductive ReceiptObservation where
  | committed | pending | conflict
  deriving DecidableEq, Repr

/-- The predicates in the native fresh-read SQLite query. -/
def receiptObservation (request : RequestState) (call : CallState)
    (sameOwner sameAnswer : Bool) : ReceiptObservation :=
  if !sameOwner then .conflict
  else if request == .completed && call == .completed && sameAnswer then .committed
  else if request == .pending && call == .active then .pending
  else .conflict

theorem receipt_requires_matching_owner (request : RequestState) (call : CallState)
    (sameAnswer : Bool) :
    receiptObservation request call false sameAnswer = .conflict := by
  simp [receiptObservation]

theorem mismatching_answer_cannot_authorize_publication
    (request : RequestState) (call : CallState) (sameOwner : Bool) :
    receiptObservation request call sameOwner false ≠ .committed := by
  cases request <;> cases call <;> cases sameOwner <;> decide

inductive Event where
  | submit
  | receive (answer : Answer)
  | write (result : WriteResult)
  | inspect (available : Bool)
  | publish
  | crash
  deriving DecidableEq, Repr

structure State where
  identity : Identity
  phase : Phase := .ready
  retained : Option Answer := none
  durable : Option Answer := none
  providerRequests : Nat := 0
  publications : Nat := 0
  usageReceipts : Nat := 0
  leaseActive : Bool := false
  deriving DecidableEq, Repr

def owned (state : State) (answer : Answer) : Bool :=
  answer.identity == state.identity

def writing (phase : Phase) : Bool :=
  phase == .received || phase == .retryLocal

def inspecting (phase : Phase) : Bool :=
  phase == .readback || phase == .retryLocal

def inspectReceipt (state : State) : ReceiptObservation :=
  match state.durable with
  | some receipt => receiptObservation .completed .completed
      (owned state receipt) (state.retained == some receipt)
  | none => receiptObservation .pending (if state.leaseActive then .active else .other) true false

/-- The abstract SQLite transaction commits usage, receipt and lease together. -/
def commit (state : State) (phase : Phase) : State :=
  { state with phase, durable := state.retained, usageReceipts := 1,
               leaseActive := false }

def step (state : State) : Event → State
  | .submit =>
      if state.phase == .ready then
        { state with phase := .submitted, providerRequests := state.providerRequests + 1,
                     leaseActive := true }
      else state
  | .receive answer =>
      if state.phase == .submitted && owned state answer then
        { state with phase := .received, retained := some answer }
      else state
  | .write result =>
      if writing state.phase && state.retained.isSome then
        match result with
        | .committed => commit state .committed
        | .unknownLanded => commit state .readback
        | .rolledBack => { state with phase := .retryLocal }
        | .unknownRolledBack => { state with phase := .readback }
      else state
  | .inspect available =>
      if inspecting state.phase && available then
        match inspectReceipt state with
        | .committed => { state with phase := .committed }
        | .pending => { state with phase := .retryLocal }
        | .conflict => { state with phase := .conflict }
      else state
  | .publish =>
      if state.phase == .committed then
        match state.durable with
        | some receipt =>
            if owned state receipt && state.retained == some receipt then
              { state with phase := .published, publications := state.publications + 1 }
            else { state with phase := .conflict }
        | none => { state with phase := .conflict }
      else state
  | .crash =>
      { state with phase := .unknown, retained := none, leaseActive := false }

def run : State → List Event → State
  | state, [] => state
  | state, event :: rest => run (step state event) rest

def afterReceive (answer : Answer) : State :=
  { identity := answer.identity, phase := .received, retained := some answer,
    providerRequests := 1, leaseActive := true }

/-- No local bookkeeping event launches HTTP, including a failed write/read. -/
theorem only_submit_can_increase_provider_requests (state : State) (event : Event)
    (localEvent : event ≠ .submit) :
    (step state event).providerRequests = state.providerRequests := by
  cases event with
  | submit => contradiction
  | receive answer => simp [step]; split <;> rfl
  | write result =>
      simp only [step]
      split
      · cases result <;> rfl
      · rfl
  | inspect available =>
      simp only [step]
      split
      · cases inspectReceipt state <;> rfl
      · rfl
  | publish =>
      simp only [step]
      split
      · split
        · split <;> rfl
        · rfl
      · rfl
  | crash => rfl

theorem received_answer_cannot_be_submitted_again (answer : Answer) :
    step (afterReceive answer) .submit = afterReceive answer := by
  simp [step, afterReceive]

theorem step_never_rearms_a_used_call (state : State) (event : Event)
    (used : state.phase ≠ .ready) : (step state event).phase ≠ .ready := by
  cases event with
  | submit => simp [step, used]
  | receive answer =>
      simp only [step]
      split
      · simp
      · exact used
  | write result =>
      simp only [step]
      split
      · cases result <;> simp [commit]
      · exact used
  | inspect available =>
      simp only [step]
      split
      · cases inspectReceipt state <;> simp
      · exact used
  | publish =>
      simp only [step]
      split
      · split
        · split <;> simp
        · simp
      · exact used
  | crash => simp [step]

theorem used_call_keeps_request_count (state : State) (event : Event)
    (used : state.phase ≠ .ready) :
    (step state event).providerRequests = state.providerRequests := by
  by_cases submitted : event = .submit
  · subst event
    simp [step, used]
  · exact only_submit_can_increase_provider_requests state event submitted

/-- This includes arbitrary failed reads/writes, duplicate submits and crashes. -/
theorem retries_cannot_make_another_provider_request
    (state : State) (events : List Event) (used : state.phase ≠ .ready) :
    (run state events).providerRequests = state.providerRequests := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      rw [run, ih (step state event) (step_never_rearms_a_used_call state event used)]
      exact used_call_keeps_request_count state event used

/-- Arbitrarily many failed/ambiguous local writes preserve the held answer. -/
theorem writes_retain_the_answer (state : State) (result : WriteResult) :
    (step state (.write result)).retained = state.retained := by
  simp only [step]
  split
  · cases result <;> rfl
  · rfl

theorem unavailable_read_grants_no_authority (state : State) :
    step state (.inspect false) = state := by simp [step]

theorem unknown_landed_is_not_yet_publication (answer : Answer) :
    (step (afterReceive answer) (.write .unknownLanded)).publications = 0 ∧
    (step (afterReceive answer) (.write .unknownLanded)).phase = .readback := by
  simp [step, writing, afterReceive, commit]

/-- An actual landed commit is recovered and published without another POST. -/
theorem readback_recovers_landed_commit (answer : Answer) :
    let final := run (afterReceive answer)
      [.write .unknownLanded, .inspect true, .publish]
    final.phase = .published ∧ final.providerRequests = 1 ∧
    final.publications = 1 ∧ final.usageReceipts = 1 ∧
    final.durable = some answer ∧ final.leaseActive = false := by
  simp [run, step, afterReceive, writing, inspecting, inspectReceipt, receiptObservation, commit, owned]

/-- A confirmed rollback retries the local write and retains the same answer. -/
theorem readback_recovers_rolled_back_commit (answer : Answer) :
    let final := run (afterReceive answer)
      [.write .unknownRolledBack, .inspect true, .write .committed, .publish]
    final.phase = .published ∧ final.providerRequests = 1 ∧
    final.publications = 1 ∧ final.durable = some answer ∧
    final.leaseActive = false := by
  simp [run, step, afterReceive, writing, inspecting, inspectReceipt, receiptObservation, commit, owned]

theorem repeated_publication_is_ignored (state : State)
    (published : state.phase = .published) : step state .publish = state := by
  simp [step, published]

theorem foreign_receipt_is_not_authority (state : State) (receipt : Answer)
    (foreign : receipt.identity ≠ state.identity)
    (saved : state.durable = some receipt)
    (phase : state.phase = .readback) :
    (step state (.inspect true)).phase = .conflict := by
  simp [step, inspecting, phase, saved, inspectReceipt, receiptObservation, owned, foreign]

/-- The former generic-error path dropped the answer and rearmed submission. -/
def discardOnLocalFailure (state : State) : State :=
  { state with phase := .ready, retained := none, leaseActive := false }

theorem discarding_failure_permits_a_second_request (answer : Answer) :
    (step (discardOnLocalFailure (afterReceive answer)) .submit).providerRequests = 2 ∧
    (discardOnLocalFailure (afterReceive answer)).retained = none := by
  simp [discardOnLocalFailure, afterReceive, step]

def abandonWithoutSettlement (state : State) : State :=
  { state with phase := .submitted, retained := none }

theorem abandoned_live_lease_rejects_every_new_submit (answer : Answer) (count : Nat) :
    run (abandonWithoutSettlement (afterReceive answer))
      (List.replicate count .submit) = abandonWithoutSettlement (afterReceive answer) := by
  induction count with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, run, step, abandonWithoutSettlement, afterReceive] using ih

/-- A committed completion cannot continue holding the admission lease. -/
theorem commit_releases_lease (state : State) (phase : Phase) :
    (commit state phase).leaseActive = false := rfl

/-- This unavoidable information-loss case is not hidden by the model. -/
theorem crash_before_write_has_no_recoverable_answer (answer : Answer) :
    let crashed := step (afterReceive answer) .crash
    crashed.retained = none ∧ crashed.durable = none ∧
    crashed.phase = .unknown ∧ step crashed .submit = crashed := by
  simp [step, afterReceive]

end PettaClaw.LlmCompletionRecovery

#print axioms PettaClaw.LlmCompletionRecovery.only_submit_can_increase_provider_requests
#print axioms PettaClaw.LlmCompletionRecovery.readback_recovers_landed_commit
#print axioms PettaClaw.LlmCompletionRecovery.readback_recovers_rolled_back_commit
#print axioms PettaClaw.LlmCompletionRecovery.retries_cannot_make_another_provider_request

-- The fixture checker consumes these finite observations and exercises the
-- real native SQLite query for the same combinations in both dialects.
open PettaClaw.LlmCompletionRecovery in
#eval (do
  for (request : RequestState) in [RequestState.pending, .completed, .other] do
    for (call : CallState) in [CallState.active, .completed, .other] do
      for (owner : Bool) in [false, true] do
        for (answer : Bool) in [false, true] do
          let r := match request with
            | RequestState.pending => "pending" | RequestState.completed => "completed" | RequestState.other => "failed"
          let c := match call with
            | CallState.active => "submitted" | CallState.completed => "completed" | CallState.other => "uncertain"
          let result := match receiptObservation request call owner answer with
            | .committed => "committed" | .pending => "pending" | .conflict => "conflict"
          IO.println s!"RECOVERY_CASE {r} {c} {owner} {answer} {result}"
  : IO Unit)
