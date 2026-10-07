import ObservedStrategy

/-!
# Periodic goal review alongside protected work

An elapsed-time counter is the smallest persistent review meta-goal. Its
salience saturates at the configured interval. Unread input and host admission
take precedence, but deferral does not pay the review debt. A due review wins
over background work at the next admitted, observation-complete boundary.

Acknowledgement requires a current, successful, observed ledger receipt and
a task-specific checker. Each review round has a distinct request key, so an
old receipt cannot acknowledge a later round. Review events preserve the
entire existing strategy state; mixed traces project exactly to that strategy.

Host obligations: elapsed time is measured faithfully and persisted with the
round counter; review keys are fresh and do not collide with other requests;
the configured checker validates an actual bounded review of goal evidence;
the acknowledgement revision is checked atomically at the post-observation
decision boundary. The model proves conditional selection, not progress when
input or resource denial lasts forever, truthful provider prose, or durability
of a physical checkpoint. No new tool permission or completion authority is
created by becoming due.
-/

namespace GoalReview

open Mettapedia.CognitiveArchitecture.Agent

structure Config where
  interval : Nat
  positive : 0 < interval
  key : Nat → ConversationContinuation.RequestKey
  key_injective : Function.Injective key

structure Clock where
  age : Nat := 0
  round : Nat := 0
deriving Repr, DecidableEq

structure State where
  agent : ObservedStrategy.State
  clock : Clock := {}

structure Report where
  revision : Nat
  receipt : ConversationContinuation.Receipt
deriving Repr, DecidableEq

inductive Choice where
  | input | wait | review | work
deriving Repr, DecidableEq

def due (cfg : Config) (clock : Clock) : Bool :=
  decide (cfg.interval ≤ clock.age)

def advance (cfg : Config) (elapsed : Nat) (clock : Clock) : Clock :=
  { clock with age := min cfg.interval (clock.age + elapsed) }

/-- Admission includes the existing resource/cooldown policy. Selection does
not itself dispatch a tool or consume a provider allowance. -/
def next (cfg : Config) (state : State) (admitted : Bool) : Choice :=
  if !state.agent.requests.inbox.isEmpty then .input
  else if !admitted || !ObservedStrategy.ready state.agent then .wait
  else if due cfg state.clock then .review else .work

def canAcknowledge (cfg : Config)
    (checks : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool)
    (state : State) (report : Report) : Bool :=
  ObservedStrategy.ready state.agent &&
    decide (report.revision = state.agent.revision ∧
      report.receipt.ticket.request = cfg.key state.clock.round ∧
      report.receipt ∈ state.agent.requests.journal ∧
      report.receipt.ticket ∈ state.agent.requests.observed) &&
    report.receipt.successful && checks (cfg.key state.clock.round) report.receipt

def acknowledge (cfg : Config)
    (checks : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool)
    (state : State) (report : Report) : State :=
  if canAcknowledge cfg checks state report then
    { state with clock := ⟨0, state.clock.round + 1⟩ }
  else state

inductive Event where
  | elapsed (ticks : Nat)
  | reviewed (report : Report)
  | operational (event : ObservedStrategy.OperationalEvent)

def step (cfg : Config)
    (checks : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool)
    (state : State) : Event → State
  | .elapsed ticks => { state with clock := advance cfg ticks state.clock }
  | .reviewed report => acknowledge cfg checks state report
  | .operational event => { state with agent := ObservedStrategy.step state.agent event }

def run (cfg : Config)
    (checks : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool) :
    State → List Event → State
  | state, [] => state
  | state, event :: events => run cfg checks (step cfg checks state event) events

def operationalEvents : List Event → List ObservedStrategy.OperationalEvent
  | [] => []
  | .operational event :: events => event :: operationalEvents events
  | _ :: events => operationalEvents events

theorem age_bounded (cfg : Config) (elapsed : Nat) (clock : Clock) :
    (advance cfg elapsed clock).age ≤ cfg.interval := by
  exact Nat.min_le_left _ _

theorem salience_monotone (cfg : Config) (elapsed : Nat) (clock : Clock)
    (bounded : clock.age ≤ cfg.interval) :
    clock.age ≤ (advance cfg elapsed clock).age := by
  simp only [advance]
  omega

/-- Once a whole interval has elapsed, review is due regardless of the
starting age. This supplies a finite bound without a fairness assumption. -/
theorem becomes_due (cfg : Config) (elapsed : Nat) (clock : Clock)
    (enough : cfg.interval ≤ elapsed) :
    due cfg (advance cfg elapsed clock) = true := by
  simp only [due, advance, decide_eq_true_eq]
  omega

theorem due_survives_time (cfg : Config) (elapsed : Nat) (clock : Clock)
    (owed : due cfg clock = true) :
    due cfg (advance cfg elapsed clock) = true := by
  simp only [due, decide_eq_true_eq] at owed ⊢
  simp only [advance]
  omega

/-- Splitting the same elapsed duration across pauses has identical state. -/
theorem elapsed_partition_independent (cfg : Config) (a b : Nat) (clock : Clock) :
    advance cfg b (advance cfg a clock) = advance cfg (a + b) clock := by
  cases clock
  simp only [advance]
  congr 1
  omega

theorem unread_input_preempts (cfg : Config) (state : State) (admitted : Bool)
    (unread : state.agent.requests.inbox.isEmpty = false) :
    next cfg state admitted = .input := by
  simp [next, unread]

theorem admission_denial_waits (cfg : Config) (state : State)
    (clear : state.agent.requests.inbox.isEmpty = true) :
    next cfg state false = .wait := by
  simp [next, clear]

theorem pending_observation_waits (cfg : Config) (state : State) (admitted : Bool)
    (clear : state.agent.requests.inbox.isEmpty = true)
    (blocked : ObservedStrategy.ready state.agent = false) :
    next cfg state admitted = .wait := by
  simp [next, clear, blocked]

/-- At an eligible boundary the host chooses review, rather than relying on
the provider to make a due maintenance task salient. -/
theorem due_review_precedes_background (cfg : Config) (state : State)
    (clear : state.agent.requests.inbox.isEmpty = true)
    (ready : ObservedStrategy.ready state.agent = true)
    (owed : due cfg state.clock = true) :
    next cfg state true = .review := by
  simp [next, clear, ready, owed]

theorem acknowledgement_contract (cfg : Config) (checks) (state : State) (report : Report) :
    canAcknowledge cfg checks state report = true ↔
      ObservedStrategy.ready state.agent = true ∧
      (report.revision = state.agent.revision ∧
        report.receipt.ticket.request = cfg.key state.clock.round ∧
        report.receipt ∈ state.agent.requests.journal ∧
        report.receipt.ticket ∈ state.agent.requests.observed) ∧
      report.receipt.successful = true ∧
      checks (cfg.key state.clock.round) report.receipt = true := by
  simp [canAcknowledge, Bool.and_eq_true, and_assoc]

theorem failed_acknowledgement_stutters (cfg : Config) (checks)
    (state : State) (report : Report)
    (failed : canAcknowledge cfg checks state report = false) :
    acknowledge cfg checks state report = state := by
  simp [acknowledge, failed]

theorem checked_review_resets (cfg : Config) (checks) (state : State) (report : Report)
    (checked : canAcknowledge cfg checks state report = true) :
    (acknowledge cfg checks state report).clock = ⟨0, state.clock.round + 1⟩ ∧
      due cfg (acknowledge cfg checks state report).clock = false := by
  simp [acknowledge, checked, due, Nat.not_le_of_gt cfg.positive]

theorem acknowledge_preserves_agent (cfg : Config) (checks)
    (state : State) (report : Report) :
    (acknowledge cfg checks state report).agent = state.agent := by
  simp [acknowledge]
  split <;> rfl

/-- A previously accepted receipt cannot clear a later round, even if the
same receipt is submitted with a fresh revision stamp. -/
theorem old_receipt_cannot_pay_new_round (cfg : Config) (checks)
    (state : State) (report : Report) (later : State) (newRevision : Nat)
    (checked : canAcknowledge cfg checks state report = true)
    (different : later.clock.round ≠ state.clock.round) :
    canAcknowledge cfg checks later { report with revision := newRevision } = false := by
  have original := ((acknowledgement_contract cfg checks state report).mp checked).2.1.2.1
  by_cases admitted : canAcknowledge cfg checks later { report with revision := newRevision } = true
  · have reused := ((acknowledgement_contract cfg checks later
        { report with revision := newRevision }).mp admitted).2.1.2.1
    have same : later.clock.round = state.clock.round :=
      cfg.key_injective (reused.symm.trans original)
    exact False.elim (different same)
  · exact Bool.eq_false_iff.mpr admitted

theorem operational_step_preserves_review (cfg : Config) (checks)
    (state : State) (event : ObservedStrategy.OperationalEvent) :
    (step cfg checks state (.operational event)).clock = state.clock := by
  rfl

/-- Selection has a finite bound when time advances and an autonomous
decision is admitted. Persistent input or denial is deliberately excluded. -/
theorem review_selected_after_interval (cfg : Config) (checks)
    (state : State) (elapsed : Nat)
    (enough : cfg.interval ≤ elapsed)
    (clear : state.agent.requests.inbox.isEmpty = true)
    (ready : ObservedStrategy.ready state.agent = true) :
    next cfg (step cfg checks state (.elapsed elapsed)) true = .review := by
  exact due_review_precedes_background cfg _ clear ready
    (becomes_due cfg elapsed state.clock enough)

theorem mixed_trace_projects_exactly (cfg : Config) (checks)
    (state : State) (events : List Event) :
    (run cfg checks state events).agent =
      ObservedStrategy.run state.agent (operationalEvents events) := by
  induction events generalizing state with
  | nil => rfl
  | cons event events ih =>
      cases event with
      | elapsed ticks =>
          simpa [run, step, operationalEvents] using
            ih { state with clock := advance cfg ticks state.clock }
      | reviewed report =>
          simpa [run, step, operationalEvents, acknowledge_preserves_agent] using
            ih (acknowledge cfg checks state report)
      | operational event =>
          simpa [run, step, operationalEvents, ObservedStrategy.run] using
            ih { state with agent := ObservedStrategy.step state.agent event }

theorem mixed_trace_preserves_unfinished_work (cfg : Config) (checks)
    (state : State) (events : List Event) (key : ConversationContinuation.RequestKey)
    (active : state.agent.requests.commitments key = .active) :
    (run cfg checks state events).agent.requests.commitments key = .active := by
  rw [mixed_trace_projects_exactly]
  exact ObservedStrategy.arbitrary_operational_trace_preserves_unfinished_work
    state.agent (operationalEvents events) key active

end GoalReview
