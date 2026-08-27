import CodingAgent

/-!
# ContextAttention — interruptible task context

This file isolates a context-management property that neither a long textual
history nor optional semantic retrieval supplies: fresh operator input must be
able to preempt autonomous work.

A task capsule is deliberately *not* the scheduler.  It contains the active
task's required facts and obligations, while a separate attention lane carries
human events.  Pending attention blocks autonomous steps until a matching
receipt acknowledges the event.  `stop` is stronger still: it halts
immediately, clears the active task, and is absorbing for autonomous work.

Semantic retrieval is supplementary and bounded.  Required facts and the
foreground human event occupy distinct fields of the request view, so an
approximate retriever cannot erase either one.

The model does not claim that a model responds correctly or that retrieval
returns relevant memories.  It proves scheduling, visibility, and separation
properties below that epistemic boundary.
-/

namespace ContextAttention

abbrev Fact := Nat
abbrev Obligation := Nat

structure Capsule where
  taskId : Nat
  required : List Fact
  openObligations : List Obligation
deriving Repr, DecidableEq

inductive HumanEvent
  | message (payload : Nat)
  | replaceTask (capsule : Capsule)
  | stop
deriving Repr, DecidableEq

/-- The capsule and attention lane are separate coordinates.  In particular,
rewriting `active` gives no access to `foreground`, `inbox`, or `halted`. -/
structure State where
  active : Option Capsule
  foreground : Option HumanEvent
  inbox : List HumanEvent
  acknowledged : List HumanEvent
  autonomousTurns : Nat
  halted : Bool
deriving Repr, DecidableEq

def initial : State := ⟨none, none, [], [], 0, false⟩

/-- Ordinary messages occupy a free foreground lane or queue behind the event
already awaiting acknowledgement.  `stop` bypasses both positions and takes
effect immediately. -/
def receive (state : State) : HumanEvent → State
  | .stop =>
      { state with
        active := none
        foreground := some .stop
        inbox := []
        halted := true }
  | event =>
      match state.foreground with
      | none => { state with foreground := some event }
      | some _ => { state with inbox := state.inbox ++ [event] }

/-- Development may replace the contents of an existing task capsule, but not
the attention lane or lifecycle authority. -/
def reviseCapsule (state : State) (change : Capsule → Capsule) : State :=
  { state with active := state.active.map change }

/-- Apply the control meaning of an acknowledged foreground event.  A normal
message leaves the task intact; a replacement becomes the active task. -/
def applyAcknowledgedDirective (state : State) : HumanEvent → State
  | .message _ => state
  | .replaceTask capsule => { state with active := some capsule }
  | .stop => receive state .stop

/-- A receipt is represented by the event identity it claims to acknowledge.
Only an exact match may clear the foreground lane. -/
def acknowledge (state : State) (receipt : HumanEvent) : State :=
  match state.foreground with
  | none => state
  | some current =>
      if current = receipt then
        let directed := applyAcknowledgedDirective state current
        match directed.inbox with
        | [] =>
            { directed with
              foreground := none
              acknowledged := directed.acknowledged ++ [current] }
        | next :: rest =>
            { directed with
              foreground := some next
              inbox := rest
              acknowledged := directed.acknowledged ++ [current] }
      else state

/-- Autonomous work is admitted only when the agent is running, no human event
is in the foreground, and no event is waiting behind it. -/
def autonomousStep (state : State) : State :=
  if state.halted then state
  else match state.foreground with
    | some _ => state
    | none =>
        if state.inbox.isEmpty then
          { state with autonomousTurns := state.autonomousTurns + 1 }
        else state

def autonomousRun : Nat → State → State
  | 0, state => state
  | n + 1, state => autonomousRun n (autonomousStep state)

/-! ## Interrupt and acknowledgement laws -/

theorem free_lane_receives_immediately (state : State) (event : HumanEvent)
    (notStop : event ≠ .stop) (free : state.foreground = none) :
    (receive state event).foreground = some event := by
  cases event <;> simp_all [receive]

theorem occupied_lane_queues_without_loss (state : State)
    (current event : HumanEvent) (notStop : event ≠ .stop)
    (occupied : state.foreground = some current) :
    (receive state event).foreground = some current ∧
      (receive state event).inbox = state.inbox ++ [event] := by
  cases event <;> simp_all [receive]

/-- A pending human event prevents even an arbitrarily long requested burst
of autonomous transitions. -/
theorem foreground_blocks_autonomous_run (state : State)
    (event : HumanEvent) (n : Nat) :
    autonomousRun n { state with foreground := some event } =
      { state with foreground := some event } := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [autonomousRun, autonomousStep, ih]

theorem queued_event_blocks_autonomous_step (state : State)
    (event : HumanEvent) (rest : List HumanEvent) :
    autonomousStep { state with foreground := none, inbox := event :: rest } =
      { state with foreground := none, inbox := event :: rest } := by
  simp [autonomousStep]

theorem mismatched_receipt_does_not_clear (state : State)
    (current receipt : HumanEvent) (different : current ≠ receipt) :
    acknowledge { state with foreground := some current } receipt =
      { state with foreground := some current } := by
  simp [acknowledge, different]

theorem matching_message_receipt_clears_free_queue (state : State)
    (payload : Nat) :
    let waiting :=
      { state with foreground := some (.message payload), inbox := [] }
    (acknowledge waiting (.message payload)).foreground = none ∧
      (acknowledge waiting (.message payload)).active = state.active ∧
      (acknowledge waiting (.message payload)).acknowledged =
        state.acknowledged ++ [.message payload] := by
  simp [acknowledge, applyAcknowledgedDirective]

theorem matching_replacement_receipt_installs_task (state : State)
    (capsule : Capsule) :
    let waiting :=
      { state with foreground := some (.replaceTask capsule), inbox := [] }
    (acknowledge waiting (.replaceTask capsule)).foreground = none ∧
      (acknowledge waiting (.replaceTask capsule)).active = some capsule := by
  simp [acknowledge, applyAcknowledgedDirective]

/-! ## Stop dominance and capsule noninterference -/

theorem stop_is_immediate (state : State) :
    (receive state .stop).halted = true ∧
      (receive state .stop).active = none ∧
      (receive state .stop).foreground = some .stop ∧
      (receive state .stop).inbox = [] := by
  simp [receive]

theorem stopped_autonomy_is_stutter (state : State) (already : state.halted) :
    autonomousStep state = state := by
  simp [autonomousStep, already]

theorem halted_blocks_autonomous_run (state : State) (already : state.halted)
    (n : Nat) :
    autonomousRun n state = state := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [autonomousRun, stopped_autonomy_is_stutter state already]
      exact ih

theorem stop_blocks_arbitrary_autonomous_run (state : State) (n : Nat) :
    autonomousRun n (receive state .stop) = receive state .stop := by
  exact halted_blocks_autonomous_run (receive state .stop) (by simp [receive]) n

theorem capsule_revision_preserves_attention (state : State)
    (change : Capsule → Capsule) :
    (reviseCapsule state change).foreground = state.foreground ∧
      (reviseCapsule state change).inbox = state.inbox ∧
      (reviseCapsule state change).halted = state.halted := by
  simp [reviseCapsule]

theorem capsule_revision_cannot_mask_fresh_message (state : State)
    (change : Capsule → Capsule) (payload : Nat)
    (free : state.foreground = none) :
    (reviseCapsule (receive state (.message payload)) change).foreground =
      some (.message payload) := by
  simp [receive, free, reviseCapsule]

/-! ## Required context versus optional semantic retrieval -/

structure RequestView where
  foreground : Option HumanEvent
  active : Option Capsule
  required : List Fact
  retrieved : List Fact
deriving Repr, DecidableEq

def requiredFacts (state : State) : List Fact :=
  match state.active with
  | none => []
  | some capsule => capsule.required

/-- Retrieval receives its own budget and cannot alter the foreground event,
active capsule, or required facts. -/
def assemble (retrievalBudget : Nat) (memoryCandidates : List Fact)
    (state : State) : RequestView :=
  { foreground := state.foreground
    active := state.active
    required := requiredFacts state
    retrieved := memoryCandidates.take retrievalBudget }

theorem assembly_preserves_foreground (budget : Nat) (memories : List Fact)
    (state : State) :
    (assemble budget memories state).foreground = state.foreground := rfl

theorem assembly_preserves_required_facts (budget : Nat)
    (memories : List Fact) (state : State) :
    (assemble budget memories state).required = requiredFacts state := rfl

theorem semantic_retrieval_is_bounded (budget : Nat) (memories : List Fact)
    (state : State) :
    (assemble budget memories state).retrieved.length ≤ budget := by
  simp [assemble, Nat.min_le_left]

/-- Changing every semantic candidate leaves the protected foreground and
required context byte-for-byte equal. -/
theorem retrieval_cannot_rewrite_mandatory_context (budget : Nat)
    (left right : List Fact) (state : State) :
    (assemble budget left state).foreground =
        (assemble budget right state).foreground ∧
      (assemble budget left state).required =
        (assemble budget right state).required := by
  constructor <;> rfl

end ContextAttention

/-! ## Axiom audit -/
#print axioms ContextAttention.foreground_blocks_autonomous_run
#print axioms ContextAttention.mismatched_receipt_does_not_clear
#print axioms ContextAttention.stop_blocks_arbitrary_autonomous_run
#print axioms ContextAttention.capsule_revision_cannot_mask_fresh_message
#print axioms ContextAttention.retrieval_cannot_rewrite_mandatory_context
