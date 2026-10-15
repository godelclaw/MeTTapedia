import TopicAsync

/-!
# Cooperative attention and reviewed background results

Transport arrival and cognitive attention are separate transitions. Ordinary
input is retained without changing a captured decision. Explicit steering
advances the affected context version; stop suspends through the shared control
state. Neither discards an outstanding provider attempt or unfinished request.

FIFO service is measured in available attention boundaries, not wall time.
The host must expose such boundaries, durably retain arrival identities, and
advance every dependency version affected by a correction. Unclassified text
cannot be assumed independent of a decision's premises.

Processing requires a successful provider turn and durable history. It does
not fulfill the user's request. Only confirmed, owned receipt notices become
eligible for deletion. Background results are evidence until foreground review;
adoption checks the original owner and dependencies and admits each result once.
-/

namespace CooperativeInput

open Mettapedia.CogArch.Agent
abbrev Key := ConversationContinuation.RequestKey

structure Arrival where
  key : Key
  topic : TopicAsync.Topic
deriving Repr, DecidableEq

structure Notice where
  input : Key
  owner : Nat
  lane : Nat
  message : Nat
deriving Repr, DecidableEq

structure State where
  core : TopicAsync.State
  waiting : List Arrival := []
  attended : List Key := []
  processed : List Key := []
  notices : List Notice := []
  adopted : List TopicAsync.CallId := []

def known (state : State) (key : Key) : Bool :=
  (state.waiting.any fun item => decide (item.key = key)) ||
    state.attended.contains key || state.processed.contains key

def enqueue (state : State) (arrival : Arrival) : State :=
  if known state arrival.key then state
  else { state with waiting := state.waiting ++ [arrival] }

def steer (state : State) (arrival : Arrival) : State :=
  if known state arrival.key then state
  else { state with
    core := TopicAsync.changed state.core arrival.topic
    waiting := arrival :: state.waiting }

def stopped (state : State) : State :=
  { state with core := TopicAsync.control state.core .paused }

def resumed (state : State) : State :=
  { state with core := TopicAsync.control state.core .resumed }

/-- The current tool operation has settled and no foreground decision is
pending. Background topics need not have finished to reach this boundary. -/
def available (state : State) : Bool :=
  !state.core.core.agent.requests.interrupted &&
    state.core.core.agent.pending.isNone && state.core.core.agent.dispatch.isNone

def attend (state : State) : State :=
  match state.waiting with
  | [] => state
  | arrival :: rest =>
      if available state then
        { state with core := TopicAsync.deliver state.core arrival.topic arrival.key
                     waiting := rest
                     attended := state.attended ++ [arrival.key] }
      else state

def settle (state : State) (key : Key) (providerSucceeded historyDurable : Bool) : State :=
  if key ∈ state.attended ∧ providerSucceeded = true ∧ historyDurable = true then
    { state with core := TopicAsync.acknowledge state.core key
                 processed := if key ∈ state.processed then state.processed
                              else state.processed ++ [key] }
  else state

def registerNotice (state : State) (notice : Notice) : State :=
  if known state notice.input && decide (notice.owner = state.core.agentId) &&
      !state.notices.contains notice then
    { state with notices := state.notices ++ [notice] }
  else state

def deletable (state : State) (notice : Notice) : Bool :=
  state.notices.contains notice && state.processed.contains notice.input &&
    decide (notice.owner = state.core.agentId)

/-- Receipt failure retains the owned notice for reconciliation. -/
def deleted (state : State) (notice : Notice) (confirmed : Bool) : State :=
  if deletable state notice && confirmed then
    { state with notices := state.notices.filter (fun item => decide (item ≠ notice)) }
  else state

def restart (state : State) : State :=
  { state with core := TopicAsync.restore state.core }

def adopt (state : State) (id : TopicAsync.CallId) (reviewed : Bool) : State :=
  match state.core.calls.find? (fun slot => decide (slot.call.id = id)) with
  | none => state
  | some slot =>
      match slot.phase with
      | .terminal (.text _) =>
          if reviewed && slot.observed && !slot.handled &&
              TopicAsync.current state.core slot.call && !state.adopted.contains id then
            { state with
              core := TopicAsync.changed
                (TopicAsync.mapSlot state.core id fun value => { value with handled := true })
                slot.call.topic
              adopted := state.adopted ++ [id] }
          else state
      | _ => state

theorem ordinary_arrival_preserves_core (state : State) (arrival : Arrival) :
    (enqueue state arrival).core = state.core := by
  simp only [enqueue]; split <;> rfl

theorem ordinary_arrival_preserves_decision_currency (state : State) (arrival : Arrival)
    (call : TopicAsync.Call) :
    TopicAsync.current (enqueue state arrival).core call = TopicAsync.current state.core call := by
  rw [ordinary_arrival_preserves_core]

theorem ordinary_arrival_retains_all_waiting (state : State) (arrival : Arrival)
    (item : Arrival) (present : item ∈ state.waiting) :
    item ∈ (enqueue state arrival).waiting := by
  simp only [enqueue]; split
  · exact present
  · exact List.mem_append_left _ present

theorem new_arrival_is_durably_represented (state : State) (arrival : Arrival)
    (fresh : known state arrival.key = false) :
    arrival ∈ (enqueue state arrival).waiting := by simp [enqueue, fresh]

theorem duplicate_arrival_stutters (state : State) (arrival : Arrival)
    (seen : known state arrival.key = true) : enqueue state arrival = state := by
  simp [enqueue, seen]

theorem steering_preserves_calls (state : State) (arrival : Arrival) :
    (steer state arrival).core.calls = state.core.calls := by
  simp only [steer]; split <;> rfl

theorem new_steering_invalidates_affected_capture (state : State) (arrival : Arrival)
    (call : TopicAsync.Call) (fresh : known state arrival.key = false)
    (own : call.topic = arrival.topic)
    (currentVersion : call.topicRevision = (state.core.contexts arrival.topic).revision) :
    TopicAsync.current (steer state arrival).core call = false := by
  simp only [steer, fresh, Bool.false_eq_true, ↓reduceIte]
  simp [TopicAsync.current, TopicAsync.changed, own, currentVersion]

theorem stop_preserves_waiting (state : State) :
    (stopped state).waiting = state.waiting := rfl

theorem stop_prevents_attention (state : State) : available (stopped state) = false := by
  simp [available, stopped, TopicAsync.control, ObservedStrategy.step,
        ObservedStrategy.pause, ConversationContinuation.interrupt]

theorem unavailable_attention_stutters (state : State) (busy : available state = false) :
    attend state = state := by
  cases waiting : state.waiting <;> simp [attend, waiting, busy]

theorem fifo_attention_removes_exactly_the_head (state : State) (arrival : Arrival)
    (rest : List Arrival) (queue : state.waiting = arrival :: rest)
    (free : available state = true) :
    (attend state).waiting = rest ∧
      (attend state).attended = state.attended ++ [arrival.key] := by
  simp [attend, queue, free]

def attentionTrace : Nat → State → State
  | 0, state => state
  | n + 1, state => attentionTrace n (attend state)

/-- Conditional liveness: with a boundary available at every step and no new
urgent arrivals, a finite FIFO prefix is consumed in its length of boundaries. -/
theorem finite_fifo_is_attended (state : State) (free : available state = true) :
    (attentionTrace state.waiting.length state).waiting = [] := by
  generalize size : state.waiting.length = n
  induction n generalizing state with
  | zero => have empty := List.length_eq_zero_iff.mp size
            simp [attentionTrace, empty]
  | succ n ih =>
      cases queue : state.waiting with
      | nil => simp [queue] at size
      | cons head tail =>
          have tailSize : tail.length = n := by simpa [queue] using size
          have nextFree : available (attend state) = true := by
            simp only [attend, queue, free, ↓reduceIte]
            by_cases owned : state.core.owners head.key = none
            · by_cases accepted : head.key ∈ state.core.core.agent.requests.accepted
              all_goals simpa [available, TopicAsync.deliver, owned,
                ConversationContinuation.accept, ConversationContinuation.setCommitment, accepted] using free
            · simpa [available, TopicAsync.deliver, owned] using free
          have nextSize : (attend state).waiting.length = n := by
            simpa [attend, queue, free] using tailSize
          exact ih (attend state) nextFree nextSize

theorem failed_provider_cannot_process (state : State) (key : Key) (durable : Bool) :
    settle state key false durable = state := by simp [settle]

theorem missing_history_cannot_process (state : State) (key : Key) (succeeded : Bool) :
    settle state key succeeded false = state := by simp [settle]

theorem unattended_input_cannot_process (state : State) (key : Key)
    (unattended : key ∉ state.attended) (succeeded durable : Bool) :
    settle state key succeeded durable = state := by simp [settle, unattended]

theorem processing_does_not_complete_work (state : State) (key other : Key)
    (succeeded durable : Bool) :
    (settle state key succeeded durable).core.core.agent.requests.commitments other =
      state.core.core.agent.requests.commitments other := by
  simp only [settle]; split
  · exact ConversationContinuation.acknowledgement_preserves_work _ _ _
  · rfl

theorem deletion_requires_known_owned_processed_notice (state : State) (notice : Notice)
    (allowed : deletable state notice = true) :
    notice ∈ state.notices ∧ notice.input ∈ state.processed ∧
      notice.owner = state.core.agentId := by
  simp only [deletable, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at allowed
  exact ⟨allowed.1.1, allowed.1.2, allowed.2⟩

theorem failed_deletion_retains_notice (state : State) (notice : Notice) :
    deleted state notice false = state := by simp [deleted]

theorem deletion_preserves_core_and_queue (state : State) (notice : Notice) (confirmed : Bool) :
    (deleted state notice confirmed).core = state.core ∧
      (deleted state notice confirmed).waiting = state.waiting := by
  simp only [deleted]; split <;> exact ⟨rfl, rfl⟩

theorem restart_retains_arrivals_notices_and_adoption_ids (state : State) :
    (restart state).waiting = state.waiting ∧
    (restart state).attended = state.attended ∧
    (restart state).processed = state.processed ∧
    (restart state).notices = state.notices ∧
    (restart state).adopted = state.adopted := by exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem unreviewed_background_result_cannot_merge (state : State) (id : TopicAsync.CallId) :
    adopt state id false = state := by
  simp only [adopt]; split
  · rfl
  · split <;> simp

theorem adopted_identity_cannot_merge_twice (state : State) (id : TopicAsync.CallId)
    (seen : id ∈ state.adopted) (reviewed : Bool) : adopt state id reviewed = state := by
  simp only [adopt]; split
  · rfl
  · split <;> simp [seen]

theorem merge_does_not_issue_tools (state : State) (id : TopicAsync.CallId) (reviewed : Bool) :
    (adopt state id reviewed).core.core.agent.requests = state.core.core.agent.requests := by
  simp only [adopt]; split
  · rfl
  · split
    · split <;> rfl
    · rfl

inductive Event where
  | arrived (arrival : Arrival)
  | steered (arrival : Arrival)
  | attended
  | settled (key : Key) (providerSucceeded historyDurable : Bool)
  | stopped | resumed | restarted
  | noticed (notice : Notice)
  | deleted (notice : Notice) (confirmed : Bool)
  | adopted (id : TopicAsync.CallId) (reviewed : Bool)

def step (state : State) : Event → State
  | .arrived arrival => enqueue state arrival
  | .steered arrival => steer state arrival
  | .attended => attend state
  | .settled key succeeded durable => settle state key succeeded durable
  | .stopped => stopped state
  | .resumed => resumed state
  | .restarted => restart state
  | .noticed notice => registerNotice state notice
  | .deleted notice confirmed => deleted state notice confirmed
  | .adopted id reviewed => adopt state id reviewed

theorem step_preserves_active_work (state : State) (event : Event) (key : Key)
    (active : state.core.core.agent.requests.commitments key = .active) :
    (step state event).core.core.agent.requests.commitments key = .active := by
  cases event with
  | arrived arrival => simpa [step, ordinary_arrival_preserves_core] using active
  | steered arrival => simp only [step, steer]; split <;> exact active
  | attended =>
      simp only [step, attend]; split
      · exact active
      · split
        · simp only [TopicAsync.deliver]; split
          · exact ConversationContinuation.accept_preserves_active_work _ _ _ active
          · exact active
        · exact active
  | settled input succeeded durable =>
      rw [step, processing_does_not_complete_work]; exact active
  | stopped => exact TopicAsync.control_preserves_active_work _ _ _ active
  | resumed => exact TopicAsync.control_preserves_active_work _ _ _ active
  | restarted => simpa [step, restart, TopicAsync.restore, ObservedStrategy.restore] using active
  | noticed notice => simp only [step, registerNotice]; split <;> exact active
  | deleted notice confirmed => rw [step, (deletion_preserves_core_and_queue _ _ _).1]; exact active
  | adopted id reviewed => rw [step, merge_does_not_issue_tools]; exact active

def run (state : State) (events : List Event) : State := events.foldl step state

theorem arbitrary_trace_preserves_unfinished_work (state : State) (events : List Event) (key : Key)
    (active : state.core.core.agent.requests.commitments key = .active) :
    (run state events).core.core.agent.requests.commitments key = .active := by
  induction events generalizing state with
  | nil => exact active
  | cons event events ih => exact ih _ (step_preserves_active_work _ _ _ active)

end CooperativeInput
