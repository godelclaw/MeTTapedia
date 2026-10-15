import FairGoalScheduling

/-!
# Owned asynchronous topic requests over one goal ledger

Provider attempts may overlap across independent topics. Each topic retains
one decision attempt until observation and explicit retirement. The existing
weighted goal queue allocates attempts, and the existing request ledger owns
unfinished work, tool receipts and checked completion. There is no second
completion rule or topic-specific goal database.

A terminal provider reply first becomes owned evidence. Observation does not
grant effect authority: context versions, declared dependencies, global control
revision and captured permissions are checked again at dispatch. Tool effects
remain serialized through the existing broker and its observation barrier.
The shared AdmissionFrontier gate admits thought independently of that barrier;
the barrier is checked explicitly when a terminal command is issued.

The host must checkpoint identities, versions, reservations and routing
atomically. All shared reads must declare dependencies, all relevant writes
must advance a version, and byte accounting must include retained payloads.
Reservations bound represented response storage, not decoder/TLS internals or
all process memory. A session-local transport handle is not a durable call ID.
Soft waiting does not extend a hard transport deadline or retry a remote POST.
-/

namespace TopicAsync

open Mettapedia.CogArch.Agent
abbrev Topic := Nat

structure CallId where
  agentId : Nat
  generation : Nat
  serial : Nat
deriving Repr, DecidableEq

structure Context where
  revision : Nat := 0
  boundary : IterArchitecture.Boundary := ⟨[], []⟩

structure Call where
  id : CallId
  topic : Topic
  topicRevision : Nat
  dependencies : List (Topic × Nat)
  snapshot : ObservedStrategy.Snapshot
  reservedBytes : Nat

deriving Repr, DecidableEq

inductive Phase where
  | waiting
  | uncertain
  | terminal (reply : ObservedStrategy.Reply)

deriving Repr, DecidableEq

structure Slot where
  call : Call
  phase : Phase := .waiting
  progressBytes : Nat := 0
  observed : Bool := false
  handled : Bool := false

deriving Repr, DecidableEq

structure Config where
  goals : GoalSystem.Config
  topicForGoal : Nat → Topic

structure State where
  core : GoalSystem.State
  contexts : Topic → Context
  owners : ConversationContinuation.RequestKey → Option Topic
  calls : List Slot := []
  agentId : Nat := 0
  generation : Nat := 0
  maxCalls : Nat := 1
  maxBytes : Nat := 0

/-- Count every retained attempt, including uncertain and unobserved results. -/
def retainedBytes (calls : List Slot) : Nat :=
  (calls.map fun slot => slot.call.reservedBytes).sum

def Bounded (state : State) : Prop :=
  state.calls.length ≤ state.maxCalls ∧ retainedBytes state.calls ≤ state.maxBytes

/-- No provider attempt is erased merely because its connection became slow. -/
def softWait (state : State) : State := state

/-- The original topic owns the work for its entire request lifetime. -/
def deliver (state : State) (topic : Topic) (key : ConversationContinuation.RequestKey) : State :=
  if state.owners key = none then
    { state with
      core := { state.core with agent := { state.core.agent with
        requests := ConversationContinuation.accept state.core.agent.requests key } }
      contexts := fun other => if other = topic then
        { state.contexts other with
          revision := (state.contexts other).revision + 1
          boundary := { (state.contexts other).boundary with
            messages := (state.contexts other).boundary.messages ++ [key.serial] } }
        else state.contexts other
      owners := fun other => if other = key then some topic else state.owners other }
  else state

def acknowledge (state : State) (key : ConversationContinuation.RequestKey) : State :=
  { state with core := { state.core with agent := ObservedStrategy.acknowledge state.core.agent key } }

/-- Shared resource or topic writes invalidate every capture that declared it. -/
def changed (state : State) (topic : Topic) : State :=
  { state with contexts := fun other => if other = topic then
      { state.contexts other with revision := (state.contexts other).revision + 1 }
    else state.contexts other }

def topicReady (state : State) (topic : Topic) : Bool :=
  !(state.calls.any fun slot => decide (slot.call.topic = topic))

/-- A topic can receive attention only for an accepted, owned active request.
An inactive queue entry must not block another topic's runnable work. -/
def readyGoal (cfg : Config) (state : State) (goal : GoalSystem.Goal) : Bool :=
  let topic := cfg.topicForGoal goal.id
  let focus := cfg.goals.key (goal.id, goal.round)
  topicReady state topic && decide (state.owners focus = some topic) &&
    decide (state.core.agent.requests.commitments focus = .active)

/-- This is a view of the existing queue; it does not alter goal meaning. -/
def readyGoals (cfg : Config) (state : State) : List GoalSystem.Goal :=
  state.core.goals.filter (readyGoal cfg state)

def next (cfg : Config) (state : State) : Option GoalSystem.Goal :=
  FairGoalScheduling.select (readyGoals cfg state)

def topicAgent (state : State) (topic : Topic) : ObservedStrategy.State :=
  { state.core.agent with boundary := (state.contexts topic).boundary }

def canCapture (state : State) (now : Int) (topic : Topic)
    (focus : ConversationContinuation.RequestKey) (bytes : Nat) : Bool :=
  topicReady state topic && decide (state.owners focus = some topic) &&
  decide (state.calls.length < state.maxCalls) &&
  decide (retainedBytes state.calls + bytes ≤ state.maxBytes) &&
  ObservedStrategy.canCapture (topicAgent state topic) now focus

theorem broker_frontier_cannot_block_topic_thinking (state : State) (now : Int)
    (topic : Topic) (focus : ConversationContinuation.RequestKey) (bytes : Nat)
    (phase : ConversationContinuation.Phase) (dispatch : Option ObservedStrategy.Dispatch) :
    canCapture { state with core := { state.core with agent := { state.core.agent with
      requests := { state.core.agent.requests with phase := phase }
      dispatch := dispatch } } } now topic focus bytes =
      canCapture state now topic focus bytes := rfl

def makeCall (state : State) (topic : Topic) (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation) (dependencies : List Topic) (bytes : Nat) : Call :=
  { id := ⟨state.agentId, state.generation, state.core.agent.nextSample⟩
    topic := topic
    topicRevision := (state.contexts topic).revision
    dependencies := dependencies.map fun dependency => (dependency, (state.contexts dependency).revision)
    snapshot := ObservedStrategy.snapshot (topicAgent state topic) focus changes
    reservedBytes := bytes }

/-- Capture and charge are one transition. Only the pending provider coordinate
moves into the owned pool; protected requests and broker state remain shared. -/
def capture (cfg : Config) (state : State) (now : Int) (goal : GoalSystem.Goal)
    (changes : List IterArchitecture.Transformation) (dependencies : List Topic) (bytes : Nat) : State :=
  let topic := cfg.topicForGoal goal.id
  let focus := cfg.goals.key (goal.id, goal.round)
  if next cfg state = some goal ∧ canCapture state now topic focus bytes = true then
    let sampled := ObservedStrategy.capture (topicAgent state topic) now focus changes
    { state with
      core := { agent := { sampled with pending := none, boundary := state.core.agent.boundary }
                goals := FairGoalScheduling.charge goal.id 1 state.core.goals }
      calls := state.calls ++ [{ call := makeCall state topic focus changes dependencies bytes }] }
  else state

def mapSlot (state : State) (id : CallId) (update : Slot → Slot) : State :=
  { state with calls := state.calls.map fun slot => if slot.call.id = id then update slot else slot }

/-- Progress is provisional and cannot settle a call or propose a tool. -/
def progress (state : State) (id : CallId) (bytes : Nat) : State :=
  mapSlot state id fun slot =>
    if slot.phase = .waiting ∧ bytes ≤ slot.call.reservedBytes then
      { slot with progressBytes := bytes }
    else slot

/-- The supplied identity selects the captured owner; payloads cannot retarget
an answer. Oversized bodies become explicit terminal failure evidence. -/
def receive (state : State) (id : CallId) (reply : ObservedStrategy.Reply) (bytes : Nat) : State :=
  mapSlot state id fun slot =>
    match slot.phase with
    | .terminal _ => slot
    | .waiting | .uncertain =>
        { slot with
          phase := .terminal (if bytes ≤ slot.call.reservedBytes then reply else .failure 1 1)
          progressBytes := if bytes ≤ slot.call.reservedBytes then bytes else 0 }

def observe (state : State) (id : CallId) : State :=
  mapSlot state id fun slot =>
    match slot.phase with
    | .terminal _ => { slot with observed := true }
    | _ => slot

def current (state : State) (call : Call) : Bool :=
  decide (call.snapshot.revision = state.core.agent.revision) &&
  decide (call.snapshot.mode = state.core.agent.mode) &&
  decide (call.topicRevision = (state.contexts call.topic).revision) &&
  decide (state.owners call.snapshot.focus = some call.topic) &&
  call.dependencies.all (fun dependency => decide
    ((state.contexts dependency.1).revision = dependency.2))

/-- Reuse admission, permissions and the global dependent-effect barrier.
Each terminal proposal has at most one admission attempt, even if denied.
Observed failure evidence applies shared cooldown independently of authority
currency: a stale quota failure still describes the provider's availability. -/
def issue (state : State) (now : Int) (id : CallId) : State :=
  match state.calls.find? (fun slot => decide (slot.call.id = id)) with
  | none => state
  | some slot =>
      match slot.phase with
      | .terminal (.command ticket tool) =>
          if slot.observed && !slot.handled && current state slot.call &&
              ObservedStrategy.ready state.core.agent &&
              ObservedStrategy.effectsReady state.core.agent then
            let admitted := ObservedStrategy.reply
              { state.core.agent with pending := some slot.call.snapshot }
              now slot.call.snapshot.serial (.command ticket tool)
            { (mapSlot state id fun entry => { entry with handled := true }) with
              core := { state.core with agent := admitted } }
          else state
      | .terminal (.failure _ retryAfter) =>
          if slot.observed && !slot.handled then
            { (mapSlot state id fun entry => { entry with handled := true }) with
              core := { state.core with agent := (ObservedStrategy.cooldown
                state.core.agent (now + max 1 retryAfter)) } }
          else state
      | _ => state

/-- Retirement frees owned storage only after observation. A live current
command proposal must first cross admission; stale evidence may be retired. -/
def retire (state : State) (id : CallId) : State :=
  { state with calls := state.calls.filter fun slot =>
      if slot.call.id ≠ id then true else
        match slot.phase with
        | .terminal (.command _ _) => !(slot.observed && (slot.handled || !current state slot.call))
        | .terminal (.failure _ _) => !(slot.observed && slot.handled)
        | .terminal _ => !slot.observed
        | _ => true }

/-- A sent attempt becomes uncertain, not unsent. Its owner and reservation
survive recovery; any late terminal can still be recorded as stale evidence. -/
def restore (state : State) : State :=
  { state with
    core := { state.core with agent := ObservedStrategy.restore state.core.agent }
    generation := state.generation + 1
    calls := state.calls.map fun slot =>
      match slot.phase with
      | .waiting => { slot with phase := .uncertain }
      | _ => slot }

/-- The old provider path cannot bypass owned topic capture or correlation.
Mode/router changes retain the shared authority version. Delivery requires
an explicit topic, and restart must restore the owned pool as well. -/
def control (state : State) (event : ObservedStrategy.OperationalEvent) : State :=
  match event with
  | .delivered _ | .captured _ _ _ | .replied _ _ _ => state
  | .restarted => restore state
  | other => { state with core := { state.core with agent := ObservedStrategy.step state.core.agent other } }

/-! Transport and routing laws. -/

theorem soft_wait_preserves_every_coordinate (state : State) : softWait state = state := rfl

theorem request_owner_cannot_be_reassigned (state : State) (topic : Topic)
    (key : ConversationContinuation.RequestKey) (owned : state.owners key ≠ none) :
    deliver state topic key = state := by simp [deliver, owned]

theorem unrelated_topic_version_is_unchanged (state : State) (topic other : Topic)
    (different : other ≠ topic) :
    (changed state topic).contexts other = state.contexts other := by simp [changed, different]

theorem changed_context_invalidates_capture (state : State) (call : Call)
    (fresh : call.topicRevision = (state.contexts call.topic).revision) :
    current (changed state call.topic) call = false := by
  simp [current, changed, fresh]

theorem map_slot_preserves_protected_work (state : State) (id : CallId) (update) :
    (mapSlot state id update).core = state.core := rfl

theorem progress_does_not_dispatch (state : State) (id : CallId) (bytes : Nat) :
    (progress state id bytes).core = state.core := rfl

theorem terminal_text_does_not_complete_work (state : State) (id : CallId) (text bytes : Nat) :
    (receive state id (.text text) bytes).core = state.core := rfl

theorem observing_provider_does_not_complete_work (state : State) (id : CallId) :
    (observe state id).core = state.core := rfl

theorem retirement_preserves_work_and_service (state : State) (id : CallId) :
    (retire state id).core = state.core := rfl

theorem terminal_settlement_is_idempotent (state : State) (id : CallId)
    (first second : ObservedStrategy.Reply) (firstBytes secondBytes : Nat) :
    receive (receive state id first firstBytes) id second secondBytes =
      receive state id first firstBytes := by
  simp only [receive, mapSlot, List.map_map]
  congr 2
  funext slot
  by_cases matching : slot.call.id = id
  · cases phase : slot.phase <;> simp [matching, phase]
  · simp [matching]

/-- Independent arrival order changes neither owner nor final retained result. -/
theorem distinct_results_commute (state : State) (firstId secondId : CallId)
    (first second : ObservedStrategy.Reply) (firstBytes secondBytes : Nat)
    (different : firstId ≠ secondId) :
    receive (receive state firstId first firstBytes) secondId second secondBytes =
      receive (receive state secondId second secondBytes) firstId first firstBytes := by
  simp only [receive, mapSlot, List.map_map]
  congr 2
  funext slot
  by_cases firstMatch : slot.call.id = firstId
  · have secondMiss : slot.call.id ≠ secondId := by
      intro secondMatch
      exact different (firstMatch.symm.trans secondMatch)
    cases phase : slot.phase <;> simp [firstMatch, secondMiss, different, phase]
  · by_cases secondMatch : slot.call.id = secondId
    · cases phase : slot.phase <;> simp [firstMatch, secondMatch, different, Ne.symm different, phase]
    · simp [firstMatch, secondMatch]

theorem foreign_delivery_stutters (state : State) (id : CallId)
    (reply : ObservedStrategy.Reply) (bytes : Nat)
    (foreign : ∀ slot ∈ state.calls, slot.call.id ≠ id) :
    receive state id reply bytes = state := by
  unfold receive mapSlot
  have same : state.calls.map (fun slot => if slot.call.id = id then
      (match slot.phase with
       | .terminal _ => slot
       | .waiting | .uncertain =>
           { slot with phase := .terminal (if bytes ≤ slot.call.reservedBytes then reply else .failure 1 1),
                       progressBytes := if bytes ≤ slot.call.reservedBytes then bytes else 0 })
      else slot) = state.calls := by
    calc
      _ = state.calls.map (fun slot => slot) := by
        apply List.map_congr_left
        intro slot member
        simp [foreign slot member]
      _ = state.calls := by simp
  simp [same]

theorem receive_changes_only_original_owner (state : State) (id : CallId)
    (reply : ObservedStrategy.Reply) (bytes : Nat) (other : Slot)
    (foreign : other.call.id ≠ id) (member : other ∈ state.calls) :
    other ∈ (receive state id reply bytes).calls := by
  apply List.mem_map.mpr
  exact ⟨other, member, by simp [receive, mapSlot, foreign]⟩

theorem restore_preserves_protected_requests_and_spend (state : State) :
    (restore state).core.agent.requests = state.core.agent.requests ∧
    (restore state).core.agent.allowance = state.core.agent.allowance ∧
    (restore state).core.goals = state.core.goals ∧
    (restore state).core.agent.nextSample = state.core.agent.nextSample := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem restore_invalidates_old_capture (state : State) (call : Call)
    (fresh : call.snapshot.revision = state.core.agent.revision) :
    current (restore state) call = false := by
  simp [current, restore, ObservedStrategy.restore, fresh]

/-! Admission, storage and service laws. -/

theorem map_slot_preserves_length (state : State) (id : CallId) (update) :
    (mapSlot state id update).calls.length = state.calls.length := by
  simp [mapSlot]

theorem map_slot_preserves_reservations (state : State) (id : CallId) (update)
    (preserved : ∀ slot, (update slot).call.reservedBytes = slot.call.reservedBytes) :
    retainedBytes (mapSlot state id update).calls = retainedBytes state.calls := by
  simp only [mapSlot, retainedBytes, List.map_map]
  congr 1
  apply List.map_congr_left
  intro slot member
  by_cases matching : slot.call.id = id
  · simpa [matching] using preserved slot
  · simp [matching]

theorem map_slot_preserves_bounds (state : State) (id : CallId) (update)
    (preserved : ∀ slot, (update slot).call.reservedBytes = slot.call.reservedBytes)
    (bounded : Bounded state) : Bounded (mapSlot state id update) := by
  constructor
  · simpa [mapSlot] using bounded.1
  · rw [map_slot_preserves_reservations state id update preserved]
    exact bounded.2

theorem progress_preserves_bounds (state : State) (id : CallId) (bytes : Nat)
    (bounded : Bounded state) : Bounded (progress state id bytes) := by
  apply map_slot_preserves_bounds _ _ _ _ bounded
  intro slot
  split <;> rfl

theorem receive_preserves_bounds (state : State) (id : CallId)
    (reply : ObservedStrategy.Reply) (bytes : Nat) (bounded : Bounded state) :
    Bounded (receive state id reply bytes) := by
  apply map_slot_preserves_bounds _ _ _ _ bounded
  intro slot
  cases slot.phase <;> rfl

theorem observation_preserves_bounds (state : State) (id : CallId)
    (bounded : Bounded state) : Bounded (observe state id) := by
  apply map_slot_preserves_bounds _ _ _ _ bounded
  intro slot
  cases slot.phase <;> rfl

private theorem filtered_reservations_le (calls : List Slot) (keep : Slot → Bool) :
    retainedBytes (calls.filter keep) ≤ retainedBytes calls := by
  induction calls with
  | nil => simp [retainedBytes]
  | cons slot calls ih =>
      cases kept : keep slot <;> simp [List.filter, kept, retainedBytes] at * <;> omega

theorem retirement_preserves_bounds (state : State) (id : CallId)
    (bounded : Bounded state) : Bounded (retire state id) := by
  constructor
  · exact Nat.le_trans (List.length_filter_le _ _) bounded.1
  · exact Nat.le_trans (filtered_reservations_le state.calls _) bounded.2

theorem chosen_goal_is_ready_and_existing (cfg : Config) (state : State) (goal : GoalSystem.Goal)
    (selected : next cfg state = some goal) :
    goal ∈ state.core.goals ∧ topicReady state (cfg.topicForGoal goal.id) = true ∧
    FairGoalScheduling.runnable goal = true := by
  obtain ⟨member, available, _⟩ := FairGoalScheduling.selection_contract _ goal selected
  obtain ⟨member, ready⟩ := List.mem_filter.mp member
  simp only [readyGoal, Bool.and_eq_true, decide_eq_true_eq] at ready
  exact ⟨member, ready.1.1, available⟩

theorem chosen_goal_has_active_owned_request (cfg : Config) (state : State) (goal : GoalSystem.Goal)
    (selected : next cfg state = some goal) :
    state.owners (cfg.goals.key (goal.id, goal.round)) = some (cfg.topicForGoal goal.id) ∧
    state.core.agent.requests.commitments (cfg.goals.key (goal.id, goal.round)) = .active := by
  obtain ⟨member, _, _⟩ := FairGoalScheduling.selection_contract _ goal selected
  have ready := (List.mem_filter.mp member).2
  simp only [readyGoal, Bool.and_eq_true, decide_eq_true_eq] at ready
  exact ⟨ready.1.2, ready.2⟩

theorem accepted_capture_contract (cfg : Config) (state : State) (now : Int)
    (goal : GoalSystem.Goal) (changes : List IterArchitecture.Transformation)
    (dependencies : List Topic) (bytes : Nat)
    (selected : next cfg state = some goal)
    (allowed : canCapture state now (cfg.topicForGoal goal.id)
      (cfg.goals.key (goal.id, goal.round)) bytes = true) :
    (capture cfg state now goal changes dependencies bytes).calls = state.calls ++
      [{ call := (makeCall state (cfg.topicForGoal goal.id)
        (cfg.goals.key (goal.id, goal.round)) changes dependencies bytes) }] ∧
    (capture cfg state now goal changes dependencies bytes).core.goals =
      FairGoalScheduling.charge goal.id 1 state.core.goals := by
  simp [capture, selected, allowed]

theorem capture_preserves_bounds (cfg : Config) (state : State) (now : Int)
    (goal : GoalSystem.Goal) (changes : List IterArchitecture.Transformation)
    (dependencies : List Topic) (bytes : Nat) (bounded : Bounded state) :
    Bounded (capture cfg state now goal changes dependencies bytes) := by
  dsimp only [capture]
  split
  · rename_i accepted
    have count : state.calls.length < state.maxCalls := by
      have allowed := accepted.2
      simp only [canCapture, Bool.and_eq_true, decide_eq_true_eq] at allowed
      omega
    have storage : retainedBytes state.calls + bytes ≤ state.maxBytes := by
      have allowed := accepted.2
      simp only [canCapture, Bool.and_eq_true, decide_eq_true_eq] at allowed
      omega
    constructor
    · simpa using (Nat.succ_le_of_lt count)
    · simpa [retainedBytes, makeCall] using storage
  · exact bounded

theorem capture_charges_exactly_one_goal (cfg : Config) (state : State) (now : Int)
    (goal : GoalSystem.Goal) (changes : List IterArchitecture.Transformation)
    (dependencies : List Topic) (bytes : Nat)
    (unique : FairGoalScheduling.UniqueIds state.core.goals)
    (selected : next cfg state = some goal)
    (allowed : canCapture state now (cfg.topicForGoal goal.id)
      (cfg.goals.key (goal.id, goal.round)) bytes = true) :
    FairGoalScheduling.totalService (capture cfg state now goal changes dependencies bytes).core.goals =
      FairGoalScheduling.totalService state.core.goals + 1 := by
  rw [(accepted_capture_contract cfg state now goal changes dependencies bytes selected allowed).2]
  exact FairGoalScheduling.charge_exactly_one_account _ goal 1 unique
    (chosen_goal_is_ready_and_existing cfg state goal selected).1

/-- The existing finite-cohort service bound applies to this queue view.
Continued admission, free capacity, timely observation/retirement and a stable
ready cohort are host obligations; this is not a wall-clock promise. -/
theorem finite_ready_cohort_gets_service (cfg : Config) (state : State) (goal : GoalSystem.Goal)
    (member : goal ∈ readyGoals cfg state) (available : FairGoalScheduling.runnable goal = true) :
    goal.id ∈ FairGoalScheduling.trace
      (FairGoalScheduling.waitBudget goal (readyGoals cfg state) + 1) (readyGoals cfg state) :=
  FairGoalScheduling.no_starvation _ goal member available


/-! Conservation and authority laws for the concurrent adapter. -/

theorem capture_preserves_request_ledger (cfg : Config) (state : State) (now : Int)
    (goal : GoalSystem.Goal) (changes : List IterArchitecture.Transformation)
    (dependencies : List Topic) (bytes : Nat) :
    (capture cfg state now goal changes dependencies bytes).core.agent.requests =
      state.core.agent.requests := by
  dsimp only [capture]
  split
  · exact ObservedStrategy.capture_preserves_request_ledger _ _ _ _
  · rfl

theorem capture_conserves_shared_allowance (cfg : Config) (state : State) (now : Int)
    (goal : GoalSystem.Goal) (changes : List IterArchitecture.Transformation)
    (dependencies : List Topic) (bytes : Nat) :
    (capture cfg state now goal changes dependencies bytes).core.agent.allowance +
      (capture cfg state now goal changes dependencies bytes).core.agent.nextSample =
      state.core.agent.allowance + state.core.agent.nextSample := by
  dsimp only [capture]
  split
  · exact ObservedStrategy.capture_conserves_request_budget _ _ _ _
  · rfl

theorem occupied_topic_blocks_capture (cfg : Config) (state : State) (now : Int)
    (goal : GoalSystem.Goal) (changes : List IterArchitecture.Transformation)
    (dependencies : List Topic) (bytes : Nat)
    (busy : topicReady state (cfg.topicForGoal goal.id) = false) :
    capture cfg state now goal changes dependencies bytes = state := by
  simp [capture, canCapture, busy]

theorem duplicate_capture_stutters (cfg : Config) (state : State) (now : Int)
    (goal : GoalSystem.Goal) (changes : List IterArchitecture.Transformation)
    (dependencies : List Topic) (bytes : Nat) :
    capture cfg (capture cfg state now goal changes dependencies bytes)
      now goal changes dependencies bytes =
      capture cfg state now goal changes dependencies bytes := by
  by_cases accepted : next cfg state = some goal ∧
      canCapture state now (cfg.topicForGoal goal.id)
        (cfg.goals.key (goal.id, goal.round)) bytes = true
  · apply occupied_topic_blocks_capture
    simp [capture, accepted, topicReady, makeCall]
  · have unchanged : capture cfg state now goal changes dependencies bytes = state := by
      simp [capture, accepted]
    simp [unchanged]

theorem map_slot_preserves_owned_metadata (state : State) (id : CallId) (update)
    (preserved : ∀ slot, (update slot).call = slot.call) :
    (mapSlot state id update).calls.map Slot.call = state.calls.map Slot.call := by
  simp only [mapSlot, List.map_map]
  apply List.map_congr_left
  intro slot member
  by_cases matching : slot.call.id = id
  · simpa [matching] using preserved slot
  · simp [matching]

theorem receive_preserves_owned_metadata (state : State) (id : CallId)
    (reply : ObservedStrategy.Reply) (bytes : Nat) :
    (receive state id reply bytes).calls.map Slot.call = state.calls.map Slot.call := by
  apply map_slot_preserves_owned_metadata
  intro slot
  cases slot.phase <;> rfl

theorem restore_preserves_owned_metadata (state : State) :
    (restore state).calls.map Slot.call = state.calls.map Slot.call := by
  simp only [restore, List.map_map]
  apply List.map_congr_left
  intro slot member
  cases phase : slot.phase <;> simp [Function.comp_apply, phase]

theorem restore_preserves_bounds (state : State) (bounded : Bounded state) :
    Bounded (restore state) := by
  constructor
  · simpa [restore] using bounded.1
  · have same : retainedBytes (restore state).calls = retainedBytes state.calls := by
      simp only [retainedBytes, restore, List.map_map]
      congr 1
      apply List.map_congr_left
      intro slot member
      cases phase : slot.phase <;> simp [Function.comp_apply, phase]
    rw [same]
    exact bounded.2

theorem shared_dependency_change_invalidates_capture (state : State) (call : Call)
    (dependency : Topic)
    (declared : (dependency, (state.contexts dependency).revision) ∈ call.dependencies) :
    current (changed state dependency) call = false := by
  have invalid : (call.dependencies.all (fun pair => decide
      (((changed state dependency).contexts pair.1).revision = pair.2))) = false := by
    apply Bool.eq_false_iff.mpr
    intro valid
    have agrees := (List.all_eq_true.mp valid) _ declared
    simp [changed] at agrees
  simp [current, invalid]

theorem provider_issue_preserves_active_work (state : State) (now : Int) (id : CallId)
    (key : ConversationContinuation.RequestKey)
    (active : state.core.agent.requests.commitments key = .active) :
    (issue state now id).core.agent.requests.commitments key = .active := by
  unfold issue
  split
  · exact active
  · rename_i slot found
    cases phase : slot.phase with
    | waiting => simp [phase, active]
    | uncertain => simp [phase, active]
    | terminal reply =>
        cases reply with
        | text answer => simp [phase, active]
        | failure error retry =>
            simp only [phase]
            split <;> exact active
        | command ticket tool =>
            simp only [phase]
            split
            · exact ObservedStrategy.reply_preserves_active_work _ _ _ _ key active
            · exact active

theorem provider_issue_preserves_bounds (state : State) (now : Int) (id : CallId)
    (bounded : Bounded state) : Bounded (issue state now id) := by
  unfold issue
  split
  · exact bounded
  · rename_i slot found
    cases phase : slot.phase with
    | waiting => simpa [phase] using bounded
    | uncertain => simpa [phase] using bounded
    | terminal reply =>
        cases reply with
        | text answer => simpa [phase] using bounded
        | failure error retry =>
            simp only [phase]
            split
            · exact map_slot_preserves_bounds state id _ (fun _ => rfl) bounded
            · exact bounded
        | command ticket tool =>
            simp only [phase]
            split
            · exact map_slot_preserves_bounds state id _ (fun _ => rfl) bounded
            · exact bounded

/-- Mode changes, interruption, observed broker results and restart preserve
unfinished work; the old provider route is deliberately not admitted here. -/
theorem control_preserves_active_work (state : State)
    (event : ObservedStrategy.OperationalEvent) (key : ConversationContinuation.RequestKey)
    (active : state.core.agent.requests.commitments key = .active) :
    (control state event).core.agent.requests.commitments key = .active := by
  cases event <;> try exact active
  all_goals exact ObservedStrategy.operational_step_preserves_active_work _ _ _ active

theorem control_preserves_bounds (state : State)
    (event : ObservedStrategy.OperationalEvent) (bounded : Bounded state) :
    Bounded (control state event) := by
  cases event <;> try exact bounded
  exact restore_preserves_bounds state bounded

/-- Events over the owned pool share the same goal and effect ledger. Checked
completion remains a separate transition through the existing task checker. -/
inductive Event where
  | delivered (topic : Topic) (key : ConversationContinuation.RequestKey)
  | acknowledged (key : ConversationContinuation.RequestKey)
  | changed (topic : Topic)
  | captured (now : Int) (goal : GoalSystem.Goal)
      (changes : List IterArchitecture.Transformation) (dependencies : List Topic) (bytes : Nat)
  | progressed (id : CallId) (bytes : Nat)
  | received (id : CallId) (reply : ObservedStrategy.Reply) (bytes : Nat)
  | observed (id : CallId)
  | issued (now : Int) (id : CallId)
  | retired (id : CallId)
  | controlled (event : ObservedStrategy.OperationalEvent)
  | elapsed (ticks : Nat)

def step (cfg : Config) (state : State) : Event → State
  | .delivered topic key => deliver state topic key
  | .acknowledged key => acknowledge state key
  | .changed topic => changed state topic
  | .captured now goal changes dependencies bytes => capture cfg state now goal changes dependencies bytes
  | .progressed id bytes => progress state id bytes
  | .received id reply bytes => receive state id reply bytes
  | .observed id => observe state id
  | .issued now id => issue state now id
  | .retired id => retire state id
  | .controlled event => control state event
  | .elapsed ticks => { state with core := { state.core with
      goals := state.core.goals.map (GoalSystem.advance ticks) } }

def run (cfg : Config) : State → List Event → State
  | state, [] => state
  | state, event :: events => run cfg (step cfg state event) events

theorem operational_step_preserves_unfinished_work (cfg : Config) (state : State)
    (event : Event) (key : ConversationContinuation.RequestKey)
    (active : state.core.agent.requests.commitments key = .active) :
    (step cfg state event).core.agent.requests.commitments key = .active := by
  cases event with
  | delivered topic input =>
      simp only [step, deliver]
      split
      · exact ConversationContinuation.accept_preserves_active_work _ _ _ active
      · exact active
  | acknowledged input =>
      exact (ConversationContinuation.acknowledgement_preserves_work _ _ _).trans active
  | changed topic => exact active
  | captured now goal changes dependencies bytes =>
      rw [step, capture_preserves_request_ledger]
      exact active
  | progressed id bytes => exact active
  | received id reply bytes => exact active
  | observed id => exact active
  | issued now id => exact provider_issue_preserves_active_work _ _ _ _ active
  | retired id => exact active
  | controlled event => exact control_preserves_active_work _ _ _ active
  | elapsed ticks => exact active

theorem arbitrary_operational_trace_preserves_unfinished_work (cfg : Config) (state : State)
    (events : List Event) (key : ConversationContinuation.RequestKey)
    (active : state.core.agent.requests.commitments key = .active) :
    (run cfg state events).core.agent.requests.commitments key = .active := by
  induction events generalizing state with
  | nil => exact active
  | cons event events ih =>
      exact ih _ (operational_step_preserves_unfinished_work _ _ _ _ active)

theorem operational_step_preserves_bounds (cfg : Config) (state : State) (event : Event)
    (bounded : Bounded state) : Bounded (step cfg state event) := by
  cases event with
  | delivered topic key =>
      dsimp only [step, deliver]
      split <;> exact bounded
  | acknowledged key => exact bounded
  | changed topic => exact bounded
  | captured now goal changes dependencies bytes => exact capture_preserves_bounds _ _ _ _ _ _ _ bounded
  | progressed id bytes => exact progress_preserves_bounds _ _ _ bounded
  | received id reply bytes => exact receive_preserves_bounds _ _ _ _ bounded
  | observed id => exact observation_preserves_bounds _ _ bounded
  | issued now id => exact provider_issue_preserves_bounds _ _ _ bounded
  | retired id => exact retirement_preserves_bounds _ _ bounded
  | controlled event => exact control_preserves_bounds _ _ bounded
  | elapsed ticks => exact bounded

theorem arbitrary_operational_trace_preserves_bounds (cfg : Config) (state : State)
    (events : List Event) (bounded : Bounded state) : Bounded (run cfg state events) := by
  induction events generalizing state with
  | nil => exact bounded
  | cons event events ih => exact ih _ (operational_step_preserves_bounds _ _ _ bounded)


/-! Explicit command and completion boundaries. -/

theorem unobserved_terminal_cannot_act (state : State) (now : Int) (id : CallId)
    (slot : Slot) (located : state.calls.find? (fun entry => decide (entry.call.id = id)) = some slot)
    (unobserved : slot.observed = false) : issue state now id = state := by
  cases phase : slot.phase with
  | waiting => simp [issue, located, phase]
  | uncertain => simp [issue, located, phase]
  | terminal reply => cases reply <;> simp [issue, located, phase, unobserved]

theorem handled_terminal_cannot_act_again (state : State) (now : Int) (id : CallId)
    (slot : Slot) (located : state.calls.find? (fun entry => decide (entry.call.id = id)) = some slot)
    (handled : slot.handled = true) : issue state now id = state := by
  cases phase : slot.phase with
  | waiting => simp [issue, located, phase]
  | uncertain => simp [issue, located, phase]
  | terminal reply => cases reply <;> simp [issue, located, phase, handled]

theorem stale_command_cannot_act (state : State) (now : Int) (id : CallId)
    (slot : Slot) (ticket : ConversationContinuation.Ticket) (tool : Nat)
    (located : state.calls.find? (fun entry => decide (entry.call.id = id)) = some slot)
    (command : slot.phase = .terminal (.command ticket tool))
    (stale : current state slot.call = false) : issue state now id = state := by
  simp [issue, located, command, stale]

theorem handled_failure_has_positive_shared_cooldown (state : State) (now : Int) (id : CallId)
    (slot : Slot) (error : Nat) (retry : Int)
    (located : state.calls.find? (fun entry => decide (entry.call.id = id)) = some slot)
    (failure : slot.phase = .terminal (.failure error retry))
    (observed : slot.observed = true) (unhandled : slot.handled = false) :
    now + 1 ≤ (issue state now id).core.agent.cooldownUntil := by
  simp only [issue, located, failure, observed, unhandled, Bool.not_false,
    Bool.true_and, ↓reduceIte, ObservedStrategy.cooldown]
  have positive := Int.le_max_left 1 retry
  have retained := Int.le_max_right state.core.agent.cooldownUntil (now + max 1 retry)
  omega

/-- A completion check cannot erase an unobserved provider attempt. The goal's
existing successful-receipt checker is the only completion implementation. -/
def completeCycle (cfg : Config)
    (checks : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool)
    (state : State) (report : GoalSystem.Report) : State :=
  if topicReady state (cfg.topicForGoal report.goal) then
    { state with core := GoalSystem.acknowledge cfg.goals checks state.core report }
  else state

theorem checked_completion_reuses_existing_ledger (cfg : Config) (checks)
    (state : State) (report : GoalSystem.Report)
    (quiet : topicReady state (cfg.topicForGoal report.goal) = true) :
    (completeCycle cfg checks state report).core =
      GoalSystem.acknowledge cfg.goals checks state.core report := by
  simp [completeCycle, quiet]

theorem checked_completion_preserves_other_requests (cfg : Config) (checks)
    (state : State) (report : GoalSystem.Report) (key : ConversationContinuation.RequestKey)
    (different : key ≠ report.receipt.ticket.request) :
    (completeCycle cfg checks state report).core.agent.requests.commitments key =
      state.core.agent.requests.commitments key := by
  unfold completeCycle
  split
  · exact GoalSystem.acknowledgement_preserves_other_work _ _ _ _ _ different
  · rfl

theorem checked_completion_preserves_bounds (cfg : Config) (checks)
    (state : State) (report : GoalSystem.Report) (bounded : Bounded state) :
    Bounded (completeCycle cfg checks state report) := by
  unfold completeCycle
  split <;> exact bounded

/-- A durable serial allocator cannot collide with any retained call, even
when old and new transport generations coexist. -/
def FreshSerials (state : State) : Prop :=
  ∀ slot ∈ state.calls, slot.call.id.serial < state.core.agent.nextSample

theorem admitted_capture_advances_serial (cfg : Config) (state : State) (now : Int)
    (goal : GoalSystem.Goal) (changes : List IterArchitecture.Transformation)
    (dependencies : List Topic) (bytes : Nat)
    (selected : next cfg state = some goal)
    (allowed : canCapture state now (cfg.topicForGoal goal.id)
      (cfg.goals.key (goal.id, goal.round)) bytes = true) :
    (capture cfg state now goal changes dependencies bytes).core.agent.nextSample =
      state.core.agent.nextSample + 1 := by
  have coreAllowed : ObservedStrategy.canCapture (topicAgent state (cfg.topicForGoal goal.id))
      now (cfg.goals.key (goal.id, goal.round)) = true := by
    simp only [canCapture, Bool.and_eq_true] at allowed
    exact allowed.2
  simpa only [capture, selected, allowed, and_self, ↓reduceIte, topicAgent] using
    (ObservedStrategy.admitted_capture_submits_exactly_one_attempt
      (topicAgent state (cfg.topicForGoal goal.id)) now
      (cfg.goals.key (goal.id, goal.round)) changes coreAllowed).2.1

theorem capture_preserves_fresh_serials (cfg : Config) (state : State) (now : Int)
    (goal : GoalSystem.Goal) (changes : List IterArchitecture.Transformation)
    (dependencies : List Topic) (bytes : Nat) (fresh : FreshSerials state) :
    FreshSerials (capture cfg state now goal changes dependencies bytes) := by
  by_cases accepted : next cfg state = some goal ∧
      canCapture state now (cfg.topicForGoal goal.id)
        (cfg.goals.key (goal.id, goal.round)) bytes = true
  · intro slot member
    have advanced := admitted_capture_advances_serial cfg state now goal changes dependencies bytes
      accepted.1 accepted.2
    rw [(accepted_capture_contract cfg state now goal changes dependencies bytes
      accepted.1 accepted.2).1] at member
    rw [advanced]
    rcases List.mem_append.mp member with previous | newest
    · exact Nat.lt_trans (fresh slot previous) (Nat.lt_succ_self _)
    · simp only [List.mem_singleton] at newest
      subst slot
      exact Nat.lt_succ_self _
  · simpa [capture, accepted] using fresh

theorem new_capture_cannot_reuse_retained_identity (state : State) (topic : Topic)
    (focus : ConversationContinuation.RequestKey) (changes : List IterArchitecture.Transformation)
    (dependencies : List Topic) (bytes : Nat) (fresh : FreshSerials state)
    (slot : Slot) (member : slot ∈ state.calls) :
    (makeCall state topic focus changes dependencies bytes).id ≠ slot.call.id := by
  intro reused
  have serials := congrArg CallId.serial reused
  have before := fresh slot member
  simp only [makeCall] at serials
  omega

end TopicAsync
