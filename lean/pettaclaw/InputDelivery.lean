import Mathlib.Data.List.Basic

/-!
# Input delivery across nondeterministic evaluation

An external input is not consumed by observation.  Observation prepares a
stable batch, a successful turn records that batch in durable history, and
only the resulting history receipt permits acknowledgement.  Inputs arriving
while a batch is being processed remain pending for the next turn.

This separates relational search from imperative queue mutation.  Re-entering
an observation during search returns the same batch, while provider failure,
parse failure, or process restart cannot silently acknowledge it.
-/

namespace PettaClaw.InputDelivery

abbrev EventId := Nat

inductive Phase where
  | idle
  | observed (batch : List EventId)
  | historicized (batch : List EventId)
deriving Repr, DecidableEq

structure State where
  pending : List EventId
  phase : Phase
  history : List EventId
  acknowledged : List EventId
deriving Repr, DecidableEq

def initial : State := ⟨[], .idle, [], []⟩

def receive (state : State) (event : EventId) : State :=
  { state with pending := state.pending ++ [event] }

/-- Freeze the current pending prefix without removing it. -/
def observe (state : State) : State :=
  match state.phase with
  | .idle => { state with phase := .observed state.pending }
  | _ => state

def observedBatch (state : State) : List EventId :=
  match (observe state).phase with
  | .observed batch => batch
  | .historicized batch => batch
  | .idle => []

/-- Failure changes no delivery coordinate.  The prepared batch remains the
foreground obligation for a later retry. -/
def fail (state : State) : State := state

/-- A successful turn first places the exact observed batch in durable
history.  There is no transition from `idle` to `historicized`. -/
def recordHistory (state : State) : State :=
  match state.phase with
  | .observed batch =>
      { state with
        phase := .historicized batch
        history := state.history ++ batch }
  | _ => state

/-- Acknowledge only a batch carrying its history receipt.  Since `pending`
only grows by appending while the batch is active, dropping the prepared
prefix retains every later arrival. -/
def acknowledge (state : State) : State :=
  match state.phase with
  | .historicized batch =>
      { state with
        pending := state.pending.drop batch.length
        phase := .idle
        acknowledged := state.acknowledged ++ batch }
  | _ => state

/-! ## Search stability and failure retention -/

theorem observe_idempotent (state : State) :
    observe (observe state) = observe state := by
  rcases state with ⟨pending, phase, history, acknowledged⟩
  cases phase <;> rfl

theorem repeated_observation_is_stable (state : State) :
    observedBatch (observe state) = observedBatch state := by
  rcases state with ⟨pending, phase, history, acknowledged⟩
  cases phase <;> rfl

theorem observe_does_not_consume (state : State) :
    (observe state).pending = state.pending := by
  rcases state with ⟨pending, phase, history, acknowledged⟩
  cases phase <;> rfl

theorem failure_preserves_pending (state : State) :
    (fail state).pending = state.pending := by
  rfl

theorem failure_preserves_observed_batch (state : State) :
    observedBatch (fail (observe state)) = observedBatch (observe state) := by
  rfl

theorem acknowledgement_without_history_is_stutter
    (state : State) (batch : List EventId)
    (phase : state.phase = .observed batch) :
    acknowledge state = state := by
  simp [acknowledge, phase]

/-! ## History-before-acknowledgement -/

theorem record_places_observed_batch_in_history
    (state : State) (batch : List EventId)
    (phase : state.phase = .observed batch) :
    (recordHistory state).history = state.history ++ batch ∧
      (recordHistory state).phase = .historicized batch := by
  simp [recordHistory, phase]

theorem settle_records_before_acknowledging
    (state : State) (batch : List EventId)
    (phase : state.phase = .observed batch) :
    let recorded := recordHistory state
    let settled := acknowledge recorded
    settled.history = state.history ++ batch ∧
      settled.acknowledged = state.acknowledged ++ batch := by
  simp [recordHistory, acknowledge, phase]

/-! ## Concurrent arrivals and restart recovery -/

theorem later_arrival_survives_settlement
    (state : State) (batch later : List EventId)
    (pending : state.pending = batch)
    (phase : state.phase = .observed batch) :
    let withLater := { state with pending := state.pending ++ later }
    (acknowledge (recordHistory withLater)).pending = later := by
  simp [recordHistory, acknowledge, phase, pending]

/-- The durable projection used at restart: accepted events minus exact
acknowledgement receipts. -/
def recover (accepted acknowledged : List EventId) : List EventId :=
  accepted.filter fun event => event ∉ acknowledged

theorem unacknowledged_event_is_recovered
    (accepted acknowledged : List EventId) (event : EventId)
    (present : event ∈ accepted) (unacknowledged : event ∉ acknowledged) :
    event ∈ recover accepted acknowledged := by
  simp [recover, present, unacknowledged]

theorem acknowledged_event_is_not_recovered
    (accepted acknowledged : List EventId) (event : EventId)
    (acknowledgedEvent : event ∈ acknowledged) :
    event ∉ recover accepted acknowledged := by
  simp [recover, acknowledgedEvent]

/-! ## Rejected destructive observation -/

def destructiveObserve (pending : List EventId) :
    List EventId × List EventId :=
  (pending, [])

/-- A destructive observation followed by abandoned search leaves the next
proof path with no event, despite there being neither history nor an
acknowledgement receipt. -/
theorem destructive_observation_admits_silent_loss :
    let first := destructiveObserve [41]
    first.1 = [41] ∧ first.2 = [] := by
  decide

end PettaClaw.InputDelivery

#print axioms PettaClaw.InputDelivery.observe_idempotent
#print axioms PettaClaw.InputDelivery.repeated_observation_is_stable
#print axioms PettaClaw.InputDelivery.failure_preserves_observed_batch
#print axioms PettaClaw.InputDelivery.acknowledgement_without_history_is_stutter
#print axioms PettaClaw.InputDelivery.settle_records_before_acknowledging
#print axioms PettaClaw.InputDelivery.later_arrival_survives_settlement
#print axioms PettaClaw.InputDelivery.unacknowledged_event_is_recovered
#print axioms PettaClaw.InputDelivery.destructive_observation_admits_silent_loss
