import ObservedStrategy

/-!
# Non-authoritative runtime observations

A bounded context keeps the distinctions needed to interpret provider,
settlement, channel, memory, budget and background observations. Diagnostic
counters may be omitted. An observation is neither a completion witness nor
permission to execute an effect. The host supplies faithful measurements and
the encoding correspondence; these laws do not verify the native runtime.
-/

namespace RuntimeObservation

inductive CallPhase
  | unknown | idle | waiting | backoff | failed | returned
deriving Repr, DecidableEq

structure Call where
  phase : CallPhase := .unknown
  ageSeconds : Option Nat := none
  retrySeconds : Option Nat := none
deriving Repr, DecidableEq

structure Memory where
  documents : Nat
  behind : Nat
  threshold : Nat
deriving Repr, DecidableEq

structure Budget where
  attemptsHour : Nat
  accountedOutputToday : Nat
  requestsHourLimit : Nat
  outputDayLimit : Nat
deriving Repr, DecidableEq

structure Background where
  pending : Nat
  review : Nat
  uncertain : Nat
  oldestReviewSeconds : Option Nat := none
deriving Repr, DecidableEq

structure Inbox where
  pending : Nat
  newestAgeSeconds : Option Nat := none
  oldestAgeSeconds : Option Nat := none
deriving Repr, DecidableEq

structure Commands where
  returned : Nat
  withheld : Nat
  deferred : Nat
  uncertain : Nat
  failed : Nat
deriving Repr, DecidableEq

structure Facts where
  call : Call := {}
  turnPending : Option Bool := none
  channelReady : Option Bool := none
  memory : Option Memory := none
  budget : Option Budget := none
  background : Option Background := none
  inbox : Option Inbox := none
  commands : Option Commands := none
deriving Repr, DecidableEq

structure Reading where
  facts : Facts
  diagnosticCounters : List Nat := []
deriving Repr, DecidableEq

def compact (reading : Reading) : Facts := reading.facts

inductive Query
  | provider | settlement | channel | index | resources | strands | humanInput | receipts
deriving Repr, DecidableEq

inductive Answer
  | provider (call : Call)
  | settlement (pending : Option Bool)
  | channel (ready : Option Bool)
  | index (memory : Option Memory)
  | resources (budget : Option Budget)
  | strands (jobs : Option Background)
  | humanInput (inbox : Option Inbox)
  | receipts (commands : Option Commands)
deriving Repr, DecidableEq

def answer (facts : Facts) : Query → Answer
  | .provider => .provider facts.call
  | .settlement => .settlement facts.turnPending
  | .channel => .channel facts.channelReady
  | .index => .index facts.memory
  | .resources => .resources facts.budget
  | .strands => .strands facts.background
  | .humanInput => .humanInput facts.inbox
  | .receipts => .receipts facts.commands

theorem compact_preserves_query (reading : Reading) (query : Query) :
    answer (compact reading) query = answer reading.facts query := by rfl

theorem diagnostic_changes_preserve_view (facts : Facts) (left right : List Nat) :
    compact ⟨facts, left⟩ = compact ⟨facts, right⟩ := by rfl

theorem provider_return_preserves_pending_turn (facts : Facts) :
    ({ facts with call := ⟨.returned, none, none⟩ } : Facts).turnPending =
      facts.turnPending := by rfl

theorem provider_failure_preserves_pending_turn (facts : Facts) :
    ({ facts with call := ⟨.failed, none, none⟩ } : Facts).turnPending =
      facts.turnPending := by rfl

theorem input_observation_does_not_answer_input (facts : Facts) (inbox : Option Inbox) :
    ({ facts with inbox := inbox } : Facts).turnPending = facts.turnPending := by rfl

theorem returned_receipt_is_not_settlement (facts : Facts) (commands : Commands) :
    ({ facts with commands := some commands } : Facts).turnPending =
      facts.turnPending := by rfl

theorem unavailable_inbox_is_not_empty (facts : Facts) :
    answer { facts with inbox := none } .humanInput ≠
      answer { facts with inbox := some ⟨0, none, none⟩ } .humanInput := by
  simp [answer]

def channelUnavailable (facts : Facts) : Bool := facts.channelReady.isNone

def channelAlert (facts : Facts) : Bool := facts.channelReady == some false

def channelHealthy (facts : Facts) : Bool := facts.channelReady == some true

theorem unknown_channel_is_unavailable (facts : Facts) :
    channelUnavailable { facts with channelReady := none } = true := by rfl

theorem unknown_channel_is_not_healthy (facts : Facts) :
    channelHealthy { facts with channelReady := none } = false := by rfl

theorem failed_channel_is_alert (facts : Facts) :
    channelAlert { facts with channelReady := some false } = true := by rfl

theorem channel_intervention_changes_answer (facts : Facts) :
    answer { facts with channelReady := some true } .channel ≠
      answer { facts with channelReady := some false } .channel := by
  simp [answer]

theorem channel_intervention_preserves_provider (facts : Facts) :
    answer { facts with channelReady := some true } .provider =
      answer { facts with channelReady := some false } .provider := by rfl

structure State where
  core : ObservedStrategy.State
  view : Facts

def refresh (state : State) (reading : Reading) : State :=
  { state with view := compact reading }

theorem refresh_preserves_core (state : State) (reading : Reading) :
    (refresh state reading).core = state.core := by rfl

theorem refresh_preserves_requests (state : State) (reading : Reading) :
    (refresh state reading).core.requests = state.core.requests := by rfl

theorem refresh_preserves_authority (state : State) (reading : Reading) :
    (refresh state reading).core.router = state.core.router := by rfl

theorem refresh_preserves_pending_decision (state : State) (reading : Reading) :
    (refresh state reading).core.pending = state.core.pending := by rfl

theorem refresh_cannot_dispatch (state : State) (reading : Reading) :
    (refresh state reading).core.dispatch = state.core.dispatch := by rfl

theorem refresh_preserves_allowance (state : State) (reading : Reading) :
    (refresh state reading).core.allowance = state.core.allowance := by rfl

def refreshMany (state : State) (readings : List Reading) : State :=
  readings.foldl refresh state

theorem arbitrary_observations_preserve_core (state : State) (readings : List Reading) :
    (refreshMany state readings).core = state.core := by
  induction readings generalizing state with
  | nil => rfl
  | cons reading rest ih =>
      simpa [refreshMany, List.foldl_cons, refresh] using ih (refresh state reading)

end RuntimeObservation
