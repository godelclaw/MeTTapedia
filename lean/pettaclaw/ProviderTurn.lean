import Mathlib

/-!
# ProviderTurn — one external request per cognitive turn

This model isolates the provider boundary of an autonomous agent loop.  A
slow or unavailable model must not cause one cognitive turn to launch a hidden
sequence of replacement requests.  Failure changes retry pacing, while the
agent's energy and working identity remain coordinates of the life loop.

The correspondence to the PeTTa runtime is intentionally small:

* `attempts` counts calls to the external model provider;
* `energy` is the loop's remaining autonomous turn budget;
* `sleepInterval` is idle pacing between turns; and
* `working` stands for the present-moment state restored across process
  boundaries.

Streaming is an implementation detail below this transition: partial chunks
are collected by the provider adapter, and only `.answered` or `.failed`
crosses the cognitive boundary.
-/

namespace PettaClaw.ProviderTurn

def fullEnergy : Nat := 50

structure State (Working : Type*) where
  working : Working
  energy : Nat
  sleepInterval : Nat
  attempts : Nat
deriving Repr, DecidableEq

inductive Outcome where
  | answered
  | failed (retryAfter : Nat)
deriving Repr, DecidableEq

def retryPacing (retryAfter : Nat) : Nat := max 1 retryAfter

/-- One cognitive turn makes exactly one provider call.  Success restores the
ordinary pacing; failure installs a bounded retry pace.  Neither outcome owns
the agent's energy coordinate. -/
def runOne (normalSleep : Nat) (state : State Working) :
    Outcome → State Working
  | .answered =>
      { state with
        sleepInterval := normalSleep
        attempts := state.attempts + 1 }
  | .failed retryAfter =>
      { state with
        sleepInterval := retryPacing retryAfter
        attempts := state.attempts + 1 }

theorem runOne_exactly_one_request (normalSleep : Nat)
    (state : State Working) (outcome : Outcome) :
    (runOne normalSleep state outcome).attempts = state.attempts + 1 := by
  cases outcome <;> rfl

theorem runOne_preserves_energy (normalSleep : Nat)
    (state : State Working) (outcome : Outcome) :
    (runOne normalSleep state outcome).energy = state.energy := by
  cases outcome <;> rfl

theorem runOne_preserves_working_self (normalSleep : Nat)
    (state : State Working) (outcome : Outcome) :
    (runOne normalSleep state outcome).working = state.working := by
  cases outcome <;> rfl

theorem failure_uses_positive_pacing (normalSleep retryAfter : Nat)
    (state : State Working) :
    0 < (runOne normalSleep state (.failed retryAfter)).sleepInterval := by
  simp [runOne, retryPacing]

theorem answer_clears_old_backoff (normalSleep : Nat)
    (state : State Working) :
    (runOne normalSleep state .answered).sleepInterval = normalSleep := by
  rfl

/-! ## The hidden-retry separation -/

def OneRequestPerTurn
    (transition : State Working → Outcome → State Working) : Prop :=
  ∀ state outcome,
    (transition state outcome).attempts = state.attempts + 1

theorem runOne_has_one_request_per_turn (normalSleep : Nat) :
    OneRequestPerTurn (runOne normalSleep :
      State Working → Outcome → State Working) := by
  intro state outcome
  exact runOne_exactly_one_request normalSleep state outcome

/-- The historical adapter behavior: `retries` replacement calls occur after
the initial call, all within the same cognitive turn. -/
def hiddenRetries (retries : Nat) (state : State Working) : State Working :=
  { state with attempts := state.attempts + (retries + 1) }

theorem six_retries_means_seven_requests (state : State Working) :
    (hiddenRetries 6 state).attempts = state.attempts + 7 := by
  simp [hiddenRetries]

theorem six_hidden_retries_violates_one_request :
    ¬ OneRequestPerTurn
        (fun state (_ : Outcome) => hiddenRetries 6 state :
          State Unit → Outcome → State Unit) := by
  intro claimed
  have impossible := claimed
    ({ working := (), energy := 7, sleepInterval := 1, attempts := 0 } :
      State Unit) .answered
  simp [hiddenRetries] at impossible

/-! ## Life remains outside provider failure -/

/-- An authenticated operator message wakes the loop and may add energy, but
never removes energy already held. -/
def operatorWake (normalSleep tier : Nat) (state : State Working) :
    State Working :=
  { state with
    energy := max state.energy tier
    sleepInterval := normalSleep }

theorem operator_wake_never_drains (normalSleep tier : Nat)
    (state : State Working) :
    state.energy ≤ (operatorWake normalSleep tier state).energy := by
  exact Nat.le_max_left _ _

theorem positive_operator_wake_recovers_zero_energy
    (normalSleep tier : Nat) (state : State Working) (positive : 0 < tier) :
    0 < (operatorWake normalSleep tier { state with energy := 0 }).energy := by
  simp [operatorWake, positive]

/-- The autonomous heartbeat is independent of provider success and restores a
full breath without consulting provider retry state. -/
def heartbeat (state : State Working) : State Working :=
  { state with energy := fullEnergy }

theorem provider_failure_cannot_block_heartbeat
    (normalSleep retryAfter : Nat) (state : State Working) :
    (heartbeat (runOne normalSleep state (.failed retryAfter))).energy =
      fullEnergy := by
  rfl

/-- A tempting failure handler that writes zero into the energy coordinate is
observably not a pacing-only transition. -/
def failureKillsEnergy (retryAfter : Nat) (state : State Working) :
    State Working :=
  { state with energy := 0, sleepInterval := retryPacing retryAfter }

theorem failure_kill_is_not_energy_preserving :
    let state : State Unit :=
      { working := (), energy := 7, sleepInterval := 1, attempts := 0 }
    (failureKillsEnergy 15 state).energy ≠ state.energy := by
  decide

end PettaClaw.ProviderTurn

#print axioms PettaClaw.ProviderTurn.runOne_exactly_one_request
#print axioms PettaClaw.ProviderTurn.runOne_preserves_energy
#print axioms PettaClaw.ProviderTurn.runOne_preserves_working_self
#print axioms PettaClaw.ProviderTurn.failure_uses_positive_pacing
#print axioms PettaClaw.ProviderTurn.runOne_has_one_request_per_turn
#print axioms PettaClaw.ProviderTurn.six_hidden_retries_violates_one_request
#print axioms PettaClaw.ProviderTurn.operator_wake_never_drains
#print axioms PettaClaw.ProviderTurn.provider_failure_cannot_block_heartbeat
#print axioms PettaClaw.ProviderTurn.failure_kill_is_not_energy_preserving
