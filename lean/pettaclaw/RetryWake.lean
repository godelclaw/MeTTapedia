import FuelPolicy

/-!
The retry incident is a composition of three individually small mistakes:

* a terminal request can retain an active native-call lease;
* already-presented input can interrupt the retry delay for that same input;
* each presentation, rather than each input occurrence, advances maintenance.

This executable state model exhibits the resulting no-progress run and proves
the corresponding repairs.  Runtime regression tests exercise the same
boundaries against the Python/MeTTa implementation.
-/

namespace RetryWake

inductive RequestState
  | pending | completed | failed | unknown
deriving DecidableEq, Repr

inductive CallState
  | absent | claimed | submitted | completed | failed | uncertain
deriving DecidableEq, Repr

def RequestState.terminal : RequestState → Bool
  | .pending => false
  | _ => true

def CallState.active : CallState → Bool
  | .claimed | .submitted => true
  | _ => false

/-- Reconcile the two durable rows sharing a request identity. -/
def reconcile : RequestState → CallState → CallState
  | .completed, .claimed | .completed, .submitted => .completed
  | .failed, .claimed => .failed
  | .failed, .submitted => .uncertain
  | .unknown, .claimed | .unknown, .submitted => .uncertain
  | _, call => call

/-- A terminal request never retains admission authority after repair. -/
theorem failedRequestHasNoActiveNativeCall
    (request : RequestState) (call : CallState)
    (terminal : request.terminal = true) :
    (reconcile request call).active = false := by
  cases request <;> cases call <;> simp_all [RequestState.terminal,
    CallState.active, reconcile]

/-- The exact contradictory pair observed in the live ledger is admitted by
the old representation. -/
example : RequestState.failed.terminal = true ∧
    CallState.submitted.active = true := by decide

/-- Reconciliation changes that pair to honest uncertainty. -/
example : reconcile .failed .submitted = .uncertain := rfl

structure LegacyState where
  now : Nat
  retryAt : Nat
  inputPending : Bool
  requestFailed : Bool
  callSubmitted : Bool
  attempts : Nat
  maintenance : Nat
  semanticProgress : Nat
deriving DecidableEq, Repr

/-- The old channel wake treats retained pending input as fresh even before
its own retry deadline.  The attempt fails locally and the fake wake advances
maintenance, while neither time nor semantic progress advances. -/
def legacyStep (state : LegacyState) : LegacyState :=
  if state.inputPending && state.requestFailed && state.callSubmitted &&
      state.now < state.retryAt then
    { state with attempts := state.attempts + 1
                 maintenance := state.maintenance + 1 }
  else state

def observedBadState : LegacyState where
  now := 0
  retryAt := 15
  inputPending := true
  requestFailed := true
  callSubmitted := true
  attempts := 0
  maintenance := 0
  semanticProgress := 0

def run {α : Type} (step : α → α) : Nat → α → α
  | 0, state => state
  | n + 1, state => step (run step n state)

def stormState (n : Nat) : LegacyState :=
  { observedBadState with attempts := n, maintenance := n }

/-- The architecture admits arbitrarily many attempts and maintenance passes
with no time or semantic progress.  This is an existence result, not a claim
that every execution diverges. -/
theorem legacyStormExists (n : Nat) :
    run legacyStep n observedBadState = stormState n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change legacyStep (run legacyStep n observedBadState) =
        stormState (n + 1)
      rw [ih]
      simp [legacyStep, stormState, observedBadState]

structure RetryFrontier where
  now : Nat
  retryAt : Nat
  presented : Nat
  live : Nat
deriving DecidableEq, Repr

/-- The permissive repaired policy allows the deadline or genuinely newer
input to admit a new attempt. -/
def frontierMayAttempt (state : RetryFrontier) : Bool :=
  decide (state.retryAt ≤ state.now ∨ state.presented < state.live)

/-- The production repair is the stricter refinement: a provider deadline is
not bypassed by input.  Independent control commands remain available. -/
def strictMayAttempt (state : RetryFrontier) : Bool :=
  decide (state.retryAt ≤ state.now)

theorem sameInputCannotPreemptOwnRetry (state : RetryFrontier)
    (same : state.live = state.presented)
    (early : state.now < state.retryAt) :
    frontierMayAttempt state = false := by
  simp [frontierMayAttempt, same, early]

theorem newInputCanInterruptPermissiveRetry (state : RetryFrontier)
    (newer : state.presented < state.live) :
    frontierMayAttempt state = true := by
  simp [frontierMayAttempt, newer]

theorem strictBackoffCannotAttemptEarly (state : RetryFrontier)
    (early : state.now < state.retryAt) :
    strictMayAttempt state = false := by
  simp [strictMayAttempt, early]

theorem strictBackoffRefinesFrontierPolicy (state : RetryFrontier)
    (strict : strictMayAttempt state = true) :
    frontierMayAttempt state = true := by
  simp [strictMayAttempt] at strict
  simp [frontierMayAttempt, strict]

structure WakeState where
  lastWake : Option Nat
  maintenance : Nat
  semanticProgress : Nat
deriving DecidableEq, Repr

def maintain (token : Nat) (state : WakeState) : WakeState :=
  if state.lastWake = some token then state
  else { state with lastWake := some token
                    maintenance := state.maintenance + 1 }

theorem maintenanceRunsOncePerWakeToken (token : Nat) (state : WakeState) :
    maintain token (maintain token state) = maintain token state := by
  by_cases same : state.lastWake = some token <;>
    simp [maintain, same]

theorem maintenanceDoesNotClaimSemanticProgress
    (token : Nat) (state : WakeState) :
    (maintain token state).semanticProgress = state.semanticProgress := by
  by_cases same : state.lastWake = some token <;>
    simp [maintain, same]

structure ProgressState where
  heartbeats : Nat
  semanticCommits : Nat
deriving DecidableEq, Repr

def heartbeat (state : ProgressState) : ProgressState :=
  { state with heartbeats := state.heartbeats + 1 }

def semanticCommit (state : ProgressState) : ProgressState :=
  { state with semanticCommits := state.semanticCommits + 1 }

theorem heartbeatDoesNotImplySemanticProgress (state : ProgressState) :
    (heartbeat state).semanticCommits = state.semanticCommits := rfl

def renderFuel : FuelPolicy.Fuel → Nat → String
  | .unlimited, _ => "FUEL: unlimited"
  | _, remaining => s!"LOOPS_LEFT: {remaining}"

theorem unlimitedFuelNeverRendersFiniteLoops :
    renderFuel .unlimited 50 = "FUEL: unlimited" := rfl

#print axioms failedRequestHasNoActiveNativeCall
#print axioms legacyStormExists
#print axioms sameInputCannotPreemptOwnRetry
#print axioms maintenanceRunsOncePerWakeToken
#print axioms heartbeatDoesNotImplySemanticProgress
#print axioms unlimitedFuelNeverRendersFiniteLoops

end RetryWake
