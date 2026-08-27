import Mathlib

/-!
# Fail-closed lifecycle authority

The Telegram control plane may remain alive while cognition is stopped.  This
model isolates the authority rule outside the weak transformation kernel:
cognition is enabled exactly when an operator-owned durable latch is running
and the external deployment watcher is active.

The transition order matters.  `stop` revokes the latch before stopping the
watcher; `start` keeps the latch stopped until the watcher has been observed
active.  Consequently every crash prefix of either operation is fail-closed.
-/

namespace PettaClaw.LifecycleAuthority

inductive Latch where
  | stopped
  | running
deriving Repr, DecidableEq

structure AuthorityState where
  latch : Latch
  watcherActive : Bool
deriving Repr, DecidableEq

def cognitionEnabled (state : AuthorityState) : Bool :=
  state.latch == .running && state.watcherActive

theorem enabled_iff_running_and_watched (state : AuthorityState) :
    cognitionEnabled state = true ↔
      state.latch = .running ∧ state.watcherActive = true := by
  cases state with
  | mk latch watcher =>
      cases latch <;> cases watcher <;> simp [cognitionEnabled]

def stopBegin (state : AuthorityState) : AuthorityState :=
  { state with latch := .stopped }

def stopWatcher (state : AuthorityState) : AuthorityState :=
  { state with watcherActive := false }

inductive StopCrashPoint where
  | beforeRevocation
  | afterRevocation
  | afterWatcherStop
deriving Repr, DecidableEq

def stoppedAt (initial : AuthorityState) : StopCrashPoint → AuthorityState
  | .beforeRevocation => initial
  | .afterRevocation => stopBegin initial
  | .afterWatcherStop => stopWatcher (stopBegin initial)

theorem every_post_revocation_stop_prefix_is_disabled
    (initial : AuthorityState) (point : StopCrashPoint)
    (revoked : point ≠ .beforeRevocation) :
    cognitionEnabled (stoppedAt initial point) = false := by
  cases point <;> simp_all [stoppedAt, stopBegin, stopWatcher,
    cognitionEnabled]

def startBegin (state : AuthorityState) : AuthorityState :=
  { state with latch := .stopped }

def startWatcher (state : AuthorityState) : AuthorityState :=
  { state with watcherActive := true }

def grant (state : AuthorityState) : AuthorityState :=
  if state.watcherActive then { state with latch := .running }
  else { state with latch := .stopped }

inductive StartCrashPoint where
  | afterRevocation
  | afterWatcherStart
  | afterGrant
deriving Repr, DecidableEq

def startedAt (initial : AuthorityState) : StartCrashPoint → AuthorityState
  | .afterRevocation => startBegin initial
  | .afterWatcherStart => startWatcher (startBegin initial)
  | .afterGrant => grant (startWatcher (startBegin initial))

theorem every_pre_grant_start_prefix_is_disabled
    (initial : AuthorityState) (point : StartCrashPoint)
    (notGranted : point ≠ .afterGrant) :
    cognitionEnabled (startedAt initial point) = false := by
  cases point <;> simp_all [startedAt, startBegin, startWatcher,
    cognitionEnabled]

theorem completed_start_is_enabled (initial : AuthorityState) :
    cognitionEnabled (startedAt initial .afterGrant) = true := by
  simp [startedAt, startBegin, startWatcher, grant, cognitionEnabled]

theorem watcher_loss_revokes_without_latch_rewrite :
    cognitionEnabled ⟨.running, false⟩ = false := by
  rfl

/-- An enabled action frontier stutters as soon as authority is absent. -/
def authorizedStep {State : Type} (transition : State → State)
    (authority : AuthorityState) (state : State) : State :=
  if cognitionEnabled authority then transition state else state

theorem unauthorized_step_stutters {State : Type}
    (transition : State → State) (authority : AuthorityState) (state : State)
    (disabled : cognitionEnabled authority = false) :
    authorizedStep transition authority state = state := by
  simp [authorizedStep, disabled]

#print axioms PettaClaw.LifecycleAuthority.enabled_iff_running_and_watched
#print axioms PettaClaw.LifecycleAuthority.every_post_revocation_stop_prefix_is_disabled
#print axioms PettaClaw.LifecycleAuthority.every_pre_grant_start_prefix_is_disabled
#print axioms PettaClaw.LifecycleAuthority.completed_start_is_enabled
#print axioms PettaClaw.LifecycleAuthority.watcher_loss_revokes_without_latch_rewrite
#print axioms PettaClaw.LifecycleAuthority.unauthorized_step_stutters

end PettaClaw.LifecycleAuthority
