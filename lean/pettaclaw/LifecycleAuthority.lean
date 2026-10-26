import Mathlib

/-!
# Fail-closed lifecycle authority

The Telegram control plane may remain alive while cognition is stopped.  This
model isolates the authority rule outside the weak transformation kernel:
cognition is enabled exactly when the operator-owned durable latch reads
`running`.  The external deployment watcher observes health; it is not an
authority, so its observation neither grants nor revokes cognition.  (An
earlier revision also required an active watcher; the runtime has trusted the
latch alone since that requirement was removed.)

The latch is one durable record, replaced atomically: the new record is
written in full to a temporary file, synced, and renamed over the old one.  A
crash at any point therefore leaves either the old record or the new one.  A
record that is missing, unreadable, malformed or carries another state reads
as stopped, so an operator `stop` holds as soon as its rename has happened,
whatever the watcher reports.
-/

namespace PettaClaw.LifecycleAuthority

inductive Latch where
  | stopped
  | running
deriving Repr, DecidableEq

/-- The watcher's health observation is carried, but has no authority. -/
structure AuthorityState where
  latch : Latch
  watcherHealthy : Bool
deriving Repr, DecidableEq

def cognitionEnabled (state : AuthorityState) : Bool :=
  state.latch == .running

theorem enabled_iff_running (state : AuthorityState) :
    cognitionEnabled state = true ↔ state.latch = .running := by
  cases state with
  | mk latch watcher => cases latch <;> simp [cognitionEnabled]

theorem watcher_observation_has_no_authority
    (state : AuthorityState) (healthy : Bool) :
    cognitionEnabled { state with watcherHealthy := healthy } =
      cognitionEnabled state := by
  rfl

/-- The rule the runtime replaced: a running latch with an unhealthy watcher
is enabled, so watcher loss alone does not revoke cognition. -/
theorem latch_alone_authorizes :
    cognitionEnabled ⟨.running, false⟩ = true := by
  rfl

/-- What the durable file holds, as far as authority is concerned. -/
inductive LatchRecord where
  | valid (latch : Latch)
  /-- Missing, unreadable, malformed, another schema, another state or extra
  keys. -/
  | invalid
deriving Repr, DecidableEq

def readLatch : LatchRecord → Latch
  | .valid latch => latch
  | .invalid => .stopped

theorem invalid_record_reads_stopped : readLatch .invalid = .stopped := rfl

/-- Crash points of one atomic replacement. -/
inductive WriteCrashPoint where
  | beforeRename
  | afterRename
deriving Repr, DecidableEq

def recordAt (old : LatchRecord) (new : Latch) : WriteCrashPoint → LatchRecord
  | .beforeRename => old
  | .afterRename => .valid new

theorem every_write_crash_point_is_old_or_new
    (old : LatchRecord) (new : Latch) (point : WriteCrashPoint) :
    recordAt old new point = old ∨ recordAt old new point = .valid new := by
  cases point <;> simp [recordAt]

def stateAt (old : LatchRecord) (new : Latch) (point : WriteCrashPoint)
    (healthy : Bool) : AuthorityState :=
  ⟨readLatch (recordAt old new point), healthy⟩

theorem completed_stop_is_disabled (old : LatchRecord) (healthy : Bool) :
    cognitionEnabled (stateAt old .stopped .afterRename healthy) = false := by
  simp [stateAt, recordAt, readLatch, cognitionEnabled]

theorem completed_start_is_enabled (old : LatchRecord) (healthy : Bool) :
    cognitionEnabled (stateAt old .running .afterRename healthy) = true := by
  simp [stateAt, recordAt, readLatch, cognitionEnabled]

/-- A stop never enables cognition at any crash point: before its rename the
old record is unchanged, and after it the latch reads stopped. -/
theorem stop_never_grants (old : LatchRecord) (point : WriteCrashPoint)
    (healthy : Bool) (disabledBefore : cognitionEnabled ⟨readLatch old, healthy⟩ = false) :
    cognitionEnabled (stateAt old .stopped point healthy) = false := by
  cases point
  · simpa [stateAt, recordAt] using disabledBefore
  · exact completed_stop_is_disabled old healthy

/-- A start that crashed before its rename leaves cognition as it was. -/
theorem interrupted_start_changes_nothing (old : LatchRecord) (healthy : Bool) :
    stateAt old .running .beforeRename healthy = ⟨readLatch old, healthy⟩ := rfl

/-- An enabled action frontier stutters as soon as authority is absent. -/
def authorizedStep {State : Type} (transition : State → State)
    (authority : AuthorityState) (state : State) : State :=
  if cognitionEnabled authority then transition state else state

theorem unauthorized_step_stutters {State : Type}
    (transition : State → State) (authority : AuthorityState) (state : State)
    (disabled : cognitionEnabled authority = false) :
    authorizedStep transition authority state = state := by
  simp [authorizedStep, disabled]

#print axioms PettaClaw.LifecycleAuthority.enabled_iff_running
#print axioms PettaClaw.LifecycleAuthority.watcher_observation_has_no_authority
#print axioms PettaClaw.LifecycleAuthority.latch_alone_authorizes
#print axioms PettaClaw.LifecycleAuthority.every_write_crash_point_is_old_or_new
#print axioms PettaClaw.LifecycleAuthority.completed_stop_is_disabled
#print axioms PettaClaw.LifecycleAuthority.completed_start_is_enabled
#print axioms PettaClaw.LifecycleAuthority.stop_never_grants
#print axioms PettaClaw.LifecycleAuthority.interrupted_start_changes_nothing
#print axioms PettaClaw.LifecycleAuthority.unauthorized_step_stutters

end PettaClaw.LifecycleAuthority
