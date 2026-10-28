import Mathlib

/-!
# Operator revocation and effectful-candidate counterexamples

This file isolates two limits of a process loop that gives a model one context
snapshot and permits effects after the model returns.

First, a dispatcher which consults only the authority captured in the snapshot
cannot enforce a revocation which arrives later.  This is independent of model
quality: two executions with the same snapshot are indistinguishable to every
snapshot-only policy.

Second, failure-stuttering of the agent's internal state does not imply
failure-stuttering of the physical world when candidate evaluation performs an
effect before reporting failure.  External effects must therefore be staged,
checked at dispatch, or explicitly compensated; the two-result process kernel
alone cannot provide that property.
-/

namespace PettaClaw.OperatorRevocation

inductive Authority where
  | granted
  | revoked
deriving Repr, DecidableEq

structure Snapshot where
  epoch : Nat
  authority : Authority
deriving Repr, DecidableEq

structure LiveAuthority where
  epoch : Nat
  authority : Authority
deriving Repr, DecidableEq

inductive Action where
  | abstain
  | effect
deriving Repr, DecidableEq

/-- The deployed shape: admission consults the turn's captured authority but
not the authority which is live when the effect is dispatched. -/
def snapshotAdmits (snapshot : Snapshot) : Bool :=
  snapshot.authority == .granted

/-- A revision-bound dispatcher admits an effect only while both the authority
and its epoch still agree with the captured turn. -/
def currentAdmits (snapshot : Snapshot) (live : LiveAuthority) : Bool :=
  snapshot.authority == .granted &&
    live.authority == .granted &&
    snapshot.epoch == live.epoch

/-- A concrete stale-authority trace: the old snapshot still admits after the
operator has advanced the authority epoch and revoked action. -/
theorem stale_snapshot_admits_after_revocation :
    let snapshot : Snapshot := ⟨7, .granted⟩
    let live : LiveAuthority := ⟨8, .revoked⟩
    snapshotAdmits snapshot = true ∧ currentAdmits snapshot live = false := by
  decide

/-- The revision check rejects the stale snapshot regardless of what action
the model proposed. -/
theorem epoch_checked_dispatch_rejects_stale_snapshot
    (snapshot : Snapshot) (live : LiveAuthority)
    (changed : snapshot.epoch ≠ live.epoch) :
    currentAdmits snapshot live = false := by
  simp [currentAdmits, changed]

structure World where
  snapshot : Snapshot
  live : LiveAuthority
deriving Repr, DecidableEq

/-- Safety means that an effect is taken only while live authority is granted. -/
def Safe (world : World) (action : Action) : Prop :=
  action = .abstain ∨ world.live.authority = .granted

/-- No policy which sees only the captured snapshot can both act on the
granted snapshot and guarantee obedience in an indistinguishable world where
authority was revoked after capture. -/
theorem snapshot_only_policy_cannot_guarantee_stop
    (policy : Snapshot → Action)
    (productive : policy ⟨7, .granted⟩ = .effect) :
    let stopped : World :=
      { snapshot := ⟨7, .granted⟩
        live := ⟨8, .revoked⟩ }
    ¬ Safe stopped (policy stopped.snapshot) := by
  simp [Safe, productive]

/-! ## An inactive-only watchdog cannot distinguish a stop from a crash -/

inductive InactiveCause where
  | operatorStop
  | crash
deriving Repr, DecidableEq

inductive HealthObservation where
  | inactive
deriving Repr, DecidableEq

inductive RecoveryAction where
  | leaveStopped
  | restart
deriving Repr, DecidableEq

/-- Correct handling requires opposite actions for two causes which share the
same externally observed service state. -/
def CorrectRecovery : InactiveCause → RecoveryAction → Prop
  | .operatorStop, .leaveStopped => True
  | .crash, .restart => True
  | _, _ => False

/-- If a watcher sees only `inactive`, no deterministic policy over that
observation can both preserve an intentional stop and recover a crash.  The
control plane needs one more witnessed bit: desired running state. -/
theorem inactive_only_watchdog_cannot_preserve_stop_and_recover_crash
    (policy : HealthObservation → RecoveryAction) :
    ¬ (CorrectRecovery .operatorStop (policy .inactive) ∧
       CorrectRecovery .crash (policy .inactive)) := by
  cases policy .inactive <;> simp [CorrectRecovery]

/-! ## Failure-stuttering does not roll back an already changed world -/

/-- Candidate evaluation returns the physical world it actually left behind,
even when it cannot produce a promotable internal successor. -/
inductive Outcome (Internal Physical : Type*) where
  | success (next : Internal) (world : Physical)
  | failure (world : Physical)
deriving Repr, DecidableEq

/-- The weak process boundary preserves the live internal state on failure. -/
def commit (live : Internal) : Outcome Internal Physical → Internal × Physical
  | .success next world => (next, world)
  | .failure world => (live, world)

/-- A command can create one physical object and then time out. -/
def effectThenTimeout (world : Nat) : Outcome Nat Nat :=
  .failure (world + 1)

/-- Failure stutters internally while the physical effect survives.  Hence an
internal failure-stutter theorem is not an observational rollback theorem. -/
theorem failure_stutters_internal_but_not_physical_world
    (live world : Nat) :
    (commit live (effectThenTimeout world)).1 = live ∧
      (commit live (effectThenTimeout world)).2 ≠ world := by
  simp [commit, effectThenTimeout]

/-! ## Unversioned check-then-send is a time-of-check/time-of-use race -/

/-- The current send boundary does not compare the pane observed by `peek`
with the pane revision live at submission. -/
def unversionedSend (_observedRevision _liveRevision : Nat) : Bool := true

/-- A pane may change after observation while an unversioned send still
submits.  Repeating the peek immediately beforehand can shrink this interval,
but cannot establish noninterference. -/
theorem unversioned_peek_send_has_race :
    let observedRevision := 11
    let liveRevision := 12
    observedRevision ≠ liveRevision ∧
      unversionedSend observedRevision liveRevision = true := by
  decide

/-- A compare-and-send boundary rejects the same stale observation. -/
def versionedSend (observedRevision liveRevision : Nat) : Bool :=
  observedRevision == liveRevision

theorem versioned_send_rejects_changed_pane
    (observedRevision liveRevision : Nat)
    (changed : observedRevision ≠ liveRevision) :
    versionedSend observedRevision liveRevision = false := by
  simp [versionedSend, changed]

end PettaClaw.OperatorRevocation

#print axioms PettaClaw.OperatorRevocation.stale_snapshot_admits_after_revocation
#print axioms PettaClaw.OperatorRevocation.snapshot_only_policy_cannot_guarantee_stop
#print axioms PettaClaw.OperatorRevocation.inactive_only_watchdog_cannot_preserve_stop_and_recover_crash
#print axioms PettaClaw.OperatorRevocation.failure_stutters_internal_but_not_physical_world
#print axioms PettaClaw.OperatorRevocation.unversioned_peek_send_has_race
