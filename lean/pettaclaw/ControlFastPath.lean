import Mathlib

/-!
# Queue-independent operator observations

Read-only operator controls observe a supplied runtime view immediately. They
do not enter either the cognitive queue or the serialized authority-mutation
queue. Mutations retain ordering; observations retain freshness.

The deployment watcher is represented by a bounded receipt. A receipt older
than its lease cannot authorize cognition even if the durable latch still says
`running`.
-/

namespace PettaClaw.ControlFastPath

inductive Command where
  | activity
  | mode
  | modes
  | engine
  | engines
  | setMode
  | setEngine
  | start
  | stop
  | wake
deriving Repr, DecidableEq

def isFastRead : Command → Bool
  | .activity | .mode | .modes | .engine | .engines => true
  | .setMode | .setEngine | .start | .stop | .wake => false

def isImmediateAuthority : Command → Bool
  | .start | .stop | .wake => true
  | _ => false

structure RuntimeView where
  activity : String
  mode : String
  engine : String
deriving Repr, DecidableEq

structure QueueDepths where
  cognition : Nat
  mutations : Nat
deriving Repr, DecidableEq

structure Snapshot where
  observedAt : Nat
  view : RuntimeView
deriving Repr, DecidableEq

inductive Dispatch where
  | reply (snapshot : Snapshot)
  | immediateAuthority
  | enqueueMutation
deriving Repr, DecidableEq

def dispatch (command : Command) (receivedAt : Nat) (view : RuntimeView)
    (_queues : QueueDepths) : Dispatch :=
  if isImmediateAuthority command then .immediateAuthority
  else if isFastRead command then .reply ⟨receivedAt, view⟩
  else .enqueueMutation

theorem fast_read_is_not_immediate (command : Command)
    (fast : isFastRead command = true) :
    isImmediateAuthority command = false := by
  cases command <;> simp_all [isFastRead, isImmediateAuthority]

theorem fast_read_snapshots_receipt_state
    (command : Command) (receivedAt : Nat) (view : RuntimeView)
    (queues : QueueDepths) (fast : isFastRead command = true) :
    dispatch command receivedAt view queues =
      .reply ⟨receivedAt, view⟩ := by
  simp [dispatch, fast, fast_read_is_not_immediate command fast]

theorem fast_read_independent_of_all_backlogs
    (command : Command) (receivedAt : Nat) (view : RuntimeView)
    (left right : QueueDepths) (fast : isFastRead command = true) :
    dispatch command receivedAt view left =
      dispatch command receivedAt view right := by
  simp [dispatch, fast]

theorem known_operator_observations_are_fast :
    [Command.activity, .mode, .modes, .engine, .engines].all isFastRead =
      true := by
  decide

theorem authority_mutations_are_not_fast_reads :
    [Command.setMode, .setEngine, .start, .stop, .wake].all
      (fun command => !isFastRead command) = true := by
  decide

theorem lifecycle_controls_are_immediate :
    [Command.start, .stop, .wake].all isImmediateAuthority = true := by
  decide

theorem ordinary_mutations_are_not_immediate :
    [Command.setMode, .setEngine].all
      (fun command => !isImmediateAuthority command) = true := by
  decide

inductive Latch where
  | stopped
  | running
deriving Repr, DecidableEq

structure WatchReceipt where
  observedAt : Nat
  exactCandidate : Bool
  active : Bool
  problemFree : Bool
deriving Repr, DecidableEq

def leaseFresh (now lease : Nat) (receipt : WatchReceipt) : Prop :=
  receipt.observedAt ≤ now ∧ now - receipt.observedAt ≤ lease

def watchAuthorizes (now lease : Nat) (receipt : WatchReceipt) : Prop :=
  leaseFresh now lease receipt ∧ receipt.exactCandidate = true ∧
    receipt.active = true ∧ receipt.problemFree = true

def cognitionEnabled (latch : Latch) (now lease : Nat)
    (receipt : WatchReceipt) : Prop :=
  latch = .running ∧ watchAuthorizes now lease receipt

theorem expired_receipt_cannot_authorize
    (latch : Latch) (now lease : Nat) (receipt : WatchReceipt)
    (expired : lease < now - receipt.observedAt) :
    ¬cognitionEnabled latch now lease receipt := by
  intro enabled
  exact (Nat.not_le_of_lt expired) enabled.2.1.2

theorem stopped_latch_cannot_authorize
    (now lease : Nat) (receipt : WatchReceipt) :
    ¬cognitionEnabled .stopped now lease receipt := by
  simp [cognitionEnabled]

structure TransitionState where
  epoch : Nat
  latch : Latch
deriving Repr, DecidableEq

def beginTransition (state : TransitionState) : TransitionState :=
  ⟨state.epoch + 1, .stopped⟩

def completeStart (token : Nat) (state : TransitionState) : TransitionState :=
  if token = state.epoch then { state with latch := .running } else state

theorem newer_stop_cancels_slow_start (initial : TransitionState) :
    let starting := beginTransition initial
    let stopped := beginTransition starting
    completeStart starting.epoch stopped = stopped := by
  simp [beginTransition, completeStart]

theorem cancelled_start_cannot_reauthorize (initial : TransitionState) :
    let starting := beginTransition initial
    let stopped := beginTransition starting
    (completeStart starting.epoch stopped).latch = .stopped := by
  simp [beginTransition, completeStart]

#print axioms PettaClaw.ControlFastPath.fast_read_snapshots_receipt_state
#print axioms PettaClaw.ControlFastPath.fast_read_independent_of_all_backlogs
#print axioms PettaClaw.ControlFastPath.known_operator_observations_are_fast
#print axioms PettaClaw.ControlFastPath.authority_mutations_are_not_fast_reads
#print axioms PettaClaw.ControlFastPath.lifecycle_controls_are_immediate
#print axioms PettaClaw.ControlFastPath.ordinary_mutations_are_not_immediate
#print axioms PettaClaw.ControlFastPath.expired_receipt_cannot_authorize
#print axioms PettaClaw.ControlFastPath.stopped_latch_cannot_authorize
#print axioms PettaClaw.ControlFastPath.newer_stop_cancels_slow_start
#print axioms PettaClaw.ControlFastPath.cancelled_start_cannot_reauthorize

end PettaClaw.ControlFastPath
