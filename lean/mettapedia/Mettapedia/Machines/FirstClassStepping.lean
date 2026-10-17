import Mettapedia.Machines.OutcomeRunner

/-!
# Retained advancement to declared observation boundaries

The next-boundary worker executes the actual transition function. It skips only
transitions explicitly marked silent, and stops at one publication, completion,
request, refusal or stuck state. A budget can interrupt the silent prefix; that
interruption is not completion. Publications keep their full ordered occurrence
list. Refusal additionally retains the actual source receiver.

Budgets count transitions of the selected machine profile. No law identifies
these counts with source-semantic events, another evaluator's ticks or native
work. A dialect adapter must justify its own observation boundaries. No scheduler
permutation or effect commutation is assumed.

Open descriptions are projections, not resumable values. The retained value is
indexed by the actual machine and initial state, and carries a checked source
execution invariant. Private Lean construction is not native unforgeability or
affine authority: host issuance, duplication policy, external effects and lifetime
remain the native capability contract's obligations. Recording is optional; the
unrecorded driver does not accumulate an event journal.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.FirstClassStepping

open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {State Event Verdict Request : Type}
variable {ControlView VerdictView RequestView : Type}

inductive Phase where
  | running | done | blocked | refused | stuck
  deriving DecidableEq, Repr

inductive Checkpoint (State Verdict Request : Type) where
  | ready (state : State)
  | done (verdict : Verdict)
  | blocked (request : Request) (saved : State)
  | refused (receiver : State)
  | stuck (state : State)
  deriving DecidableEq

namespace Checkpoint

def outcome : Checkpoint State Verdict Request → Outcome State Verdict Request
  | .ready state => .exhausted state
  | .done verdict => .finished verdict
  | .blocked request saved => .suspended request saved
  | .refused _ => .faulted
  | .stuck state => .stuck state

def phase : Checkpoint State Verdict Request → Phase
  | .ready _ => .running
  | .done _ => .done
  | .blocked _ _ => .blocked
  | .refused _ => .refused
  | .stuck _ => .stuck

def is_done (checkpoint : Checkpoint State Verdict Request) : Bool := checkpoint.phase == .done

theorem is_done_exact (checkpoint : Checkpoint State Verdict Request) :
    checkpoint.is_done = true ↔ ∃ verdict, checkpoint = .done verdict := by
  cases checkpoint <;> simp [is_done, phase]

end Checkpoint

/-- Only this request's newly published occurrences are retained. `used` is
profile-relative transition accounting, not a stable source-language clock. -/
structure Delivery (State Event Verdict Request : Type) where
  used : Nat
  events : List Event
  checkpoint : Checkpoint State Verdict Request
  deriving DecidableEq

/-- Execute silent control until the next declared observation boundary, or
retain the pending receiver when the supplied transition budget is exhausted. -/
def advance (machine : Machine State Event Verdict Request) :
    Nat → Checkpoint State Verdict Request → Delivery State Event Verdict Request
  | _, .done verdict => ⟨0, [], .done verdict⟩
  | _, .blocked request saved => ⟨0, [], .blocked request saved⟩
  | _, .refused receiver => ⟨0, [], .refused receiver⟩
  | _, .stuck state => ⟨0, [], .stuck state⟩
  | 0, .ready state => ⟨0, [], .ready state⟩
  | fuel + 1, .ready state =>
      match machine.step state with
      | none => ⟨1, [], .stuck state⟩
      | some (.silent next) =>
          let reply := advance machine fuel (.ready next)
          { reply with used := reply.used + 1 }
      | some (.publish events next) => ⟨1, events, .ready next⟩
      | some (.finish verdict) => ⟨1, [], .done verdict⟩
      | some (.call request saved) => ⟨1, [], .blocked request saved⟩
      | some (.fail events) => ⟨1, events, .refused state⟩

theorem advance_used_le (machine : Machine State Event Verdict Request) (fuel : Nat)
    (checkpoint : Checkpoint State Verdict Request) :
    (advance machine fuel checkpoint).used ≤ fuel := by
  induction fuel generalizing checkpoint with
  | zero => cases checkpoint <;> simp [advance]
  | succ fuel ih =>
      cases checkpoint <;> try simp [advance]
      rename_i state
      cases moved : machine.step state with
      | none => dsimp; omega
      | some transition =>
          cases transition <;> dsimp <;> first | exact Nat.succ_le_succ (ih _) | omega

/-- Every delivered boundary is an actual finite prefix of the original
machine, including its exact ordered publication list and terminal status. -/
theorem advance_prefix (machine : Machine State Event Verdict Request) (fuel : Nat)
    (checkpoint : Checkpoint State Verdict Request) :
    machine.continueRun (advance machine fuel checkpoint).used ([], checkpoint.outcome) =
      ((advance machine fuel checkpoint).events, (advance machine fuel checkpoint).checkpoint.outcome) := by
  induction fuel generalizing checkpoint with
  | zero => cases checkpoint <;> rfl
  | succ fuel ih =>
      cases checkpoint <;> try rfl
      rename_i state
      cases moved : machine.step state with
      | none => simp [advance, moved, Machine.continueRun, Machine.run, Checkpoint.outcome]
      | some transition =>
          cases transition with
          | silent next =>
              simpa only [advance, moved, Machine.continueRun, Checkpoint.outcome,
                List.nil_append, Machine.run] using ih (.ready next)
          | publish events next =>
              simp [advance, moved, Machine.continueRun, Machine.run, Checkpoint.outcome]
          | finish verdict =>
              simp [advance, moved, Machine.continueRun, Machine.run, Checkpoint.outcome]
          | call request saved =>
              simp [advance, moved, Machine.continueRun, Machine.run, Checkpoint.outcome]
          | fail events =>
              simp [advance, moved, Machine.continueRun, Machine.run, Checkpoint.outcome]

theorem actual_stuck_is_not_done (machine : Machine State Event Verdict Request) (state : State)
    (fuel : Nat) (stopped : machine.step state = none) :
    (advance machine (fuel + 1) (.ready state)).checkpoint = .stuck state ∧
      (advance machine (fuel + 1) (.ready state)).checkpoint.is_done = false := by
  simp [advance, stopped, Checkpoint.is_done, Checkpoint.phase]

theorem actual_refusal_is_not_stuck (machine : Machine State Event Verdict Request) (state : State)
    (events : List Event) (fuel : Nat) (failed : machine.step state = some (.fail events)) :
    (advance machine (fuel + 1) (.ready state)).checkpoint = .refused state ∧
      (advance machine (fuel + 1) (.ready state)).checkpoint.phase ≠ .stuck := by
  simp [advance, failed, Checkpoint.phase]

/-- Continuing with the unused transition allowance recovers the complete
original budget observation. Boundary discovery is not another evaluator. -/
theorem advance_remainder (machine : Machine State Event Verdict Request) (fuel : Nat)
    (checkpoint : Checkpoint State Verdict Request) :
    machine.continueRun fuel ([], checkpoint.outcome) =
      machine.continueRun (fuel - (advance machine fuel checkpoint).used)
        ((advance machine fuel checkpoint).events,
          (advance machine fuel checkpoint).checkpoint.outcome) := by
  have total := Nat.add_sub_of_le (advance_used_le machine fuel checkpoint)
  calc
    machine.continueRun fuel ([], checkpoint.outcome) =
        machine.continueRun ((advance machine fuel checkpoint).used +
          (fuel - (advance machine fuel checkpoint).used)) ([], checkpoint.outcome) := by rw [total]
    _ = _ := by rw [machine.continueRun_add, advance_prefix machine fuel checkpoint]

/-- An optional recorder, for observers that require the accumulated list.
The count bounds service requests; each request has its own transition budget. -/
def record (machine : Machine State Event Verdict Request) (fuel : Nat) :
    Nat → Checkpoint State Verdict Request → Delivery State Event Verdict Request
  | 0, checkpoint => ⟨0, [], checkpoint⟩
  | requests + 1, checkpoint =>
      let first := advance machine fuel checkpoint
      let later := record machine fuel requests first.checkpoint
      ⟨first.used + later.used, first.events ++ later.events, later.checkpoint⟩

/-- The ordinary retained driver discards delivered event lists after each
request. Required effects must remain in the source receiver or be observed. -/
def drive (machine : Machine State Event Verdict Request) (fuel : Nat) :
    Nat → Checkpoint State Verdict Request → Checkpoint State Verdict Request
  | 0, checkpoint => checkpoint
  | requests + 1, checkpoint => drive machine fuel requests (advance machine fuel checkpoint).checkpoint

theorem drive_eq_record (machine : Machine State Event Verdict Request) (fuel requests : Nat)
    (checkpoint : Checkpoint State Verdict Request) :
    drive machine fuel requests checkpoint = (record machine fuel requests checkpoint).checkpoint := by
  induction requests generalizing checkpoint with
  | zero => rfl
  | succ requests ih => simpa only [drive, record] using ih (advance machine fuel checkpoint).checkpoint

theorem drive_add (machine : Machine State Event Verdict Request) (fuel first later : Nat)
    (checkpoint : Checkpoint State Verdict Request) :
    drive machine fuel (first + later) checkpoint =
      drive machine fuel later (drive machine fuel first checkpoint) := by
  induction first generalizing checkpoint with
  | zero => simp [drive]
  | succ first ih => simpa only [Nat.succ_add, drive] using ih (advance machine fuel checkpoint).checkpoint

theorem record_prefix (machine : Machine State Event Verdict Request) (fuel requests : Nat)
    (checkpoint : Checkpoint State Verdict Request) :
    machine.continueRun (record machine fuel requests checkpoint).used ([], checkpoint.outcome) =
      ((record machine fuel requests checkpoint).events,
        (record machine fuel requests checkpoint).checkpoint.outcome) := by
  induction requests generalizing checkpoint with
  | zero => cases checkpoint <;> rfl
  | succ requests ih =>
      simp only [record]
      rw [machine.continueRun_add, advance_prefix]
      have prepend := machine.continueRun_prepend
        (record machine fuel requests (advance machine fuel checkpoint).checkpoint).used
        (advance machine fuel checkpoint).events ([], (advance machine fuel checkpoint).checkpoint.outcome)
      simp only [List.append_nil] at prepend
      rw [prepend]
      rw [ih]

/-- Unit allowance is an explicitly named reference mode. Its agreement with
one original transition is computed, not postulated as a semantic clock law. -/
theorem advance_unit_exact (machine : Machine State Event Verdict Request)
    (checkpoint : Checkpoint State Verdict Request) :
    ((advance machine 1 checkpoint).events, (advance machine 1 checkpoint).checkpoint.outcome) =
      machine.continueRun 1 ([], checkpoint.outcome) := by
  cases checkpoint <;> try rfl
  rename_i state
  cases moved : machine.step state with
  | none => simp [advance, moved, Machine.continueRun, Machine.run, Checkpoint.outcome]
  | some transition =>
      cases transition <;> simp [advance, moved, Machine.continueRun, Machine.run, Checkpoint.outcome]

/-- Every finite source budget has the same full ordered observations in the
reference allowance mode, including exhaustion, requests, faults and stuckness. -/
theorem record_unit_exact (machine : Machine State Event Verdict Request) (requests : Nat)
    (checkpoint : Checkpoint State Verdict Request) :
    ((record machine 1 requests checkpoint).events,
      (record machine 1 requests checkpoint).checkpoint.outcome) =
        machine.continueRun requests ([], checkpoint.outcome) := by
  induction requests generalizing checkpoint with
  | zero => simp [record]
  | succ requests ih =>
      let first := advance machine 1 checkpoint
      change (first.events ++ (record machine 1 requests first.checkpoint).events,
        (record machine 1 requests first.checkpoint).checkpoint.outcome) = _
      have later := congrArg (fun result : List Event × Outcome State Verdict Request =>
        (first.events ++ result.1, result.2)) (ih first.checkpoint)
      have prepend := machine.continueRun_prepend requests first.events ([], first.checkpoint.outcome)
      simp only [List.append_nil] at prepend
      calc
        _ = _ := later
        _ = machine.continueRun requests (first.events, first.checkpoint.outcome) := prepend.symm
        _ = machine.continueRun requests (machine.continueRun 1 ([], checkpoint.outcome)) := by
          rw [← advance_unit_exact]
        _ = _ := by rw [← machine.continueRun_add, Nat.add_comm 1 requests]

/-- Only actual continuing transitions connect source receivers. -/
def Progress (machine : Machine State Event Verdict Request) (before after : State) : Prop :=
  machine.step before = some (.silent after) ∨
    ∃ events, machine.step before = some (.publish events after)

/-- The original receiver path and actual terminal transition authenticate
even a refused receiver, which ordinary `Outcome.faulted` alone erases. -/
def ValidCheckpoint (machine : Machine State Event Verdict Request) (initial : State) :
    Checkpoint State Verdict Request → Prop
  | .ready state => Relation.ReflTransGen (Progress machine) initial state
  | .done verdict => ∃ state, Relation.ReflTransGen (Progress machine) initial state ∧
      machine.step state = some (.finish verdict)
  | .blocked request saved => ∃ state, Relation.ReflTransGen (Progress machine) initial state ∧
      machine.step state = some (.call request saved)
  | .refused state => Relation.ReflTransGen (Progress machine) initial state ∧
      ∃ events, machine.step state = some (.fail events)
  | .stuck state => Relation.ReflTransGen (Progress machine) initial state ∧ machine.step state = none

theorem advance_valid (machine : Machine State Event Verdict Request) (initial : State)
    (fuel : Nat) (checkpoint : Checkpoint State Verdict Request)
    (valid : ValidCheckpoint machine initial checkpoint) :
    ValidCheckpoint machine initial (advance machine fuel checkpoint).checkpoint := by
  induction fuel generalizing checkpoint with
  | zero => cases checkpoint <;> exact valid
  | succ fuel ih =>
      cases checkpoint with
      | done _ | blocked _ _ | refused _ | stuck _ => exact valid
      | ready state =>
          cases moved : machine.step state with
          | none => simp only [advance, moved]; exact ⟨valid, moved⟩
          | some transition =>
              cases transition with
              | silent next =>
                  simp only [advance, moved]
                  exact ih (.ready next) (.tail valid (Or.inl moved))
              | publish events next =>
                  simp only [advance, moved]
                  exact .tail valid (Or.inr ⟨events, moved⟩)
              | finish verdict =>
                  simp only [advance, moved]
                  exact ⟨state, valid, moved⟩
              | call request saved =>
                  simp only [advance, moved]
                  exact ⟨state, valid, moved⟩
              | fail events =>
                  simp only [advance, moved]
                  exact ⟨valid, events, moved⟩

theorem drive_valid (machine : Machine State Event Verdict Request) (initial : State)
    (fuel requests : Nat) (checkpoint : Checkpoint State Verdict Request)
    (valid : ValidCheckpoint machine initial checkpoint) :
    ValidCheckpoint machine initial (drive machine fuel requests checkpoint) := by
  induction requests generalizing checkpoint with
  | zero => exact valid
  | succ requests ih => exact ih _ (advance_valid machine initial fuel checkpoint valid)

structure Capability (machine : Machine State Event Verdict Request) (initial : State) where
  private mk ::
  checkpoint : Checkpoint State Verdict Request
  reached : ∃ fuel events, machine.run fuel initial = (events, checkpoint.outcome)
  valid : ValidCheckpoint machine initial checkpoint

namespace Capability

/-- Initial issuance is a host operation. Descriptions do not supply its input
authority; an implementation must enforce that boundary with native seals. -/
def begin (machine : Machine State Event Verdict Request) (initial : State) : Capability machine initial :=
  ⟨.ready initial, ⟨0, [], rfl⟩, .refl⟩

def resume {machine : Machine State Event Verdict Request} {initial : State}
    (capability : Capability machine initial) (fuel requests : Nat) : Capability machine initial :=
  ⟨drive machine fuel requests capability.checkpoint, by
    obtain ⟨paid, history, before⟩ := capability.reached
    let reply := record machine fuel requests capability.checkpoint
    refine ⟨paid + reply.used, history ++ reply.events, ?_⟩
    rw [machine.run_add, before]
    have prepend := machine.continueRun_prepend reply.used history ([], capability.checkpoint.outcome)
    simp only [List.append_nil] at prepend
    rw [prepend, record_prefix machine fuel requests capability.checkpoint]
    rw [drive_eq_record]
    , drive_valid machine initial fuel requests capability.checkpoint capability.valid⟩

theorem resume_checkpoint {machine : Machine State Event Verdict Request} {initial : State}
    (capability : Capability machine initial) (fuel requests : Nat) :
    (capability.resume fuel requests).checkpoint = drive machine fuel requests capability.checkpoint := rfl

theorem resume_add {machine : Machine State Event Verdict Request} {initial : State}
    (capability : Capability machine initial) (fuel first later : Nat) :
    ((capability.resume fuel first).resume fuel later).checkpoint =
      (capability.resume fuel (first + later)).checkpoint := by
  exact (drive_add machine fuel first later capability.checkpoint).symm

end Capability

/-- Open inspection deliberately lacks a transition function, private receiver
or authority to reconstruct a resumable value. Each field uses a chosen view. -/
structure Description (ControlView VerdictView RequestView : Type) where
  phase : Phase
  control : Option ControlView
  result : Option VerdictView
  request : Option RequestView
  deriving DecidableEq

def inspect (control : State → ControlView) (result : Verdict → VerdictView)
    (request : Request → RequestView) (checkpoint : Checkpoint State Verdict Request) :
    Description ControlView VerdictView RequestView :=
  match checkpoint with
  | .ready state => ⟨.running, some (control state), none, none⟩
  | .done value => ⟨.done, none, some (result value), none⟩
  | .blocked asked saved => ⟨.blocked, some (control saved), none, some (request asked)⟩
  | .refused state => ⟨.refused, some (control state), none, none⟩
  | .stuck state => ⟨.stuck, some (control state), none, none⟩

theorem inspect_phase (control : State → ControlView) (result : Verdict → VerdictView)
    (request : Request → RequestView) (checkpoint : Checkpoint State Verdict Request) :
    (inspect control result request checkpoint).phase = checkpoint.phase := by cases checkpoint <;> rfl

#print axioms Checkpoint.is_done_exact
#print axioms advance_used_le
#print axioms advance_prefix
#print axioms actual_stuck_is_not_done
#print axioms actual_refusal_is_not_stuck
#print axioms advance_remainder
#print axioms drive_eq_record
#print axioms drive_add
#print axioms record_prefix
#print axioms advance_unit_exact
#print axioms record_unit_exact
#print axioms advance_valid
#print axioms drive_valid
#print axioms Capability.resume_add

end Mettapedia.Machines.FirstClassStepping
