import Mettapedia.Machines.ErrorBoundaryContracts.Supervision
import Mettapedia.GSLT.Core.AtomicSnapshotTransaction
import Mettapedia.Logic.GovernanceReasoning.TreatyKernel

/-!
# Task and attempt identity at a supervision boundary

The core supervisor consumes already-admitted completion events. This wrapper
binds each reply to a stable task identifier and a durable generation, incremented
only when a new reservation grants an attempt. Delayed, duplicated, and misrouted
replies cannot affect a later generation or another task. Restart preserves the
generation and core uncertainty handling remains authoritative.

The identifiers establish correlation, not authentication. Task identifiers must
not be recycled with reset generations while old replies may remain in flight.
Generation persistence, unbounded mathematical counters, and atomic transitions
are modeled; storage durability, bounded-counter rollover, concurrent dispatch,
and physical exactly-once execution are separate implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ErrorBoundaryContracts.AttemptIdentity

open RunContracts.ScopedOutcome

universe u v w
variable {α : Type u} {ε : Type v} {Id : Type w}

structure State (Id : Type w) (α : Type u) (ε : Type v) where
  owner : Id
  generation : Nat
  task : Supervision.Task α ε
  deriving DecidableEq, Repr

inductive Control where
  | reserve
  | restart
  | abandonUncertain
  | acknowledge
  | idle
  deriving DecidableEq, Repr

def Control.core : Control → Supervision.Event α ε
  | .reserve => .reserve
  | .restart => .restart
  | .abandonUncertain => .abandonUncertain
  | .acknowledge => .acknowledge
  | .idle => .idle

inductive ReplyKind where
  | complete
  | reconcile
  deriving DecidableEq, Repr

structure Reply (Id : Type w) (α : Type u) (ε : Type v) where
  owner : Id
  generation : Nat
  kind : ReplyKind
  outcome : Outcome α ε
  retryAuthorized : Bool
  deriving DecidableEq, Repr

def Reply.core (reply : Reply Id α ε) : Supervision.Event α ε :=
  match reply.kind with
  | .complete => .complete reply.outcome reply.retryAuthorized
  | .reconcile => .reconcile reply.outcome reply.retryAuthorized

inductive Event (Id : Type w) (α : Type u) (ε : Type v) where
  | control (request : Control)
  | reply (message : Reply Id α ε)
  deriving DecidableEq, Repr

def charge (state : State Id α ε) : Event Id α ε → Nat
  | .control request => Supervision.charge state.task request.core
  | .reply _ => 0

def step [DecidableEq Id] (state : State Id α ε) : Event Id α ε → State Id α ε
  | .control request =>
      ⟨state.owner,
        state.generation + Supervision.charge state.task request.core,
        Supervision.step state.task request.core⟩
  | .reply message =>
      if message.owner = state.owner ∧ message.generation = state.generation then
        { state with task := Supervision.step state.task message.core }
      else state

def run [DecidableEq Id] (state : State Id α ε) : List (Event Id α ε) → State Id α ε
  | [] => state
  | event :: rest => run (step state event) rest

def charges [DecidableEq Id] (state : State Id α ε) : List (Event Id α ε) → Nat
  | [] => 0
  | event :: rest => charge state event + charges (step state event) rest

theorem stale_reply_noop [DecidableEq Id] (state : State Id α ε)
    (message : Reply Id α ε) (stale : message.generation ≠ state.generation) :
    step state (.reply message) = state := by
  simp [step, stale]

theorem wrong_task_reply_noop [DecidableEq Id] (state : State Id α ε)
    (message : Reply Id α ε) (wrongTask : message.owner ≠ state.owner) :
    step state (.reply message) = state := by
  simp [step, wrongTask]

/-- Correlation admits an event; the core phase check can still reject it. -/
theorem matching_reply_refines_core [DecidableEq Id] (state : State Id α ε)
    (message : Reply Id α ε) (sameTask : message.owner = state.owner)
    (sameAttempt : message.generation = state.generation) :
    step state (.reply message) =
      { state with task := Supervision.step state.task message.core } := by
  simp [step, sameTask, sameAttempt]

theorem step_owner [DecidableEq Id] (state : State Id α ε) (event : Event Id α ε) :
    (step state event).owner = state.owner := by
  cases event with
  | control request => rfl
  | reply message => simp only [step]; split <;> rfl

theorem step_generation [DecidableEq Id] (state : State Id α ε) (event : Event Id α ε) :
    (step state event).generation = state.generation + charge state event := by
  cases event with
  | control request => rfl
  | reply message => simp only [step, charge, Nat.add_zero]; split <;> rfl

theorem run_owner [DecidableEq Id] (state : State Id α ε) (events : List (Event Id α ε)) :
    (run state events).owner = state.owner := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih => simp only [run, ih, step_owner]

theorem run_generation [DecidableEq Id] (state : State Id α ε) (events : List (Event Id α ε)) :
    (run state events).generation = state.generation + charges state events := by
  induction events generalizing state with
  | nil => simp [run, charges]
  | cons event rest ih => simp [run, charges, ih, step_generation, Nat.add_assoc]

theorem generation_monotone [DecidableEq Id] (state : State Id α ε)
    (events : List (Event Id α ε)) :
    state.generation ≤ (run state events).generation := by
  rw [run_generation]
  omega

theorem restart_keeps_generation [DecidableEq Id] (state : State Id α ε) :
    (step state (.control .restart)).generation = state.generation := by
  simp [step, Control.core, Supervision.charge]

/-- The wrapper preserves the core's exact permit budget even for rejected replies. -/
theorem step_permit_accounting [DecidableEq Id] (state : State Id α ε)
    (event : Event Id α ε) :
    (step state event).task.remaining + charge state event = state.task.remaining := by
  cases event with
  | control request => exact Supervision.step_accounting state.task request.core
  | reply message =>
      simp only [step, charge, Nat.add_zero]
      split
      · have core := Supervision.step_accounting state.task message.core
        cases kindEq : message.kind <;>
          simpa [Reply.core, kindEq, Supervision.charge] using core
      · rfl

theorem run_permit_accounting [DecidableEq Id] (state : State Id α ε)
    (events : List (Event Id α ε)) :
    (run state events).task.remaining + charges state events = state.task.remaining := by
  induction events generalizing state with
  | nil => simp [run, charges]
  | cons event rest ih =>
      have next := ih (step state event)
      have one := step_permit_accounting state event
      simp only [run, charges]
      omega

/-- Generations can advance only as often as the durable permit budget allows. -/
theorem generation_budget [DecidableEq Id] (state : State Id α ε)
    (events : List (Event Id α ε)) :
    (run state events).generation ≤ state.generation + state.task.remaining := by
  rw [run_generation]
  have h := run_permit_accounting state events
  omega

/-! ## Delayed and misrouted reply controls -/

def testInitial : State Nat Nat String := ⟨7, 0, Supervision.initial 2⟩

def attemptTwo : State Nat Nat String :=
  run testInitial
    [.control .reserve, .reply ⟨7, 1, .complete, .raised "retryable", true⟩,
      .control .reserve]

theorem second_attempt_has_new_generation :
    attemptTwo = ⟨7, 2, ⟨0, .active, false⟩⟩ := rfl

theorem old_reply_does_not_settle_new_attempt :
    step attemptTwo (.reply ⟨7, 1, .complete, .value 42, false⟩) = attemptTwo := by decide

theorem current_reply_settles_new_attempt :
    (step attemptTwo (.reply ⟨7, 2, .complete, .value 9, false⟩)).task.phase =
      .terminal (.completed (.value 9)) := by decide

theorem another_task_reply_does_not_settle :
    step attemptTwo (.reply ⟨8, 2, .complete, .value 42, false⟩) = attemptTwo := by decide

/-- The unwrapped core demonstrates the bug that task/attempt correlation prevents. -/
theorem uncorrelated_old_reply_would_settle :
    (Supervision.step attemptTwo.task (.complete (.value 42) false)).phase =
      .terminal (.completed (.value 42)) := rfl

/-- Resetting both identity and generation makes an old reply current again (ABA).
A durable task incarnation or never-reset generation is therefore necessary. -/
theorem recycled_identity_accepts_old_reply :
    (step (step testInitial (.control .reserve))
      (.reply ⟨7, 1, .complete, .value 42, false⟩)).task.phase =
      .terminal (.completed (.value 42)) := by decide

/-- Correlation alone does not turn an uncertain operation into a completed one. -/
theorem ordinary_reply_after_restart_waits_for_reconciliation :
    step (step attemptTwo (.control .restart))
      (.reply ⟨7, 2, .complete, .value 9, false⟩) =
      step attemptTwo (.control .restart) := by decide

theorem current_reconciliation_settles_uncertainty :
    (step (step attemptTwo (.control .restart))
      (.reply ⟨7, 2, .reconcile, .value 9, false⟩)).task.phase =
      .terminal (.completed (.value 9)) := by decide

/-! ## Durable duties over supervised attempts

Permission remains discardable. An issued duty instead occupies one stable
ledger position until an authorized disposition is recorded there. Transfers
change its current holder, not its obligor, obligee, scope or occurrence.

The current grant list is a service input; its authentication and currency are
separate implementation obligations. A disposition records the exact grant
snapshot used at its adoption boundary. Replies still use the existing
supervisor's admitted-outcome boundary: correlation alone is not evidence of a
real external effect. The concrete service adapter supplies that evidence.
-/

namespace DurableDuty

variable {Party Scope Answer Fault : Type}

inductive Purpose where
  | primary | repair
  deriving DecidableEq, Repr

inductive Right where
  | issue | hold | transfer | execute | adopt | compensate
  deriving DecidableEq, Repr

def Purpose.dispositionRight : Purpose → Right
  | .primary => .adopt
  | .repair => .compensate

structure Grant (Party Scope : Type) where
  principal : Party
  scope : Scope
  right : Right
  deriving DecidableEq, Repr

def allowed [DecidableEq Party] [DecidableEq Scope]
    (grants : List (Grant Party Scope)) (principal : Party) (scope : Scope) (right : Right) : Bool :=
  decide (⟨principal, scope, right⟩ ∈ grants)

structure Descriptor (Party Scope : Type) where
  occurrence : Nat
  obligor : Party
  obligee : Party
  scope : Scope
  deriving DecidableEq, Repr

/-- The existing treaty clause supplies the bilateral parties and scope;
runtime allocation supplies the independent physical occurrence. -/
def Descriptor.fromClause {Entity Pred Time : Type} (occurrence : Nat)
    (clause : Mettapedia.Logic.GovernanceReasoning.TreatyKernel.TreatyClause
      Scope Entity Pred Time Party) : Descriptor Party Scope :=
  ⟨occurrence, clause.obligor, clause.obligee, clause.id⟩

structure Transfer (Party Scope : Type) where
  actor : Party
  recipient : Party
  authority : List (Grant Party Scope)
  deriving DecidableEq, Repr

structure Disposition (Party Scope Answer : Type) where
  actor : Party
  purpose : Purpose
  generation : Nat
  answer : Answer
  authority : List (Grant Party Scope)
  deriving DecidableEq, Repr

structure Row (Party Scope Answer Fault : Type) where
  origin : Descriptor Party Scope
  holder : Party
  primary : AttemptIdentity.State (Nat × Purpose) Answer Fault
  repair : AttemptIdentity.State (Nat × Purpose) Answer Fault
  transfers : List (Transfer Party Scope)
  disposition : Option (Disposition Party Scope Answer)
  cancelled : Bool
  deriving DecidableEq, Repr

def Row.task (row : Row Party Scope Answer Fault) :
    Purpose → AttemptIdentity.State (Nat × Purpose) Answer Fault
  | .primary => row.primary
  | .repair => row.repair

def Row.withTask (row : Row Party Scope Answer Fault) (purpose : Purpose)
    (task : AttemptIdentity.State (Nat × Purpose) Answer Fault) : Row Party Scope Answer Fault :=
  match purpose with
  | .primary => { row with primary := task }
  | .repair => { row with repair := task }

def Row.issued (origin : Descriptor Party Scope) (primaryBudget repairBudget : Nat) :
    Row Party Scope Answer Fault :=
  ⟨origin, origin.obligor,
    ⟨(origin.occurrence, .primary), 0, Supervision.initial primaryBudget⟩,
    ⟨(origin.occurrence, .repair), 0, Supervision.initial repairBudget⟩, [], none, false⟩

/-- A chain records actual handovers, including the giver's permission and
the recipient's acceptance. It does not identify either party with the
immutable original obligor. -/
inductive Ownership [DecidableEq Party] [DecidableEq Scope] (origin : Descriptor Party Scope) :
    List (Transfer Party Scope) → Party → Prop
  | issued : Ownership origin [] origin.obligor
  | transfer {history : List (Transfer Party Scope)} {holder : Party}
      (previous : Ownership origin history holder) (receipt : Transfer Party Scope)
      (actor : receipt.actor = holder)
      (gives : allowed receipt.authority receipt.actor origin.scope .transfer = true)
      (accepts : allowed receipt.authority receipt.recipient origin.scope .hold = true) :
      Ownership origin (history ++ [receipt]) receipt.recipient

abbrev Meaning (Party Scope Answer : Type) := Descriptor Party Scope → Purpose → Answer → Bool

def Row.AuthorizedDisposition [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (row : Row Party Scope Answer Fault)
    (receipt : Disposition Party Scope Answer) : Prop :=
  receipt.actor = row.holder ∧
    allowed receipt.authority receipt.actor row.origin.scope receipt.purpose.dispositionRight = true ∧
    (row.task receipt.purpose).generation = receipt.generation ∧
    (row.task receipt.purpose).task.phase = .terminal (.completed (.value receipt.answer)) ∧
    meaning row.origin receipt.purpose receipt.answer = true

def Row.Lawful [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (row : Row Party Scope Answer Fault) : Prop :=
  row.primary.owner = (row.origin.occurrence, .primary) ∧
    row.repair.owner = (row.origin.occurrence, .repair) ∧
    Ownership row.origin row.transfers row.holder ∧
    ∀ receipt, row.disposition = some receipt → row.AuthorizedDisposition meaning receipt

def Row.transfer [DecidableEq Party] [DecidableEq Scope]
    (grants : List (Grant Party Scope)) (actor recipient : Party)
    (row : Row Party Scope Answer Fault) : Row Party Scope Answer Fault :=
  if row.disposition.isNone ∧ actor = row.holder ∧
      allowed grants actor row.origin.scope .transfer = true ∧
      allowed grants recipient row.origin.scope .hold = true then
    { row with holder := recipient, transfers := row.transfers ++ [⟨actor, recipient, grants⟩] }
  else row

/-- Only a newly permitted reservation consumes an execution permit. Admitted
historical completion/reconciliation events may still be persisted after
revocation. Acknowledgement belongs to authorized adoption below. -/
def Row.supervise [DecidableEq Party] [DecidableEq Scope]
    (grants : List (Grant Party Scope)) (actor : Party) (purpose : Purpose)
    (event : AttemptIdentity.Event (Nat × Purpose) Answer Fault)
    (row : Row Party Scope Answer Fault) : Row Party Scope Answer Fault :=
  if row.disposition.isSome then row else
    match event with
    | .control .acknowledge => row
    | .control .reserve =>
        if actor = row.holder ∧ allowed grants actor row.origin.scope .execute = true then
          row.withTask purpose (AttemptIdentity.step (row.task purpose) event)
        else row
    | _ => row.withTask purpose (AttemptIdentity.step (row.task purpose) event)

/-- Adoption is separate from completion persistence. It requires current
authority and the declared result meaning, and atomically records the
disposition with the existing supervisor acknowledgement. -/
def Row.settle [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (grants : List (Grant Party Scope))
    (actor : Party) (purpose : Purpose) (row : Row Party Scope Answer Fault) :
    Row Party Scope Answer Fault :=
  if row.disposition.isSome then row else
    match (row.task purpose).task.phase with
    | .terminal (.completed (.value answer)) =>
        if actor = row.holder ∧
            allowed grants actor row.origin.scope purpose.dispositionRight = true ∧
            meaning row.origin purpose answer = true then
          { row.withTask purpose
              (AttemptIdentity.step (row.task purpose) (.control .acknowledge)) with
            disposition := some ⟨actor, purpose, (row.task purpose).generation, answer, grants⟩ }
        else row
    | _ => row

inductive Action (Party Scope Answer Fault : Type) where
  | issue (obligee : Party) (scope : Scope) (primaryBudget repairBudget : Nat)
  | supervise (occurrence : Nat) (purpose : Purpose)
      (event : AttemptIdentity.Event (Nat × Purpose) Answer Fault)
  | transfer (occurrence : Nat) (recipient : Party)
  | cancel (occurrence : Nat)
  | settle (occurrence : Nat) (purpose : Purpose)
  deriving DecidableEq, Repr

structure Ledger (Party Scope Answer Fault : Type) where
  issued : List (Descriptor Party Scope)
  rows : List (Row Party Scope Answer Fault)
  deriving DecidableEq, Repr

def initial : Ledger Party Scope Answer Fault := ⟨[], []⟩

def update (occurrence : Nat) (action : Row Party Scope Answer Fault → Row Party Scope Answer Fault)
    (ledger : Ledger Party Scope Answer Fault) : Ledger Party Scope Answer Fault :=
  { ledger with rows := ledger.rows.map fun row =>
      if row.origin.occurrence = occurrence then action row else row }

def step [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (grants : List (Grant Party Scope)) (actor : Party)
    (ledger : Ledger Party Scope Answer Fault) :
    Action Party Scope Answer Fault → Ledger Party Scope Answer Fault
  | .issue obligee scope primaryBudget repairBudget =>
      if allowed grants actor scope .issue ∧ allowed grants actor scope .hold then
        let origin := Descriptor.mk ledger.issued.length actor obligee scope
        ⟨ledger.issued ++ [origin], ledger.rows ++ [Row.issued origin primaryBudget repairBudget]⟩
      else ledger
  | .supervise occurrence purpose event =>
      update occurrence (Row.supervise grants actor purpose event) ledger
  | .transfer occurrence recipient => update occurrence (Row.transfer grants actor recipient) ledger
  | .cancel occurrence => update occurrence (fun row => { row with cancelled := true }) ledger
  | .settle occurrence purpose => update occurrence (Row.settle meaning grants actor purpose) ledger

abbrev Request (Party Scope Answer Fault : Type) :=
  List (Grant Party Scope) × Party × Action Party Scope Answer Fault

def run [DecidableEq Party] [DecidableEq Scope] (meaning : Meaning Party Scope Answer)
    (ledger : Ledger Party Scope Answer Fault) : List (Request Party Scope Answer Fault) →
    Ledger Party Scope Answer Fault
  | [] => ledger
  | (grants, actor, action) :: rest => run meaning (step meaning grants actor ledger action) rest

@[simp] theorem Row.withTask_origin (row : Row Party Scope Answer Fault) (purpose : Purpose)
    (task : AttemptIdentity.State (Nat × Purpose) Answer Fault) :
    (row.withTask purpose task).origin = row.origin := by cases purpose <;> rfl

@[simp] theorem Row.withTask_holder (row : Row Party Scope Answer Fault) (purpose : Purpose)
    (task : AttemptIdentity.State (Nat × Purpose) Answer Fault) :
    (row.withTask purpose task).holder = row.holder := by cases purpose <;> rfl

@[simp] theorem Row.withTask_transfers (row : Row Party Scope Answer Fault) (purpose : Purpose)
    (task : AttemptIdentity.State (Nat × Purpose) Answer Fault) :
    (row.withTask purpose task).transfers = row.transfers := by cases purpose <;> rfl

@[simp] theorem Row.withTask_disposition (row : Row Party Scope Answer Fault) (purpose : Purpose)
    (task : AttemptIdentity.State (Nat × Purpose) Answer Fault) :
    (row.withTask purpose task).disposition = row.disposition := by cases purpose <;> rfl

@[simp] theorem Row.task_withTask (row : Row Party Scope Answer Fault) (purpose : Purpose)
    (task : AttemptIdentity.State (Nat × Purpose) Answer Fault) :
    (row.withTask purpose task).task purpose = task := by cases purpose <;> rfl

theorem Row.issued_lawful [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (origin : Descriptor Party Scope)
    (primaryBudget repairBudget : Nat) :
    (Row.issued (Fault := Fault) origin primaryBudget repairBudget).Lawful meaning :=
  ⟨rfl, rfl, Ownership.issued, by simp [Row.issued]⟩

theorem Row.withTask_lawful_pending [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (row : Row Party Scope Answer Fault)
    (lawful : row.Lawful meaning) (pending : row.disposition = none) (purpose : Purpose)
    (next : AttemptIdentity.State (Nat × Purpose) Answer Fault)
    (owner : next.owner = (row.origin.occurrence, purpose)) :
    (row.withTask purpose next).Lawful meaning := by
  obtain ⟨primary, repair, ownership, _⟩ := lawful
  cases purpose with
  | primary => exact ⟨owner, repair, ownership, by simp [Row.withTask, pending]⟩
  | repair => exact ⟨primary, owner, ownership, by simp [Row.withTask, pending]⟩

theorem Row.transfer_lawful [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (grants : List (Grant Party Scope))
    (actor recipient : Party) (row : Row Party Scope Answer Fault) (lawful : row.Lawful meaning) :
    (row.transfer grants actor recipient).Lawful meaning := by
  unfold Row.transfer
  split
  · rename_i accepted
    obtain ⟨pending, actorIsHolder, gives, accepts⟩ := accepted
    have empty : row.disposition = none := Option.isNone_iff_eq_none.mp pending
    exact ⟨lawful.1, lawful.2.1,
      Ownership.transfer lawful.2.2.1 ⟨actor, recipient, grants⟩ actorIsHolder gives accepts,
      by simp [empty]⟩
  · exact lawful

theorem Row.supervise_lawful [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (grants : List (Grant Party Scope))
    (actor : Party) (purpose : Purpose)
    (event : AttemptIdentity.Event (Nat × Purpose) Answer Fault)
    (row : Row Party Scope Answer Fault) (lawful : row.Lawful meaning) :
    (row.supervise grants actor purpose event).Lawful meaning := by
  cases pending : row.disposition with
  | some receipt => simpa [Row.supervise, pending] using lawful
  | none =>
      have owner : (row.task purpose).owner = (row.origin.occurrence, purpose) := by
        cases purpose
        · exact lawful.1
        · exact lawful.2.1
      have moved := row.withTask_lawful_pending meaning lawful pending purpose
        (AttemptIdentity.step (row.task purpose) event)
        ((AttemptIdentity.step_owner _ _).trans owner)
      cases event with
      | reply message => simpa [Row.supervise, pending] using moved
      | control request =>
          cases request <;> simp only [Row.supervise, pending, Option.isSome_none,
            Bool.false_eq_true, ↓reduceIte]
          · split
            · exact moved
            · exact lawful
          · exact moved
          · exact moved
          · exact lawful
          · exact moved

theorem Row.settle_lawful [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (grants : List (Grant Party Scope))
    (actor : Party) (purpose : Purpose) (row : Row Party Scope Answer Fault)
    (lawful : row.Lawful meaning) :
    (row.settle meaning grants actor purpose).Lawful meaning := by
  cases pending : row.disposition with
  | some receipt => simpa [Row.settle, pending] using lawful
  | none =>
      have owner : (row.task purpose).owner = (row.origin.occurrence, purpose) := by
        cases purpose
        · exact lawful.1
        · exact lawful.2.1
      have moved := row.withTask_lawful_pending meaning lawful pending purpose
        (AttemptIdentity.step (row.task purpose) (.control .acknowledge))
        ((AttemptIdentity.step_owner _ _).trans owner)
      cases phase : (row.task purpose).task.phase with
      | ready => simpa [Row.settle, pending, phase] using lawful
      | active => simpa [Row.settle, pending, phase] using lawful
      | uncertain => simpa [Row.settle, pending, phase] using lawful
      | terminal receipt =>
          cases receipt with
          | unresolved => simpa [Row.settle, pending, phase] using lawful
          | completed outcome =>
              cases outcome with
              | raised fault => simpa [Row.settle, pending, phase] using lawful
              | value answer =>
                  simp only [Row.settle, pending, Option.isSome_none, Bool.false_eq_true,
                    ↓reduceIte, phase]
                  split
                  · rename_i accepted
                    obtain ⟨actorIsHolder, permits, interprets⟩ := accepted
                    refine ⟨moved.1, moved.2.1, moved.2.2.1, ?_⟩
                    intro actual same
                    cases Option.some.inj same
                    change actor = (row.withTask purpose _).holder ∧
                      allowed grants actor (row.withTask purpose _).origin.scope purpose.dispositionRight = true ∧
                      ((row.withTask purpose _).task purpose).generation = (row.task purpose).generation ∧
                      ((row.withTask purpose _).task purpose).task.phase =
                        .terminal (.completed (.value answer)) ∧
                      meaning (row.withTask purpose _).origin purpose answer = true
                    simp only [Row.withTask_holder, Row.withTask_origin, Row.task_withTask]
                    refine ⟨actorIsHolder, permits, ?_, ?_, interprets⟩
                    · simp [AttemptIdentity.step, Control.core, Supervision.charge]
                    · simp [AttemptIdentity.step, Control.core, Supervision.step, Supervision.terminal, phase]
                  · exact lawful

theorem Row.transfer_origin [DecidableEq Party] [DecidableEq Scope]
    (grants : List (Grant Party Scope)) (actor recipient : Party) (row : Row Party Scope Answer Fault) :
    (row.transfer grants actor recipient).origin = row.origin := by
  unfold Row.transfer
  split <;> rfl

theorem Row.supervise_origin [DecidableEq Party] [DecidableEq Scope]
    (grants : List (Grant Party Scope)) (actor : Party) (purpose : Purpose)
    (event : AttemptIdentity.Event (Nat × Purpose) Answer Fault) (row : Row Party Scope Answer Fault) :
    (row.supervise grants actor purpose event).origin = row.origin := by
  unfold Row.supervise
  split
  · rfl
  · cases event with
    | reply message => exact Row.withTask_origin _ _ _
    | control request =>
        cases request with
        | reserve =>
            dsimp only
            split
            · exact Row.withTask_origin _ _ _
            · rfl
        | restart => exact Row.withTask_origin _ _ _
        | abandonUncertain => exact Row.withTask_origin _ _ _
        | acknowledge => rfl
        | idle => exact Row.withTask_origin _ _ _

theorem Row.settle_origin [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (grants : List (Grant Party Scope))
    (actor : Party) (purpose : Purpose) (row : Row Party Scope Answer Fault) :
    (row.settle meaning grants actor purpose).origin = row.origin := by
  unfold Row.settle
  split
  · rfl
  · split
    · split
      · exact Row.withTask_origin _ _ _
      · rfl
    · rfl

def Lawful [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (ledger : Ledger Party Scope Answer Fault) : Prop :=
  ledger.rows.map Row.origin = ledger.issued ∧
    ledger.issued.map Descriptor.occurrence = List.range ledger.issued.length ∧
    ∀ row ∈ ledger.rows, row.Lawful meaning

theorem initial_lawful [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) : Lawful meaning (initial (Fault := Fault)) := by
  exact ⟨rfl, rfl, by simp [initial]⟩

theorem update_lawful [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (occurrence : Nat)
    (action : Row Party Scope Answer Fault → Row Party Scope Answer Fault)
    (origin : ∀ row, (action row).origin = row.origin)
    (preserves : ∀ row, row.Lawful meaning → (action row).Lawful meaning)
    (ledger : Ledger Party Scope Answer Fault) (lawful : Lawful meaning ledger) :
    Lawful meaning (update occurrence action ledger) := by
  refine ⟨?_, lawful.2.1, ?_⟩
  · change (ledger.rows.map _).map Row.origin = ledger.issued
    rw [List.map_map]
    convert lawful.1 using 1
    apply List.map_congr_left
    intro row _
    dsimp only [Function.comp_apply]
    split
    · exact origin row
    · rfl
  · intro after present
    change after ∈ ledger.rows.map
      (fun row => if row.origin.occurrence = occurrence then action row else row) at present
    obtain ⟨before, beforeMem, same⟩ := List.mem_map.mp present
    subst after
    split
    · exact preserves before (lawful.2.2 before beforeMem)
    · exact lawful.2.2 before beforeMem

theorem step_lawful [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (grants : List (Grant Party Scope)) (actor : Party)
    (ledger : Ledger Party Scope Answer Fault) (action : Action Party Scope Answer Fault)
    (lawful : Lawful meaning ledger) : Lawful meaning (step meaning grants actor ledger action) := by
  cases action with
  | issue obligee scope primaryBudget repairBudget =>
      simp only [step]
      split
      · refine ⟨?_, ?_, ?_⟩
        · simpa [List.map_append, Row.issued] using lawful.1
        · simpa [List.map_append, List.range_succ] using lawful.2.1
        · intro row present
          rcases List.mem_append.mp present with old | fresh
          · exact lawful.2.2 row old
          · have same := List.mem_singleton.mp fresh
            subst row
            exact Row.issued_lawful meaning _ _ _
      · exact lawful
  | supervise occurrence purpose event =>
      exact update_lawful meaning occurrence _ (Row.supervise_origin grants actor purpose event)
        (fun row valid => row.supervise_lawful meaning grants actor purpose event valid) ledger lawful
  | transfer occurrence recipient =>
      exact update_lawful meaning occurrence _ (Row.transfer_origin grants actor recipient)
        (fun row valid => row.transfer_lawful meaning grants actor recipient valid) ledger lawful
  | cancel occurrence =>
      apply update_lawful meaning occurrence (fun row => {row with cancelled := true})
        (fun _ => rfl) _ ledger lawful
      intro row valid
      exact valid
  | settle occurrence purpose =>
      exact update_lawful meaning occurrence _ (Row.settle_origin meaning grants actor purpose)
        (fun row valid => row.settle_lawful meaning grants actor purpose valid) ledger lawful

theorem run_lawful [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (ledger : Ledger Party Scope Answer Fault)
    (requests : List (Request Party Scope Answer Fault)) (lawful : Lawful meaning ledger) :
    Lawful meaning (run meaning ledger requests) := by
  induction requests generalizing ledger with
  | nil => exact lawful
  | cons request rest ih =>
      rcases request with ⟨grants, actor, action⟩
      exact ih _ (step_lawful meaning grants actor ledger action lawful)

theorem lawful_duty_conservation [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (after : Ledger Party Scope Answer Fault)
    (lawful : Lawful meaning after) (occurrence : Nat) (issued : occurrence < after.issued.length) :
    (after.rows.map fun row => row.origin.occurrence).count occurrence = 1 ∧
      ∃ row ∈ after.rows, row.origin.occurrence = occurrence ∧
        Ownership row.origin row.transfers row.holder ∧
        (row.disposition = none ∨
          ∃ receipt, row.disposition = some receipt ∧ row.AuthorizedDisposition meaning receipt) := by
  have keys : (after.rows.map fun row => row.origin.occurrence) = List.range after.issued.length := by
    calc
      _ = (after.rows.map Row.origin).map Descriptor.occurrence := List.map_map.symm
      _ = _ := by rw [lawful.1, lawful.2.1]
  have member : occurrence ∈ after.rows.map (fun row => row.origin.occurrence) := by
    rw [keys]
    exact List.mem_range.mpr issued
  refine ⟨List.count_eq_one_of_mem (keys ▸ List.nodup_range) member, ?_⟩
  obtain ⟨row, present, same⟩ := List.mem_map.mp member
  refine ⟨row, present, same, (lawful.2.2 row present).2.2.1, ?_⟩
  cases disposition : row.disposition with
  | none => exact Or.inl rfl
  | some receipt => exact Or.inr ⟨receipt, rfl, (lawful.2.2 row present).2.2.2 _ disposition⟩

/-- This conservation theorem is derived from the concrete allocating,
transferring, supervising and settling transitions from the empty ledger.
Neither target conservation nor a generic duty-preservation premise is assumed. -/
theorem issued_duty_conservation [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (requests : List (Request Party Scope Answer Fault))
    (occurrence : Nat)
    (issued : occurrence < (run meaning initial requests).issued.length) :
    let after := run meaning initial requests
    (after.rows.map fun row => row.origin.occurrence).count occurrence = 1 ∧
      ∃ row ∈ after.rows, row.origin.occurrence = occurrence ∧
        Ownership row.origin row.transfers row.holder ∧
        (row.disposition = none ∨
          ∃ receipt, row.disposition = some receipt ∧ row.AuthorizedDisposition meaning receipt) :=
  lawful_duty_conservation meaning _
    (run_lawful meaning initial requests (initial_lawful meaning)) occurrence issued

/-- Copying or transferring a descriptor does not allocate another duty.
Only the separately authorized `issue` transition extends this exact list. -/
theorem transfer_preserves_issued_occurrences [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (grants : List (Grant Party Scope)) (actor recipient : Party)
    (ledger : Ledger Party Scope Answer Fault) (occurrence : Nat) :
    (step meaning grants actor ledger (.transfer occurrence recipient)).rows.map Row.origin =
      ledger.rows.map Row.origin := by
  change (ledger.rows.map _).map Row.origin = _
  rw [List.map_map]
  apply List.map_congr_left
  intro row _
  dsimp only [Function.comp_apply]
  split
  · exact Row.transfer_origin _ _ _ _
  · rfl

theorem stale_holder_cannot_transfer_twice [DecidableEq Party] [DecidableEq Scope]
    (grants : List (Grant Party Scope)) (actor recipient : Party) (row : Row Party Scope Answer Fault)
    (pending : row.disposition = none) (holder : actor = row.holder)
    (gives : allowed grants actor row.origin.scope .transfer = true)
    (accepts : allowed grants recipient row.origin.scope .hold = true)
    (distinct : actor ≠ recipient) :
    (row.transfer grants actor recipient).transfer grants actor recipient =
      row.transfer grants actor recipient := by
  have approved : row.disposition.isNone ∧ actor = row.holder ∧
      allowed grants actor row.origin.scope .transfer = true ∧
      allowed grants recipient row.origin.scope .hold = true :=
    ⟨by simp [pending], holder, gives, accepts⟩
  have moved : row.transfer grants actor recipient =
      {row with holder := recipient, transfers := row.transfers ++ [⟨actor, recipient, grants⟩]} := by
    exact if_pos approved
  rw [moved]
  apply if_neg
  intro again
  exact distinct again.2.1

/-! ### The existing atomic publication boundary

The target is computed from the actual local action. A conflict retains the
whole original ledger and pending command; it never removes an issued duty.
External effects are deliberately outside this local atomic snapshot.
-/

structure PublicationState (Party Scope Answer Fault : Type) where
  ledger : Ledger Party Scope Answer Fault
  authority : List (Grant Party Scope)
  deriving DecidableEq, Repr

structure Proposal (Party Scope Answer Fault : Type) where
  captured : Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Snapshot Nat
    (PublicationState Party Scope Answer Fault)
  actor : Party
  action : Action Party Scope Answer Fault

def publicationSpec [DecidableEq Party] [DecidableEq Scope] (meaning : Meaning Party Scope Answer) :
    Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Spec Nat (PublicationState Party Scope Answer Fault)
      (Action Party Scope Answer Fault) (Proposal Party Scope Answer Fault) where
  capturedRevision proposal := proposal.captured.revision
  capturedState proposal := proposal.captured.state
  targetState proposal :=
    {proposal.captured.state with
      ledger := step meaning proposal.captured.state.authority proposal.actor
        proposal.captured.state.ledger proposal.action}
  pendingWork proposal := [proposal.action]

/-- The current authority data is in the validated snapshot alongside the
ledger. It is not an unvalidated permission copied into the proposal. -/
def publish [DecidableEq Party] [DecidableEq Scope] [DecidableEq Answer] [DecidableEq Fault]
    (meaning : Meaning Party Scope Answer) (proposal : Proposal Party Scope Answer Fault)
    (live : Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Snapshot Nat
      (PublicationState Party Scope Answer Fault)) :
    Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Decision (publicationSpec meaning) proposal live :=
  Mettapedia.GSLT.Core.AtomicSnapshotTransaction.attempt (publicationSpec meaning) proposal live
    (live.revision + 1) (by omega)

/-- Conservation of an accepted publication follows from the computed action
and exact captured-state match, rather than a supplied target-validity premise. -/
theorem committed_publication_lawful [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (proposal : Proposal Party Scope Answer Fault)
    (live : Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Snapshot Nat
      (PublicationState Party Scope Answer Fault))
    (receipt : Mettapedia.GSLT.Core.AtomicSnapshotTransaction.CommitReceipt
      (publicationSpec meaning) proposal live) (lawful : Lawful meaning live.state.ledger) :
    Lawful meaning receipt.after.state.ledger := by
  change Lawful meaning (step meaning proposal.captured.state.authority proposal.actor
    proposal.captured.state.ledger proposal.action)
  apply step_lawful
  have same : live.state.ledger = proposal.captured.state.ledger :=
    congrArg PublicationState.ledger receipt.current.state_eq
  rw [← same]
  exact lawful

theorem committed_publication_uses_current_authority [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (proposal : Proposal Party Scope Answer Fault)
    (live : Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Snapshot Nat
      (PublicationState Party Scope Answer Fault))
    (receipt : Mettapedia.GSLT.Core.AtomicSnapshotTransaction.CommitReceipt
      (publicationSpec meaning) proposal live) :
    proposal.captured.state.authority = live.state.authority :=
  (congrArg PublicationState.authority receipt.current.state_eq).symm

theorem publication_accounts_exact_command [DecidableEq Party] [DecidableEq Scope]
    (meaning : Meaning Party Scope Answer) (proposal : Proposal Party Scope Answer Fault)
    (live : Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Snapshot Nat
      (PublicationState Party Scope Answer Fault))
    (decision : Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Decision
      (publicationSpec meaning) proposal live) :
    decision.orderedLedger.executed ++ decision.orderedLedger.pending = [proposal.action] :=
  decision.orderedLedger_accounts

namespace Controls

def meaning : Meaning Nat Nat Nat := fun origin _ answer => decide (answer = origin.scope)

def grants (actor scope : Nat) : List (Grant Nat Nat) :=
  [⟨actor, scope, .issue⟩, ⟨actor, scope, .hold⟩, ⟨actor, scope, .transfer⟩,
    ⟨actor, scope, .execute⟩, ⟨actor, scope, .adopt⟩, ⟨actor, scope, .compensate⟩]

def authority : List (Grant Nat Nat) := grants 1 5 ++ grants 3 5

def requests : List (Request Nat Nat Nat String) :=
  [(authority, 1, .issue 2 5 2 2),
    (authority, 1, .transfer 0 3),
    (authority, 3, .supervise 0 .primary (.control .reserve)),
    ([], 3, .supervise 0 .primary (.reply ⟨(0, .primary), 1, .complete, .value 5, false⟩))]

def completed : Ledger Nat Nat Nat String := run meaning initial requests
def adopted : Ledger Nat Nat Nat String := step meaning authority 3 completed (.settle 0 .primary)
def revoked : Ledger Nat Nat Nat String := step meaning [] 3 completed (.settle 0 .primary)
def cancelled : Ledger Nat Nat Nat String := step meaning [] 3 adopted (.cancel 0)

theorem actual_transfers_and_persistence_preserve_single_duty :
    completed.issued = [⟨0, 1, 2, 5⟩] ∧
      (completed.rows.map fun row => row.origin.occurrence).count 0 = 1 ∧
      (completed.rows[0]?).map Row.holder = some 3 ∧
      (completed.rows[0]?).map (fun row => row.primary.task.phase) =
        some (.terminal (.completed (.value 5))) ∧
      (completed.rows[0]?).map Row.disposition = some none := by decide

theorem revocation_refuses_adoption_without_erasing_completion : revoked = completed := by decide

theorem authorized_adoption_records_disposition_before_ack :
    (adopted.rows[0]?).map Row.disposition =
      some (some ⟨3, .primary, 1, 5, authority⟩) ∧
      (adopted.rows[0]?).map (fun row => row.primary.task.acknowledged) = some true ∧
      Lawful meaning adopted := by
  refine ⟨by decide, by decide, ?_⟩
  exact step_lawful meaning authority 3 completed (.settle 0 .primary)
    (run_lawful meaning initial requests (initial_lawful meaning))

theorem cancellation_preserves_authorized_completed_disposition :
    cancelled.issued = adopted.issued ∧
      (cancelled.rows[0]?).map Row.disposition = (adopted.rows[0]?).map Row.disposition ∧
      (cancelled.rows[0]?).map (fun row => row.primary.task.phase) =
        (adopted.rows[0]?).map (fun row => row.primary.task.phase) ∧
      (cancelled.rows[0]?).map Row.cancelled = some true := by decide

theorem copied_reference_cannot_duplicate_transferred_duty :
    step meaning authority 1 completed (.transfer 0 3) = completed ∧
      (step meaning authority 1 completed (.transfer 0 3)).rows.length = 1 := by decide

theorem equal_descriptions_can_be_distinct_issued_occurrences :
    let twice : Ledger Nat Nat Nat String := run meaning initial
      [(authority, 1, .issue 2 5 2 2), (authority, 1, .issue 2 5 2 2)]
    twice.issued = [⟨0, 1, 2, 5⟩, ⟨1, 1, 2, 5⟩] ∧
      twice.rows.map (fun row => row.origin.scope) = [5, 5] ∧
      (twice.rows.map fun row => row.origin.occurrence).count 0 = 1 ∧
      (twice.rows.map fun row => row.origin.occurrence).count 1 = 1 := by decide

def proposal : Proposal Nat Nat Nat String :=
  ⟨⟨7, ⟨completed, authority⟩⟩, 3, .settle 0 .primary⟩

def revokedSnapshot : Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Snapshot Nat
    (PublicationState Nat Nat Nat String) := ⟨8, ⟨completed, []⟩⟩

theorem actual_atomic_publication_commits_complete_disposition :
    (publish meaning proposal proposal.captured).physicalSnapshot = ⟨8, ⟨adopted, authority⟩⟩ ∧
      (publish meaning proposal proposal.captured).orderedLedger.executed = [.settle 0 .primary] ∧
      (publish meaning proposal proposal.captured).orderedLedger.pending = [] := by
  exact ⟨rfl, rfl, rfl⟩

theorem revocation_before_atomic_commit_retains_duty_and_command :
    (publish meaning proposal revokedSnapshot).physicalSnapshot = revokedSnapshot ∧
      (publish meaning proposal revokedSnapshot).orderedLedger.executed = [] ∧
      (publish meaning proposal revokedSnapshot).orderedLedger.pending = [.settle 0 .primary] := by
  exact ⟨rfl, rfl, rfl⟩

theorem changed_authority_cannot_hide_behind_reused_revision :
    let live := {revokedSnapshot with revision := 7}
    (publish meaning proposal live).physicalSnapshot = live ∧
      (publish meaning proposal live).orderedLedger.pending = [.settle 0 .primary] := by
  exact ⟨rfl, rfl⟩

end Controls

#print axioms Row.transfer_lawful
#print axioms Row.supervise_lawful
#print axioms Row.settle_lawful
#print axioms step_lawful
#print axioms issued_duty_conservation
#print axioms transfer_preserves_issued_occurrences
#print axioms stale_holder_cannot_transfer_twice
#print axioms committed_publication_lawful
#print axioms committed_publication_uses_current_authority
#print axioms publication_accounts_exact_command
#print axioms Controls.actual_transfers_and_persistence_preserve_single_duty
#print axioms Controls.revocation_refuses_adoption_without_erasing_completion
#print axioms Controls.authorized_adoption_records_disposition_before_ack
#print axioms Controls.cancellation_preserves_authorized_completed_disposition
#print axioms Controls.copied_reference_cannot_duplicate_transferred_duty
#print axioms Controls.equal_descriptions_can_be_distinct_issued_occurrences
#print axioms Controls.actual_atomic_publication_commits_complete_disposition
#print axioms Controls.revocation_before_atomic_commit_retains_duty_and_command
#print axioms Controls.changed_authority_cannot_hide_behind_reused_revision

end DurableDuty

end Mettapedia.Machines.ErrorBoundaryContracts.AttemptIdentity
