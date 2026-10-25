import Mettapedia.Machines.ErrorBoundaryContracts.AttemptIdentity
import Mettapedia.GSLT.LanguageDef.OperationCostProtocol
import Mettapedia.Machines.Cursor.ReadOnlyQuery

/-! A persisted reservation and a one-use local dispatch permit are different
objects. This model counts grants, not external effects. Its validity argument
is supplied by checking the current ledger owner, generation and active phase.
Restart invalidates old permits; it does not manufacture a fresh reservation. -/

namespace Mettapedia.Machines.ErrorBoundaryContracts.DispatchPermit

universe u v w
variable {α : Type u} {ε : Type v} {Id : Type w}

def claim (used valid : Bool) : Bool × Nat :=
  if valid && !used then (true, 1) else (used, 0)

def run : Bool → List Bool → Bool × Nat
  | used, [] => (used, 0)
  | used, valid :: rest =>
    let first := claim used valid
    let later := run first.1 rest
    (later.1, first.2 + later.2)

theorem claim_accounting (used valid : Bool) :
    (claim used valid).1.toNat = used.toNat + (claim used valid).2 := by
  cases used <;> cases valid <;> rfl

theorem run_accounting (used : Bool) (requests : List Bool) :
    (run used requests).1.toNat = used.toNat + (run used requests).2 := by
  induction requests generalizing used with
  | nil => simp [run]
  | cons valid rest ih =>
    simp only [run]
    rw [ih, claim_accounting]
    omega

theorem at_most_one_grant (requests : List Bool) : (run false requests).2 ≤ 1 := by
  have h := run_accounting false requests
  have bound : (run false requests).1.toNat ≤ 1 := by
    cases (run false requests).1 <;> decide
  simp only [Bool.toNat_false, Nat.zero_add] at h
  omega

theorem used_permit_never_grants (requests : List Bool) :
    (run true requests).2 = 0 := by
  have h := run_accounting true requests
  have bound : (run true requests).1.toNat ≤ 1 := by
    cases (run true requests).1 <;> decide
  simp only [Bool.toNat_true] at h
  omega

theorem rejected_request_keeps_permit (used : Bool) : claim used false = (used, 0) := by
  cases used <;> rfl

def ready (task : Supervision.Task α ε) : Bool :=
  match task.phase, task.remaining with
  | .ready, _ + 1 => true
  | _, _ => false

def nextReady : List (Id × Supervision.Task α ε) → Option Id
  | [] => none
  | (id, task) :: rest => if ready task then some id else nextReady rest

theorem nextReady_skips_unready (earlier rest : List (Id × Supervision.Task α ε))
    (h : ∀ entry ∈ earlier, ready entry.2 = false) :
    nextReady (earlier ++ rest) = nextReady rest := by
  induction earlier with
  | nil => rfl
  | cons entry tail ih =>
    simp only [List.cons_append, nextReady, h entry (by simp), Bool.false_eq_true,
      ↓reduceIte]
    exact ih (fun x hx => h x (by simp [hx]))

theorem uncertain_does_not_block_ready (first second : Id) (n : Nat) :
    nextReady [(first, (⟨n, .uncertain, false⟩ : Supervision.Task α ε)),
      (second, Supervision.initial (n + 1))] = some second := by
  simp [nextReady, ready, Supervision.initial]

example : run false [false, true, true, false, true] = (true, 1) := rfl
example : run true [true, true] = (true, 0) := rfl

/-! ## A supervised escrow service with a real compensator

Local duty publication, transport dispatch, remote acceptance, completion
persistence and adoption remain distinct actions. The remote service commits
its idempotency identity together with its debit/refund. Its compensator
restores the balance but retains both historical effects. Storage durability,
authenticated service replies and physical atomicity remain implementation
obligations of this declared profile.
-/

namespace DurableEscrow

open AttemptIdentity.DurableDuty
open RunContracts.ScopedOutcome

structure Receipt where
  occurrence : Nat
  amount : Nat
  purpose : Purpose
  deriving DecidableEq, Repr

inductive Effect where
  | debit (occurrence amount : Nat)
  | refund (occurrence amount : Nat)
  deriving DecidableEq, Repr

structure Remote where
  /-- The example wallet belongs to obligee 2; service 1 owns the escrow. -/
  balance : Nat
  accepted : List (Nat × Nat)
  refunded : Finset Nat
  irreversible : Finset Nat
  history : List Effect
  deriving DecidableEq

def remoteInitial (balance : Nat) : Remote := ⟨balance, [], ∅, ∅, []⟩

def Remote.accept (occurrence amount : Nat) (reversible : Bool) (remote : Remote) :
    Outcome Receipt String × Remote :=
  match remote.accepted.lookup occurrence with
  | some previous =>
      if previous = amount then (.value ⟨occurrence, amount, .primary⟩, remote)
      else (.raised "request-key-conflict", remote)
  | none =>
      if 0 < amount ∧ amount ≤ remote.balance then
        (.value ⟨occurrence, amount, .primary⟩,
          {remote with
            balance := remote.balance - amount
            accepted := (occurrence, amount) :: remote.accepted
            irreversible := if reversible then remote.irreversible else insert occurrence remote.irreversible
            history := remote.history ++ [.debit occurrence amount]})
      else (.raised "insufficient-funds", remote)

def Remote.compensate (occurrence amount : Nat) (remote : Remote) :
    Outcome Receipt String × Remote :=
  match remote.accepted.lookup occurrence with
  | none => (.raised "no-accepted-reservation", remote)
  | some previous =>
      if previous ≠ amount then (.raised "request-key-conflict", remote)
      else if occurrence ∈ remote.irreversible then (.raised "irreversible-effect", remote)
      else if occurrence ∈ remote.refunded then (.value ⟨occurrence, amount, .repair⟩, remote)
      else
        (.value ⟨occurrence, amount, .repair⟩,
          {remote with
            balance := remote.balance + amount
            refunded := insert occurrence remote.refunded
            history := remote.history ++ [.refund occurrence amount]})

def Receipt.valid (receipt : Receipt) (remote : Remote) : Bool :=
  remote.accepted.lookup receipt.occurrence == some receipt.amount &&
    match receipt.purpose with
    | .primary => decide (receipt.occurrence ∉ remote.refunded)
    | .repair => decide (receipt.occurrence ∈ remote.refunded)

def meaning : Meaning Nat Nat Receipt := fun origin purpose receipt =>
  decide (receipt.occurrence = origin.occurrence ∧ receipt.amount = origin.scope ∧ receipt.purpose = purpose)

/-- This is an actual compensator postcondition for every fresh funded
reservation. The original balance is restored; the debit and refund remain
distinct ordered historical effects. -/
theorem compensation_restores_balance_and_retains_history (remote : Remote)
    (occurrence amount : Nat) (fresh : remote.accepted.lookup occurrence = none)
    (notRefunded : occurrence ∉ remote.refunded) (notIrreversible : occurrence ∉ remote.irreversible)
    (positive : 0 < amount) (funded : amount ≤ remote.balance) :
    let accepted := (remote.accept occurrence amount true).2
    let repaired := accepted.compensate occurrence amount
    repaired.1 = .value ⟨occurrence, amount, .repair⟩ ∧
      repaired.2.balance = remote.balance ∧
      repaired.2.history = remote.history ++ [.debit occurrence amount, .refund occurrence amount] ∧
      (Receipt.mk occurrence amount .repair).valid repaired.2 = true := by
  simp [Remote.accept, fresh, positive, funded, Remote.compensate, notRefunded,
    notIrreversible, Nat.sub_add_cancel funded, List.append_assoc, Receipt.valid]

theorem compensation_replay_is_inert (remote : Remote) (occurrence amount : Nat)
    (accepted : remote.accepted.lookup occurrence = some amount)
    (refunded : occurrence ∈ remote.refunded) (reversible : occurrence ∉ remote.irreversible) :
    remote.compensate occurrence amount = (.value ⟨occurrence, amount, .repair⟩, remote) := by
  simp [Remote.compensate, accepted, reversible, refunded]

theorem irreversible_effect_refuses_compensation (remote : Remote) (occurrence amount : Nat)
    (accepted : remote.accepted.lookup occurrence = some amount)
    (irreversible : occurrence ∈ remote.irreversible) :
    remote.compensate occurrence amount = (.raised "irreversible-effect", remote) := by
  simp [Remote.compensate, accepted, irreversible]

structure Envelope where
  occurrence : Nat
  purpose : Purpose
  generation : Nat
  amount : Nat
  deriving DecidableEq, Repr

structure Service where
  ledger : Ledger Nat Nat Receipt String
  remote : Remote
  reversible : Bool
  dispatched : Finset (Nat × Purpose × Nat)
  pending : List Envelope
  replies : List (AttemptIdentity.Reply (Nat × Purpose) Receipt String)
  deriving DecidableEq

def initialService (balance : Nat) (reversible : Bool) : Service :=
  ⟨AttemptIdentity.DurableDuty.initial, remoteInitial balance, reversible, ∅, [], []⟩

def Service.local (service : Service) (grants : List (Grant Nat Nat)) (actor : Nat)
    (action : Action Nat Nat Receipt String) : Service :=
  { service with ledger := AttemptIdentity.DurableDuty.step meaning grants actor service.ledger action }

def direction (cancelled : Bool) : Purpose → Bool
  | .primary => !cancelled
  | .repair => cancelled

/-- Dispatch consumes the existing one-use claim for the exact task purpose
and attempt. An active ledger cell by itself never grants another send. -/
def Service.dispatch (service : Service) (grants : List (Grant Nat Nat))
    (actor occurrence : Nat) (purpose : Purpose) : Service :=
  match service.ledger.rows[occurrence]? with
  | none => service
  | some row =>
      let task := row.task purpose
      let token := (occurrence, purpose, task.generation)
      let active := match task.task.phase with | .active => true | _ => false
      let admitted := decide (actor = row.holder) && allowed grants actor row.origin.scope .execute &&
        row.disposition.isNone && direction row.cancelled purpose && active
      let claimed := claim (decide (token ∈ service.dispatched)) admitted
      if claimed.2 = 1 then
        {service with
          dispatched := insert token service.dispatched
          pending := service.pending ++ [⟨occurrence, purpose, task.generation, row.origin.scope⟩]}
      else service

/-- The receiver changes only external state and produces a correlated reply.
It does not manufacture a locally persisted completion. -/
def Service.acceptRemote (service : Service) : Service :=
  match service.pending with
  | [] => service
  | envelope :: rest =>
      let accepted := match envelope.purpose with
        | .primary => service.remote.accept envelope.occurrence envelope.amount service.reversible
        | .repair => service.remote.compensate envelope.occurrence envelope.amount
      {service with
        remote := accepted.2
        pending := rest
        replies := service.replies ++
          [⟨(envelope.occurrence, envelope.purpose), envelope.generation, .complete, accepted.1, false⟩]}

/-- Persist only the actual transport reply. The existing attempt owner and
phase checks decide whether it is current, stale, or requires reconciliation. -/
def Service.persistCompletion (service : Service) : Service :=
  match service.replies with
  | [] => service
  | reply :: rest =>
      {service.local [] 0 (.supervise reply.owner.1 reply.owner.2 (.reply reply)) with replies := rest}

def restartRows : List Nat → Ledger Nat Nat Receipt String → Ledger Nat Nat Receipt String
  | [], ledger => ledger
  | occurrence :: rest, ledger =>
      restartRows rest
        (AttemptIdentity.DurableDuty.step meaning [] 0
          (AttemptIdentity.DurableDuty.step meaning [] 0 ledger
            (.supervise occurrence .primary (.control .restart)))
          (.supervise occurrence .repair (.control .restart)))

/-- Remote acceptance and in-flight delivery survive independently of the
local process. Unpersisted return messages may be lost. Active attempts become
uncertain through the original supervision transition. -/
def Service.crash (service : Service) : Service :=
  {service with
    ledger := restartRows (service.ledger.issued.map Descriptor.occurrence) service.ledger
    replies := []}

/-- A missing remote record remains unknown. A positive query reconstructs
the exact receipt and submits an existing `reconcile` event; it never fabricates
failure or a fresh attempt from absence. -/
def Service.reconcile (service : Service) (occurrence : Nat) (purpose : Purpose) : Service :=
  match service.ledger.rows[occurrence]? with
  | none => service
  | some row =>
      let receipt := Receipt.mk occurrence row.origin.scope purpose
      if receipt.valid service.remote then
        service.local [] 0 (.supervise occurrence purpose
          (.reply ⟨(occurrence, purpose), (row.task purpose).generation, .reconcile, .value receipt, false⟩))
      else service

/-- The ordinary adopting route checks current service evidence, direction
and authority. No acknowledgement is inferred from a missing reply. -/
def Service.adopt (service : Service) (grants : List (Grant Nat Nat))
    (actor occurrence : Nat) (purpose : Purpose) : Service :=
  match service.ledger.rows[occurrence]? with
  | none => service
  | some row =>
      match (row.task purpose).task.phase with
      | .terminal (.completed (.value receipt)) =>
          if receipt.valid service.remote && direction row.cancelled purpose then
            service.local grants actor (.settle occurrence purpose)
          else service
      | _ => service

inductive Command where
  | issue (grants : List (Grant Nat Nat)) (actor beneficiary amount primaryBudget repairBudget : Nat)
  | reserve (grants : List (Grant Nat Nat)) (actor occurrence : Nat) (purpose : Purpose)
  | transfer (grants : List (Grant Nat Nat)) (actor occurrence recipient : Nat)
  | cancel (occurrence : Nat)
  | dispatch (grants : List (Grant Nat Nat)) (actor occurrence : Nat) (purpose : Purpose)
  | acceptRemote
  | persistCompletion
  | reconcile (occurrence : Nat) (purpose : Purpose)
  | abandon (occurrence : Nat) (purpose : Purpose)
  | crash
  | adopt (grants : List (Grant Nat Nat)) (actor occurrence : Nat) (purpose : Purpose)
  deriving DecidableEq, Repr

/-- This is an adapter over the existing attempt/supervision machine, not a
replacement evaluator. Every local task transition delegates to its owner. -/
def serviceStep (service : Service) : Command → Service
  | .issue grants actor beneficiary amount primaryBudget repairBudget =>
      if actor = 1 ∧ beneficiary = 2 then
        service.local grants actor (.issue beneficiary amount primaryBudget repairBudget)
      else service
  | .reserve grants actor occurrence purpose =>
      service.local grants actor (.supervise occurrence purpose (.control .reserve))
  | .transfer grants actor occurrence recipient => service.local grants actor (.transfer occurrence recipient)
  | .cancel occurrence => service.local [] 0 (.cancel occurrence)
  | .dispatch grants actor occurrence purpose => service.dispatch grants actor occurrence purpose
  | .acceptRemote => service.acceptRemote
  | .persistCompletion => service.persistCompletion
  | .reconcile occurrence purpose => service.reconcile occurrence purpose
  | .abandon occurrence purpose =>
      service.local [] 0 (.supervise occurrence purpose (.control .abandonUncertain))
  | .crash => service.crash
  | .adopt grants actor occurrence purpose => service.adopt grants actor occurrence purpose

def serviceRun (service : Service) : List Command → Service
  | [] => service
  | command :: rest => serviceRun (serviceStep service command) rest

theorem Service.local_lawful (service : Service) (grants : List (Grant Nat Nat)) (actor : Nat)
    (action : Action Nat Nat Receipt String) (lawful : Lawful meaning service.ledger) :
    Lawful meaning (service.local grants actor action).ledger :=
  AttemptIdentity.DurableDuty.step_lawful meaning grants actor service.ledger action lawful

theorem Service.dispatch_lawful (service : Service) (grants : List (Grant Nat Nat))
    (actor occurrence : Nat) (purpose : Purpose) (lawful : Lawful meaning service.ledger) :
    Lawful meaning (service.dispatch grants actor occurrence purpose).ledger := by
  unfold Service.dispatch
  split
  · exact lawful
  · dsimp only
    split <;> split <;> exact lawful

theorem Service.acceptRemote_lawful (service : Service) (lawful : Lawful meaning service.ledger) :
    Lawful meaning service.acceptRemote.ledger := by
  cases pending : service.pending <;> simpa [Service.acceptRemote, pending] using lawful

theorem Service.persistCompletion_lawful (service : Service) (lawful : Lawful meaning service.ledger) :
    Lawful meaning service.persistCompletion.ledger := by
  cases replies : service.replies with
  | nil => simpa [Service.persistCompletion, replies] using lawful
  | cons reply rest =>
      simpa only [Service.persistCompletion, replies] using
        service.local_lawful [] 0 (.supervise reply.owner.1 reply.owner.2 (.reply reply)) lawful

theorem restartRows_lawful (keys : List Nat) (ledger : Ledger Nat Nat Receipt String)
    (lawful : Lawful meaning ledger) : Lawful meaning (restartRows keys ledger) := by
  induction keys generalizing ledger with
  | nil => exact lawful
  | cons occurrence rest ih =>
      exact ih _ (AttemptIdentity.DurableDuty.step_lawful _ _ _ _ _
        (AttemptIdentity.DurableDuty.step_lawful _ _ _ _ _ lawful))

theorem Service.crash_lawful (service : Service) (lawful : Lawful meaning service.ledger) :
    Lawful meaning service.crash.ledger :=
  restartRows_lawful _ _ lawful

theorem Service.reconcile_lawful (service : Service) (occurrence : Nat) (purpose : Purpose)
    (lawful : Lawful meaning service.ledger) :
    Lawful meaning (service.reconcile occurrence purpose).ledger := by
  unfold Service.reconcile
  split
  · exact lawful
  · dsimp only
    split
    · exact service.local_lawful _ _ _ lawful
    · exact lawful

theorem Service.adopt_lawful (service : Service) (grants : List (Grant Nat Nat))
    (actor occurrence : Nat) (purpose : Purpose) (lawful : Lawful meaning service.ledger) :
    Lawful meaning (service.adopt grants actor occurrence purpose).ledger := by
  unfold Service.adopt
  split
  · exact lawful
  · split
    · split
      · exact service.local_lawful _ _ _ lawful
      · exact lawful
    · exact lawful

/-- Any effective adoption must pass the concrete receiver-evidence check on
an already persisted successful completion. This is derived from the actual
adapter branches; neither intent nor uncertainty is accepted as an answer. -/
theorem Service.changed_adoption_has_remote_evidence (service : Service)
    (grants : List (Grant Nat Nat)) (actor occurrence : Nat) (purpose : Purpose)
    (changed : service.adopt grants actor occurrence purpose ≠ service) :
    ∃ row receipt, service.ledger.rows[occurrence]? = some row ∧
      (row.task purpose).task.phase = .terminal (.completed (.value receipt)) ∧
      receipt.valid service.remote = true ∧ direction row.cancelled purpose = true := by
  cases found : service.ledger.rows[occurrence]? with
  | none => simp [Service.adopt, found] at changed
  | some row =>
      cases phase : (row.task purpose).task.phase with
      | ready => simp [Service.adopt, found, phase] at changed
      | active => simp [Service.adopt, found, phase] at changed
      | uncertain => simp [Service.adopt, found, phase] at changed
      | terminal result =>
          cases result with
          | unresolved => simp [Service.adopt, found, phase] at changed
          | completed outcome =>
              cases outcome with
              | raised fault => simp [Service.adopt, found, phase] at changed
              | value receipt =>
                  cases approved : receipt.valid service.remote && direction row.cancelled purpose with
                  | false => simp [Service.adopt, found, phase, approved] at changed
                  | true =>
                      have conjunction : receipt.valid service.remote = true ∧
                          direction row.cancelled purpose = true := by
                        simpa only [Bool.and_eq_true] using approved
                      exact ⟨row, receipt, rfl, phase, conjunction⟩

theorem serviceStep_lawful (service : Service) (command : Command)
    (lawful : Lawful meaning service.ledger) : Lawful meaning (serviceStep service command).ledger := by
  cases command with
  | issue grants actor beneficiary amount primaryBudget repairBudget =>
      dsimp only [serviceStep]
      split
      · exact service.local_lawful _ _ _ lawful
      · exact lawful
  | reserve grants actor occurrence purpose => exact service.local_lawful _ _ _ lawful
  | transfer grants actor occurrence recipient => exact service.local_lawful _ _ _ lawful
  | cancel occurrence => exact service.local_lawful _ _ _ lawful
  | dispatch grants actor occurrence purpose => exact service.dispatch_lawful _ _ _ _ lawful
  | acceptRemote => exact service.acceptRemote_lawful lawful
  | persistCompletion => exact service.persistCompletion_lawful lawful
  | reconcile occurrence purpose => exact service.reconcile_lawful _ _ lawful
  | abandon occurrence purpose => exact service.local_lawful _ _ _ lawful
  | crash => exact service.crash_lawful lawful
  | adopt grants actor occurrence purpose => exact service.adopt_lawful _ _ _ _ lawful

theorem serviceRun_lawful (service : Service) (commands : List Command)
    (lawful : Lawful meaning service.ledger) : Lawful meaning (serviceRun service commands).ledger := by
  induction commands generalizing service with
  | nil => exact lawful
  | cons command rest ih => exact ih _ (serviceStep_lawful _ _ lawful)

/-- Duties remain uniquely owned or have an authorized disposition through
the real service adapter, including remote acceptance, lost replies, restart,
reconciliation, transfer and current-authority adoption. -/
theorem service_run_duty_conservation (balance : Nat) (reversible : Bool)
    (commands : List Command) (occurrence : Nat)
    (issued : occurrence < (serviceRun (initialService balance reversible) commands).ledger.issued.length) :
    let after := (serviceRun (initialService balance reversible) commands).ledger
    (after.rows.map fun row => row.origin.occurrence).count occurrence = 1 ∧
      ∃ row ∈ after.rows, row.origin.occurrence = occurrence ∧
        Ownership row.origin row.transfers row.holder ∧
        (row.disposition = none ∨
          ∃ receipt, row.disposition = some receipt ∧ row.AuthorizedDisposition meaning receipt) :=
  lawful_duty_conservation meaning _
    (serviceRun_lawful _ _ (initial_lawful meaning)) occurrence issued

theorem Service.crash_preserves_external_effects (service : Service) :
    service.crash.remote = service.remote := rfl

theorem Service.cancellation_preserves_external_effects (service : Service) (occurrence : Nat) :
    (serviceStep service (.cancel occurrence)).remote = service.remote := rfl

theorem Service.dispatch_preserves_external_effects (service : Service) (grants : List (Grant Nat Nat))
    (actor occurrence : Nat) (purpose : Purpose) :
    (service.dispatch grants actor occurrence purpose).remote = service.remote := by
  unfold Service.dispatch
  split
  · rfl
  · dsimp only
    split <;> split <;> rfl

/-! ### Compensation interpreted through the existing treaty kernel -/

open Mettapedia.Logic.GovernanceReasoning
open TreatyKernel Subsumption

inductive PaymentPredicate where
  | refund
  deriving DecidableEq, Repr

def refundRoles (amount : Nat) : Core.ThematicRole → Option Nat
  | .agent => some 1
  | .beneficiary => some 2
  | .theme => some amount
  | _ => none

def refundClause (amount : Nat) : TreatyClause Nat Nat PaymentPredicate Nat Nat :=
  { id := amount
    obligor := 1
    obligee := 2
    modality := .obligatory
    eventPattern := ⟨.refund, refundRoles amount, true⟩ }

def refundEvent (occurrence amount : Nat) : TreatyEvent Nat PaymentPredicate Nat Nat :=
  ⟨0, ⟨.refund, (fun role => if role = .result then some occurrence else refundRoles amount role), true⟩, 3⟩

def treatyTrace (history : List Effect) : TreatyTrace Nat PaymentPredicate Nat Nat :=
  history.filterMap fun effect => match effect with
    | .debit _ _ => none
    | .refund occurrence amount => some (refundEvent occurrence amount)

theorem actual_refund_matches_clause (occurrence amount : Nat) :
    eventSubsumes (refundClause amount).eventPattern (refundEvent occurrence amount).event := by
  refine ⟨rfl, ?_, rfl⟩
  intro role value supplied
  cases role <;> simp_all [refundClause, refundEvent, refundRoles]

/-- The satisfying event is read from the compensator's actual retained
effect history. A method name or an unacknowledged intention supplies no event. -/
theorem compensation_fulfills_treaty_from_actual_history (remote : Remote)
    (occurrence amount : Nat) (fresh : remote.accepted.lookup occurrence = none)
    (notRefunded : occurrence ∉ remote.refunded) (notIrreversible : occurrence ∉ remote.irreversible)
    (positive : 0 < amount) (funded : amount ≤ remote.balance) :
    obligationFulfilled (refundClause amount)
      (treatyTrace (((remote.accept occurrence amount true).2.compensate occurrence amount).2.history)) := by
  have post := compensation_restores_balance_and_retains_history remote occurrence amount
    fresh notRefunded notIrreversible positive funded
  apply obligationFulfilled_of_event (te := refundEvent occurrence amount) rfl
  · apply List.mem_filterMap.mpr
    refine ⟨.refund occurrence amount, ?_, rfl⟩
    rw [post.2.2.1]
    simp
  · exact actual_refund_matches_clause occurrence amount
  · simp [occursWithin, refundClause]

namespace Controls

def grants : List (Grant Nat Nat) :=
  AttemptIdentity.DurableDuty.Controls.grants 1 3 ++ AttemptIdentity.DurableDuty.Controls.grants 3 3

def setup (reversible : Bool) : Service :=
  serviceRun (initialService 10 reversible)
    [.issue grants 1 2 3 2 2, .transfer grants 1 0 3]

def intended (reversible : Bool) : Service := serviceStep (setup reversible) (.reserve grants 3 0 .primary)
def dispatched (reversible : Bool) : Service := serviceStep (intended reversible) (.dispatch grants 3 0 .primary)
def accepted (reversible : Bool) : Service := serviceStep (dispatched reversible) .acceptRemote
def persisted (reversible : Bool) : Service := serviceStep (accepted reversible) .persistCompletion
def adopted : Service := serviceStep (persisted true) (.adopt grants 3 0 .primary)

def phase (service : Service) (purpose : Purpose) : Option (Supervision.Phase Receipt String) :=
  (service.ledger.rows[0]?).map fun row => (row.task purpose).task.phase

def disposition (service : Service) : Option (Option (Disposition Nat Nat Receipt)) :=
  (service.ledger.rows[0]?).map Row.disposition

def repairCommands : List Command :=
  [.cancel 0, .crash, .reserve grants 3 0 .repair, .dispatch grants 3 0 .repair,
    .acceptRemote, .persistCompletion, .adopt grants 3 0 .repair]

def compensated : Service := serviceRun (accepted true) repairCommands
def uncompensated : Service := serviceRun (accepted false) repairCommands

def repairIntended : Service := serviceRun (accepted true)
  [.cancel 0, .crash, .reserve grants 3 0 .repair]
def repairDispatched : Service := serviceStep repairIntended (.dispatch grants 3 0 .repair)
def repairAccepted : Service := serviceStep repairDispatched .acceptRemote
def repairPersisted : Service := serviceStep repairAccepted .persistCompletion
def repairRecovered : Service := serviceStep (repairAccepted.crash.reconcile 0 .repair)
  (.adopt grants 3 0 .repair)

theorem actual_issued_metadata_matches_treaty_and_transferred_holder :
    ((setup true).ledger.rows[0]?).map Row.origin = some (Descriptor.fromClause 0 (refundClause 3)) ∧
      ((setup true).ledger.rows[0]?).map Row.holder = some 3 := by decide

theorem intention_and_dispatch_are_not_remote_acceptance :
    phase (intended true) .primary = some .active ∧
      (intended true).remote.balance = 10 ∧ (intended true).remote.history = [] ∧
      (dispatched true).pending.length = 1 ∧ (dispatched true).remote.balance = 10 ∧
      (serviceStep (dispatched true) (.dispatch grants 3 0 .primary)).pending.length = 1 := by decide

theorem remote_acceptance_precedes_completion_persistence :
    (accepted true).remote.balance = 7 ∧
      (accepted true).remote.history = [.debit 0 3] ∧
      phase (accepted true) .primary = some .active ∧
      phase (persisted true) .primary = some (.terminal (.completed (.value ⟨0, 3, .primary⟩))) ∧
      disposition (persisted true) = some none := by decide

theorem every_crash_window_retains_the_correct_supervision_phase :
    phase (setup true).crash .primary = some .ready ∧
      phase (intended true).crash .primary = some .uncertain ∧
      phase (dispatched true).crash .primary = some .uncertain ∧
      (dispatched true).crash.pending.length = 1 ∧
      phase (accepted true).crash .primary = some .uncertain ∧
      (accepted true).crash.remote.balance = 7 ∧
      phase (persisted true).crash .primary = some (.terminal (.completed (.value ⟨0, 3, .primary⟩))) ∧
      disposition adopted.crash = disposition adopted := by decide

theorem missing_acknowledgement_is_not_failure :
    (intended true).crash.ledger = (accepted true).crash.ledger ∧
      (intended true).crash.remote.balance = 10 ∧ (accepted true).crash.remote.balance = 7 ∧
      ((intended true).crash.reconcile 0 .primary) = (intended true).crash ∧
      phase ((accepted true).crash.reconcile 0 .primary) .primary =
        some (.terminal (.completed (.value ⟨0, 3, .primary⟩))) := by decide

theorem no_local_ledger_function_decides_remote_acceptance :
    ¬ ∃ readBalance : Ledger Nat Nat Receipt String → Nat,
      readBalance (intended true).crash.ledger = (intended true).crash.remote.balance ∧
      readBalance (accepted true).crash.ledger = (accepted true).crash.remote.balance := by
  rintro ⟨readBalance, before, after⟩
  rw [← missing_acknowledgement_is_not_failure.1] at after
  have contradictory := before.symm.trans after
  cases contradictory

def lateAccepted : Service := serviceStep (dispatched true).crash .acceptRemote
def latePersisted : Service := serviceStep lateAccepted .persistCompletion

theorem late_ordinary_reply_requires_reconciliation :
    latePersisted.remote.balance = 7 ∧ phase latePersisted .primary = some .uncertain ∧
      phase (latePersisted.reconcile 0 .primary) .primary =
        some (.terminal (.completed (.value ⟨0, 3, .primary⟩))) := by decide

theorem revocation_blocks_adoption_and_retains_actual_effect :
    serviceStep (persisted true) (.adopt [] 3 0 .primary) = persisted true ∧
      (serviceStep adopted (.cancel 0)).remote = adopted.remote ∧
      disposition (serviceStep adopted (.cancel 0)) = disposition adopted ∧
      phase adopted.crash .primary = some (.terminal (.completed (.value ⟨0, 3, .primary⟩))) := by decide

theorem actual_compensation_restores_funds_and_records_authorized_repair :
    compensated.remote.balance = 10 ∧
      compensated.remote.history = [.debit 0 3, .refund 0 3] ∧
      disposition compensated = some (some ⟨3, .repair, 1, ⟨0, 3, .repair⟩, grants⟩) ∧
      phase compensated .primary = some .uncertain ∧
      phase compensated .repair = some (.terminal (.completed (.value ⟨0, 3, .repair⟩))) ∧
      (compensated.ledger.rows[0]?).map (fun row => row.repair.task.acknowledged) = some true := by decide

theorem compensation_replay_neither_refunds_twice_nor_reopens_reservation :
    compensated.remote.compensate 0 3 = (.value ⟨0, 3, .repair⟩, compensated.remote) ∧
      (compensated.remote.accept 0 3 true).2 = compensated.remote ∧
      (Receipt.mk 0 3 .primary).valid compensated.remote = false ∧
      (Receipt.mk 0 3 .repair).valid compensated.remote = true := by decide

theorem compensation_crash_windows_reconcile_without_repeating_refund :
    phase repairIntended.crash .repair = some .uncertain ∧ repairIntended.crash.remote.balance = 7 ∧
      phase repairDispatched.crash .repair = some .uncertain ∧ repairDispatched.crash.pending.length = 1 ∧
      phase repairAccepted.crash .repair = some .uncertain ∧ repairAccepted.crash.remote.balance = 10 ∧
      repairAccepted.crash.remote.history = [.debit 0 3, .refund 0 3] ∧
      phase repairPersisted.crash .repair = some (.terminal (.completed (.value ⟨0, 3, .repair⟩))) ∧
      disposition repairRecovered = disposition compensated ∧
      repairRecovered.remote.history = [.debit 0 3, .refund 0 3] ∧
      disposition repairRecovered.crash = disposition compensated := by
  decide +kernel

theorem compensated_effect_fulfills_declared_treaty :
    obligationFulfilled (refundClause 3) (treatyTrace compensated.remote.history) := by
  apply obligationFulfilled_of_event (te := refundEvent 0 3) rfl
  · change refundEvent 0 3 ∈ [refundEvent 0 3]
    simp
  · exact actual_refund_matches_clause 0 3
  · simp [occursWithin, refundClause]

theorem irreversible_or_unresolved_never_becomes_compensated :
    uncompensated.remote.balance = 7 ∧ uncompensated.remote.history = [.debit 0 3] ∧
      phase uncompensated .repair = some (.terminal (.completed (.raised "irreversible-effect"))) ∧
      disposition uncompensated = some none ∧
      phase (serviceStep uncompensated (.abandon 0 .primary)) .primary = some (.terminal .unresolved) ∧
      disposition (serviceStep uncompensated (.abandon 0 .primary)) = some none := by decide

theorem irreversible_has_no_refund_treaty_event :
    ¬ obligationFulfilled (refundClause 3) (treatyTrace uncompensated.remote.history) := by
  change ¬ (Core.DeonticModality.obligatory = .obligatory ∧
    eventOccursBy (refundClause 3).eventPattern (refundClause 3).deadline [])
  simp [eventOccursBy]

end Controls

#print axioms compensation_restores_balance_and_retains_history
#print axioms compensation_replay_is_inert
#print axioms irreversible_effect_refuses_compensation
#print axioms serviceStep_lawful
#print axioms service_run_duty_conservation
#print axioms Service.changed_adoption_has_remote_evidence
#print axioms Service.crash_preserves_external_effects
#print axioms Service.cancellation_preserves_external_effects
#print axioms Service.dispatch_preserves_external_effects
#print axioms compensation_fulfills_treaty_from_actual_history
#print axioms Controls.actual_issued_metadata_matches_treaty_and_transferred_holder
#print axioms Controls.intention_and_dispatch_are_not_remote_acceptance
#print axioms Controls.remote_acceptance_precedes_completion_persistence
#print axioms Controls.every_crash_window_retains_the_correct_supervision_phase
#print axioms Controls.missing_acknowledgement_is_not_failure
#print axioms Controls.no_local_ledger_function_decides_remote_acceptance
#print axioms Controls.late_ordinary_reply_requires_reconciliation
#print axioms Controls.revocation_blocks_adoption_and_retains_actual_effect
#print axioms Controls.actual_compensation_restores_funds_and_records_authorized_repair
#print axioms Controls.compensation_replay_neither_refunds_twice_nor_reopens_reservation
#print axioms Controls.compensation_crash_windows_reconcile_without_repeating_refund
#print axioms Controls.compensated_effect_fulfills_declared_treaty
#print axioms Controls.irreversible_or_unresolved_never_becomes_compensated
#print axioms Controls.irreversible_has_no_refund_treaty_event

/-! ## Retained settlement and current publication

The local service, policy and receiver observation are separate captured
coordinates. A successful query computes the existing `Service.adopt`; neither
a caller-supplied disposition nor a completed handler reply supplies authority.
Receiver authenticity and the native decoding of these coordinates remain
service assumptions. Read invoices below count logical observations, not Rho
steps, payload work, journal synchronization or physical service latency.
-/

namespace RetainedSettlement

open Mettapedia.Machines
open Mettapedia.GSLT.LanguageDef.OperationCostProtocol
open Mettapedia.GSLT.LanguageDef.OperationCostProtocol.Indexed
open Mettapedia.TypeTheory.IndexedPolynomial

structure Keys where
  localState : Nat
  policy : Nat
  receiver : Nat
  deriving DecidableEq, Repr

structure Request where
  actor : Nat
  occurrence : Nat
  purpose : Purpose
  deriving DecidableEq, Repr

inductive Cell where
  | absent
  | localState (service : Service)
  | policy (grants : List (Grant Nat Nat))
  | receiver (remote : Remote)
  deriving DecidableEq

inductive Refused where
  | localState | policy | receiver | changedReceiver | notAdopted
  deriving DecidableEq, Repr

structure Plan where
  before : Service
  authority : List (Grant Nat Nat)
  receiver : Remote
  after : Service
  deriving DecidableEq

abbrev Readout := Except Refused Plan
abbrev Store := Nat → Cell

/-- The receiver observation must agree with the service view used by its
semantic checker. The actual adopter then checks the task, direction, holder,
current application grant and receipt meaning. Refusal is an explicit reply. -/
def prepare (request : Request) (service : Service)
    (grants : List (Grant Nat Nat)) (receiver : Remote) : Readout :=
  if receiver = service.remote then
    let after := service.adopt grants request.actor request.occurrence request.purpose
    if after = service then .error .notAdopted
    else .ok ⟨service, grants, receiver, after⟩
  else .error .changedReceiver

def query (keys : Keys) (request : Request) : ReadOnlyQuery.Program Nat Cell Readout :=
  .read keys.localState fun stored => match stored with
    | .localState service => .read keys.policy fun policy => match policy with
      | .policy grants => .read keys.receiver fun evidence => match evidence with
        | .receiver remote => .pure (prepare request service grants remote)
        | _ => .pure (.error .receiver)
      | _ => .pure (.error .policy)
    | _ => .pure (.error .localState)

def writes (keys : Keys) : Readout → ValidatedCommit.Writes Nat Cell
  | .error _ => []
  | .ok plan => [(keys.localState, .localState plan.after)]

def transaction (keys : Keys) (request : Request) : ValidatedCommit.Transaction Nat Cell :=
  ReadOnlyQuery.map (writes keys) (query keys request)

theorem transaction_readout (snapshot : Store) (keys : Keys) (request : Request) :
    ReadOnlyQuery.run snapshot (transaction keys request) =
      ⟨writes keys (ReadOnlyQuery.run snapshot (query keys request)).answer,
        (ReadOnlyQuery.run snapshot (query keys request)).reads⟩ :=
  ReadOnlyQuery.run_map snapshot (query keys request) (writes keys)

theorem prepare_ok (request : Request) (service : Service)
    (grants : List (Grant Nat Nat)) (receiver : Remote) (plan : Plan)
    (accepted : prepare request service grants receiver = .ok plan) :
    plan.before = service ∧ plan.authority = grants ∧ plan.receiver = receiver ∧
      receiver = service.remote ∧
      plan.after = service.adopt grants request.actor request.occurrence request.purpose ∧
      plan.after ≠ service := by
  unfold prepare at accepted
  split at accepted
  · rename_i agrees
    dsimp only at accepted
    split at accepted
    · cases accepted
    · rename_i changed
      cases accepted
      exact ⟨rfl, rfl, rfl, agrees, rfl, changed⟩
  · cases accepted

/-- All successful local, policy and receiver dependencies are recovered
from the actual adaptive query, including its computed service transition. -/
theorem query_ok (snapshot : Store) (keys : Keys) (request : Request) (plan : Plan)
    (accepted : (ReadOnlyQuery.run snapshot (query keys request)).answer = .ok plan) :
    snapshot keys.localState = .localState plan.before ∧
      snapshot keys.policy = .policy plan.authority ∧
      snapshot keys.receiver = .receiver plan.receiver ∧
      plan.receiver = plan.before.remote ∧
      plan.after = plan.before.adopt plan.authority request.actor request.occurrence request.purpose ∧
      plan.after ≠ plan.before := by
  cases stored : snapshot keys.localState <;>
    simp [query, ReadOnlyQuery.run, stored] at accepted
  rename_i service
  cases policy : snapshot keys.policy <;>
    simp [policy, ReadOnlyQuery.run] at accepted
  rename_i grants
  cases receiver : snapshot keys.receiver <;>
    simp [receiver, ReadOnlyQuery.run] at accepted
  rename_i remote
  obtain ⟨before, authority, evidence, agrees, after, changed⟩ :=
    prepare_ok request service grants remote plan accepted
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [before]
  · rw [authority]
  · rw [evidence]
  · rw [evidence, before]; exact agrees
  · rw [before, authority]; exact after
  · intro same
    exact changed (same.trans before)

/-- The semantic receiver check is inherited from the real adopter, rather
than from the plan's printed fields or a claimed success bit. -/
theorem successful_query_has_receiver_evidence
    (snapshot : Store) (keys : Keys) (request : Request) (plan : Plan)
    (accepted : (ReadOnlyQuery.run snapshot (query keys request)).answer = .ok plan) :
    ∃ row receipt, plan.before.ledger.rows[request.occurrence]? = some row ∧
      (row.task request.purpose).task.phase = .terminal (.completed (.value receipt)) ∧
      receipt.valid plan.receiver = true ∧ direction row.cancelled request.purpose = true := by
  obtain ⟨_, _, _, receiver, after, changed⟩ := query_ok snapshot keys request plan accepted
  have adopted := plan.before.changed_adoption_has_remote_evidence
    plan.authority request.actor request.occurrence request.purpose
    (by simpa only [after] using changed)
  simpa only [receiver] using adopted

theorem successful_query_lawful (snapshot : Store) (keys : Keys) (request : Request) (plan : Plan)
    (accepted : (ReadOnlyQuery.run snapshot (query keys request)).answer = .ok plan)
    (lawful : Lawful meaning plan.before.ledger) : Lawful meaning plan.after.ledger := by
  rw [(query_ok snapshot keys request plan accepted).2.2.2.2.1]
  exact plan.before.adopt_lawful plan.authority request.actor request.occurrence request.purpose lawful

abbrev source (snapshot : Store) := Cursor.ReadOnlyQuery.provider snapshot
abbrev reader := Cursor.ReadOnlyQuery.client (Key := Nat) (Value := Cell) (Answer := Readout)
abbrev Gate (snapshot : Store) := Indexed.Gate (Denied := Refused) (source snapshot)
abbrev Notice := Indexed.Notice (Cursor.ReadOnlyQuery.protocol Nat Cell) Refused

def readProfile : Profile :=
  ⟨"duty-settlement-read", [("observation", some .quantum)], .steps, none, .transparent⟩

/-- The invoice origin distinguishes this logical account. It carries no
permission, service generation, receiver authentication or physical bound. -/
def invoice (snapshot : Store) (origin : Nat) : Indexed.Invoice (source snapshot) :=
  fun reads _ => [(reads.length, ⟨origin, reads.length, .quantum, 1⟩)]

abbrev Invocation (snapshot : Store) (gate : Gate snapshot) (origin : Nat) (notice : Notice) :=
  Indexed.Invocation (Key := Nat) (Value := Cell) (source snapshot) gate
    (fun _ => readProfile) (fun _ => false) (invoice snapshot origin) reader notice .unit

abbrev Packet (snapshot : Store) (gate : Gate snapshot) (origin : Nat) (notice : Notice) :=
  Cursor.Packet (Indexed.provider (source snapshot) gate
    (fun _ => readProfile) (fun _ => false) (invoice snapshot origin))
    (Indexed.client reader notice) .unit

abbrev Outcome (snapshot : Store) (gate : Gate snapshot) (origin : Nat) (notice : Notice) :=
  Indexed.Outcome (source snapshot) gate (fun _ => readProfile) (fun _ => false)
    (invoice snapshot origin) reader notice .unit

def pendingProgram : Indexed.Control (Denied := Refused) reader .unit .unit →
    ReadOnlyQuery.Program Nat Cell Readout
  | .inl program => program
  | .inr (_, program) => program

def residualObservation (snapshot : Store)
    (control : Indexed.Control (Denied := Refused) reader .unit .unit)
    (reads : ReadOnlyQuery.Reads Nat Cell) : ReadOnlyQuery.Observation Nat Cell Readout :=
  let rest := ReadOnlyQuery.run snapshot (pendingProgram control)
  ⟨rest.answer, reads.reverse ++ rest.reads⟩

/-- This is a mathematical observation of the retained residual. Only the
ordinary terminal branch exposes a result to a caller. A refused or paused
query retains its exact program and already acquired read occurrences. -/
def observation (snapshot : Store) {gate : Gate snapshot} {origin : Nat} {notice : Notice} :
    Outcome snapshot gate origin notice → ReadOnlyQuery.Observation Nat Cell Readout
  | .paused ⟨.unit, control, state⟩ => residualObservation snapshot control state.1
  | .done ⟨.unit, .inl value, state⟩ => ⟨value, state.1.reverse⟩
  | .done ⟨.unit, .inr (_, program), state⟩ =>
      residualObservation snapshot (.inl program) state.1

set_option backward.isDefEq.respectTransparency false in
/-- Local read/admission/reply transitions prove the full residual law.
There is no premise asserting equality of completed handler runs. -/
theorem run_observation (snapshot : Store) (gate : Gate snapshot) (origin : Nat)
    (notice : Notice) (fuel : Nat) (packet : Packet snapshot gate origin notice) :
    observation snapshot
      (Indexed.run (source snapshot) gate (fun _ => readProfile) (fun _ => false)
        (invoice snapshot origin) reader notice fuel packet).2 =
      residualObservation snapshot packet.2.1 packet.2.2.1 := by
  induction fuel generalizing packet with
  | zero => rfl
  | succ fuel ih =>
      rcases packet with ⟨⟨⟩, control, reads, account⟩
      cases control with
      | inr refused =>
          rcases refused with ⟨reason, program⟩
          rfl
      | inl program =>
          cases program with
          | pure answer => simp [Indexed.run, Cursor.advance, Indexed.client, Indexed.expose,
              reader, Cursor.ReadOnlyQuery.client, observation, residualObservation, pendingProgram,
              ReadOnlyQuery.run]
          | read key next =>
              have head := Indexed.client_call reader notice
                (base := .unit) (index := .unit) (.read key next) key next rfl
              cases admitted : Indexed.admit (source snapshot) gate
                  (fun _ => readProfile) (fun _ => false) (invoice snapshot origin)
                  (base := .unit) (index := .unit) reads key account with
              | error reason =>
                  unfold Indexed.run
                  rw [Cursor.advance.eq_def]
                  dsimp only
                  rw [head]
                  dsimp only [withHoles]
                  rw [(Indexed.refused_step (source snapshot) gate
                    (fun _ => readProfile) (fun _ => false) (invoice snapshot origin)
                    (reads, account) key reason admitted).1]
                  exact ih ⟨.unit, .inr (reason, .read key next), reads, account⟩
              | ok paid =>
                  unfold Indexed.run
                  rw [Cursor.advance.eq_def]
                  dsimp only
                  rw [head]
                  dsimp only [withHoles]
                  rw [(Indexed.accepted_step (source snapshot) gate
                    (fun _ => readProfile) (fun _ => false) (invoice snapshot origin)
                    (reads, account) key paid admitted).1]
                  dsimp only [source, Cursor.ReadOnlyQuery.provider]
                  cases noted : notice key (snapshot key) with
                  | none =>
                      simpa only [Indexed.run, source, Cursor.ReadOnlyQuery.provider, noted,
                        residualObservation, pendingProgram,
                        ReadOnlyQuery.run, List.reverse_cons, List.append_assoc, List.singleton_append]
                        using
                        ih ⟨.unit, .inl (next (snapshot key)), (key, snapshot key) :: reads, paid⟩
                  | some reason =>
                      simpa only [Indexed.run, source, Cursor.ReadOnlyQuery.provider, noted,
                        residualObservation, pendingProgram,
                        ReadOnlyQuery.run, List.reverse_cons, List.append_assoc, List.singleton_append]
                        using
                        ih ⟨.unit, .inr (.inl reason, next (snapshot key)),
                          (key, snapshot key) :: reads, paid⟩

def start (snapshot : Store) (keys : Keys) (request : Request) (gate : Gate snapshot)
    (origin : Nat) (notice : Notice) (account : Account) (fuel : Nat) :
    Invocation snapshot gate origin notice :=
  let executed := Indexed.run (source snapshot) gate (fun _ => readProfile) (fun _ => false)
    (invoice snapshot origin) reader notice fuel
    ⟨.unit, .inl (query keys request), [], account⟩
  ⟨⟨snapshot, transaction keys request⟩, executed.1, executed.2⟩

theorem start_observation (snapshot : Store) (keys : Keys) (request : Request)
    (gate : Gate snapshot) (origin : Nat) (notice : Notice) (account : Account) (fuel : Nat) :
    observation snapshot (start snapshot keys request gate origin notice account fuel).outcome =
      ReadOnlyQuery.run snapshot (query keys request) := by
  simpa [start, residualObservation, pendingProgram] using
    run_observation snapshot gate origin notice fuel
      ⟨.unit, .inl (query keys request), [], account⟩

theorem replaceGate_observation (snapshot : Store) (gate next : Gate snapshot)
    (origin : Nat) (notice : Notice) (outcome : Outcome snapshot gate origin notice) :
    observation snapshot
      (Indexed.replaceGate (source snapshot) gate (fun _ => readProfile) (fun _ => false)
        (invoice snapshot origin) reader notice next outcome) = observation snapshot outcome := by
  cases outcome with
  | paused packet => rcases packet with ⟨⟨⟩, control, state⟩; rfl
  | done result => rcases result with ⟨⟨⟩, value, state⟩; cases value <;> rfl

theorem retry_observation (snapshot : Store) (gate : Gate snapshot) (origin : Nat)
    (notice : Notice) (outcome : Outcome snapshot gate origin notice) :
    observation snapshot
      (Indexed.retry (source snapshot) gate (fun _ => readProfile) (fun _ => false)
        (invoice snapshot origin) reader notice outcome) = observation snapshot outcome := by
  cases outcome with
  | paused packet => rfl
  | done result => rcases result with ⟨⟨⟩, value, state⟩; cases value <;> rfl

theorem resume_observation (snapshot : Store) (gate : Gate snapshot) (origin : Nat)
    (notice : Notice) (fuel spent : Nat) (outcome : Outcome snapshot gate origin notice) :
    observation snapshot
      (Indexed.resume (source snapshot) gate (fun _ => readProfile) (fun _ => false)
        (invoice snapshot origin) reader notice fuel (spent, outcome)).2 = observation snapshot outcome := by
  cases outcome with
  | done result => rfl
  | paused packet => exact run_observation snapshot gate origin notice fuel packet

/-- Changing the current checker and explicitly rearming a refusal preserves
the original query meaning and all prior ordered read occurrences. -/
theorem resumeWith_observation (snapshot : Store) (gate next : Gate snapshot)
    (origin : Nat) (notice : Notice) (held : Invocation snapshot gate origin notice) (fuel : Nat) :
    observation snapshot
      (held.resumeWith (source snapshot) gate (fun _ => readProfile) (fun _ => false)
        (invoice snapshot origin) reader notice next fuel).outcome =
      observation snapshot held.outcome := by
  rw [Indexed.Invocation.resumeWith]
  dsimp only
  rw [resume_observation, retry_observation]
  exact replaceGate_observation snapshot gate next origin notice held.outcome

/-- Reachability records only the existing invocation constructors. Correct
readout and publication are theorems of these transitions, not constructor
premises or a supplied complete-run equivalence. -/
inductive Executed (snapshot : Store) (keys : Keys) (request : Request)
    (origin : Nat) (notice : Notice) (account : Account) :
    {gate : Gate snapshot} → Invocation snapshot gate origin notice → Prop
  | start (gate : Gate snapshot) (fuel : Nat) :
      @Executed snapshot keys request origin (@notice) account (@gate)
        (RetainedSettlement.start snapshot keys request gate origin notice account fuel)
  | resume {gate : Gate snapshot} {held : Invocation snapshot gate origin notice}
      (previous : @Executed snapshot keys request origin (@notice) account (@gate) held)
      (next : Gate snapshot) (fuel : Nat) :
      @Executed snapshot keys request origin (@notice) account (@next)
        (held.resumeWith (source snapshot) gate (fun _ => readProfile) (fun _ => false)
          (invoice snapshot origin) reader notice next fuel)

theorem Executed.submission {snapshot : Store} {keys : Keys} {request : Request}
    {origin : Nat} {notice : Notice} {account : Account} {gate : Gate snapshot}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held) :
    held.submission = (snapshot, transaction keys request) := by
  induction executed with
  | start => rfl
  | resume previous next fuel ih =>
      exact (Indexed.Invocation.resumeWith_submission ..).trans ih

theorem Executed.observation {snapshot : Store} {keys : Keys} {request : Request}
    {origin : Nat} {notice : Notice} {account : Account} {gate : Gate snapshot}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held) :
    observation snapshot held.outcome = ReadOnlyQuery.run snapshot (query keys request) := by
  induction executed with
  | start gate fuel => exact start_observation snapshot keys request gate origin notice account fuel
  | resume previous next fuel ih => exact (resumeWith_observation ..).trans ih

theorem Executed.terminal_readout {snapshot : Store} {keys : Keys} {request : Request}
    {origin : Nat} {notice : Notice} {account : Account} {gate : Gate snapshot}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (value : Readout) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl value, state⟩) :
    value = (ReadOnlyQuery.run snapshot (query keys request)).answer := by
  have same := congrArg ReadOnlyQuery.Observation.answer executed.observation
  simpa only [finished, RetainedSettlement.observation] using same

/-- The terminal-write witness is constructed from the actual retained run
and the independent adaptive-query interpreter. Refusals cannot provide a
terminal original reply. -/
theorem Executed.ready {snapshot : Store} {keys : Keys} {request : Request}
    {origin : Nat} {notice : Notice} {account : Account} {gate : Gate snapshot}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (value : Readout) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl value, state⟩) :
    Indexed.Invocation.Ready (source := source snapshot) (gate := gate)
      (profiles := fun _ => readProfile) (replay := fun _ => false)
      (invoice := invoice snapshot origin) (reader := reader) (notice := notice)
      (fun {_} answer => writes keys answer) held := by
  refine ⟨.unit, value, state, finished, ?_⟩
  rw [executed.submission]
  simp only [transaction_readout]
  exact congrArg (writes keys) (executed.terminal_readout value state finished)

/-- Paid progress is accounted independently of current permission and the
application's eventual semantic settlement. Installing a new checker cannot
refund an already executed observation or duplicate its invoice. -/
theorem resumeWith_account (snapshot : Store) (gate next : Gate snapshot)
    (origin : Nat) (notice : Notice) (held : Invocation snapshot gate origin notice) (fuel : Nat) :
    let later := held.resumeWith (source snapshot) gate (fun _ => readProfile) (fun _ => false)
      (invoice snapshot origin) reader notice next fuel
    later.account.remaining + later.spent = held.account.remaining + held.spent ∧
      work later.account.events + held.spent = work held.account.events + later.spent ∧
      allowanceTotal later.account = allowanceTotal held.account :=
  Indexed.Invocation.resumeWith_account ..

open _root_.CategoryTheory
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone (Handle)

variable {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
  {Provider Resource : Type} [DecidableEq Provider] [DecidableEq Resource]

/-- Only an actual successful settlement readout reaches publication. The
current host grant and its generation are checked independently of the
versioned application grants read by the query. -/
def publish {snapshot : Store} {keys : Keys} {request : Request}
    {origin : Nat} {notice : Notice} {account : Account} {gate : Gate snapshot}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (plan : Plan) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl (.ok plan), state⟩)
    (history : NativePoll.History) (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (handle : Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)]
    (denied : Refused) (current : Store) :=
  held.publishCheckedGrant (source snapshot) gate (fun _ => readProfile) (fun _ => false)
    (invoice snapshot origin) reader notice (fun {_} answer => writes keys answer)
    (executed.ready (.ok plan) state finished) history authority point requirement handle denied current

/-- Exact current-generation publication validates the complete read path,
including policy and receiver observations. This proof follows the actual
publication branches; a success tag alone cannot supply freshness. -/
theorem publish_validates {snapshot : Store} {keys : Keys} {request : Request}
    {origin : Nat} {notice : Notice} {account : Account} {gate : Gate snapshot}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (plan : Plan) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl (.ok plan), state⟩)
    (history : NativePoll.History) (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (handle : Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)]
    (denied : Refused) (current next : Store)
    (accepted : publish executed plan state finished history authority point requirement handle denied current =
      .committed next history) :
    ReadOnlyQuery.checkReads current (ReadOnlyQuery.run snapshot (query keys request)).reads = true := by
  unfold publish Indexed.Invocation.publishCheckedGrant at accepted
  split at accepted
  · unfold Indexed.Invocation.publishCurrent at accepted
    split at accepted
    · cases committed : ValidatedCommit.commit current
          (ValidatedCommit.propose held.submission.1 held.submission.2) with
      | none => simp [committed] at accepted
      | some actual =>
          have valid : ReadOnlyQuery.checkReads current
              (ReadOnlyQuery.run held.submission.1 held.submission.2).reads = true := by
            unfold ValidatedCommit.commit ValidatedCommit.propose at committed
            split at committed
            · assumption
            · cases committed
          rw [executed.submission] at valid
          simpa only [transaction_readout] using valid
    · cases accepted
  · cases accepted

theorem publish_current_readout {snapshot : Store} {keys : Keys} {request : Request}
    {origin : Nat} {notice : Notice} {account : Account} {gate : Gate snapshot}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (plan : Plan) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl (.ok plan), state⟩)
    (history : NativePoll.History) (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (handle : Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)]
    (denied : Refused) (current next : Store)
    (accepted : publish executed plan state finished history authority point requirement handle denied current =
      .committed next history) :
    (ReadOnlyQuery.run current (query keys request)).answer = .ok plan :=
  (ReadOnlyQuery.validated_answer snapshot current (query keys request)
    (publish_validates executed plan state finished history authority point requirement handle denied
      current next accepted)).trans (executed.terminal_readout (.ok plan) state finished).symm

theorem query_ok_reads (snapshot : Store) (keys : Keys) (request : Request) (plan : Plan)
    (accepted : (ReadOnlyQuery.run snapshot (query keys request)).answer = .ok plan) :
    (ReadOnlyQuery.run snapshot (query keys request)).reads =
      [(keys.localState, .localState plan.before), (keys.policy, .policy plan.authority),
        (keys.receiver, .receiver plan.receiver)] := by
  obtain ⟨stored, policy, receiver, _⟩ := query_ok snapshot keys request plan accepted
  simp [query, ReadOnlyQuery.run, stored, policy, receiver]

theorem adopt_preserves_receiver (service : Service) (grants : List (Grant Nat Nat))
    (actor occurrence : Nat) (purpose : Purpose) :
    (service.adopt grants actor occurrence purpose).remote = service.remote := by
  unfold Service.adopt
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-- Publication keeps the exact host generation and reads the current local
service, application authority and receiver state. It commits the actual
adoption computed from those values, with no new receiver effect. -/
theorem publish_fresh {snapshot : Store} {keys : Keys} {request : Request}
    {origin : Nat} {notice : Notice} {account : Account} {gate : Gate snapshot}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (plan : Plan) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl (.ok plan), state⟩)
    (history : NativePoll.History) (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (handle : Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)]
    (denied : Refused) (current next : Store)
    (accepted : publish executed plan state finished history authority point requirement handle denied current =
      .committed next history) :
    requirement.handle = handle ∧ FrameUpdate point.authority requirement.required ∧
      current keys.localState = .localState plan.before ∧
      current keys.policy = .policy plan.authority ∧
      current keys.receiver = .receiver plan.receiver ∧
      next keys.localState = .localState plan.after ∧
      plan.after = plan.before.adopt plan.authority request.actor request.occurrence request.purpose ∧
      plan.after ≠ plan.before ∧ plan.after.remote = plan.before.remote := by
  have original := Indexed.Invocation.publishCheckedGrant_fresh
    (source snapshot) gate (fun _ => readProfile) (fun _ => false)
    (invoice snapshot origin) reader notice (fun {_} answer => writes keys answer)
    held (executed.ready (.ok plan) state finished) history authority point requirement handle denied
    current next accepted
  have currentAnswer := publish_current_readout executed plan state finished history authority point
    requirement handle denied current next accepted
  obtain ⟨stored, policy, receiver, _, adopted, changed⟩ := query_ok current keys request plan currentAnswer
  have written : next keys.localState = .localState plan.after := by
    rw [original.2.2.1, executed.submission, transaction_readout, currentAnswer]
    simp [writes, ValidatedCommit.write]
  exact ⟨original.1, original.2.1, stored, policy, receiver, written, adopted, changed,
    adopted ▸ adopt_preserves_receiver plan.before plan.authority request.actor request.occurrence request.purpose⟩

/-- Every effective published disposition has a current successful attempt
and actual receiver evidence. Cancellation/restart uncertainty cannot be
reinterpreted as a completed answer by the handler or publication layer. -/
theorem publish_has_receiver_evidence {snapshot : Store} {keys : Keys} {request : Request}
    {origin : Nat} {notice : Notice} {account : Account} {gate : Gate snapshot}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (plan : Plan) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl (.ok plan), state⟩)
    (history : NativePoll.History) (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (handle : Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)]
    (denied : Refused) (current next : Store)
    (accepted : publish executed plan state finished history authority point requirement handle denied current =
      .committed next history) :
    ∃ row receipt, plan.before.ledger.rows[request.occurrence]? = some row ∧
      (row.task request.purpose).task.phase = .terminal (.completed (.value receipt)) ∧
      receipt.valid plan.receiver = true ∧ direction row.cancelled request.purpose = true :=
  successful_query_has_receiver_evidence current keys request plan
    (publish_current_readout executed plan state finished history authority point requirement handle denied
      current next accepted)

/-- Actual current-state adoption preserves all issued duties and their
unique custody/disposition. The conservation premise is the source ledger's
invariant, discharged for arbitrary real service runs by `serviceRun_lawful`. -/
theorem publish_duty_conservation {snapshot : Store} {keys : Keys} {request : Request}
    {origin : Nat} {notice : Notice} {account : Account} {gate : Gate snapshot}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (plan : Plan) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl (.ok plan), state⟩)
    (history : NativePoll.History) (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (handle : Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)]
    (denied : Refused) (current next : Store)
    (accepted : publish executed plan state finished history authority point requirement handle denied current =
      .committed next history)
    (lawful : Lawful meaning plan.before.ledger) (occurrence : Nat)
    (issued : occurrence < plan.after.ledger.issued.length) :
    (plan.after.ledger.rows.map fun row => row.origin.occurrence).count occurrence = 1 ∧
      ∃ row ∈ plan.after.ledger.rows, row.origin.occurrence = occurrence ∧
        Ownership row.origin row.transfers row.holder ∧
        (row.disposition = none ∨
          ∃ receipt, row.disposition = some receipt ∧ row.AuthorizedDisposition meaning receipt) := by
  apply lawful_duty_conservation meaning _ _ occurrence issued
  exact successful_query_lawful current keys request plan
    (publish_current_readout executed plan state finished history authority point requirement handle denied
      current next accepted) lawful

/-- Restoring equal rights at a different host-grant generation cannot revive
a retained settlement. Its entire paid invocation and history are returned. -/
theorem publish_stale_generation {snapshot : Store} {keys : Keys} {request : Request}
    {origin : Nat} {notice : Notice} {account : Account} {gate : Gate snapshot}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (plan : Plan) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl (.ok plan), state⟩)
    (history : NativePoll.History) (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (handle : Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)]
    (denied : Refused) (current : Store) (stale : requirement.handle ≠ handle) :
    publish executed plan state finished history authority point requirement handle denied current =
      .authorityRefused denied held history := by
  exact Indexed.Invocation.publishCheckedGrant_stale (source snapshot) gate
    (fun _ => readProfile) (fun _ => false) (invoice snapshot origin) reader notice
    (fun {_} answer => writes keys answer) held (executed.ready (.ok plan) state finished)
    history authority point requirement handle denied current stale

section Handler

variable {snapshot : Store} {gate : Gate snapshot} {origin : Nat}
  {target : Cursor.Provider (Cursor.ReadOnlyQuery.protocol Nat Cell)}
  {targetGate : Indexed.Gate (Denied := Refused) target}
  {targetInvoice : Indexed.Invoice target}
  (handler : Indexed.HandlerHom (source snapshot) target gate targetGate
    (fun _ => readProfile) (fun _ => readProfile) (fun _ => false) (fun _ => false)
    (invoice snapshot origin) targetInvoice)

/-- A different handler representation carries the same actual duty result,
submission and account. Its local protocol/invoice laws are supplied by the
existing `HandlerHom`; no agreement of complete runs is an input. -/
def publishVia {keys : Keys} {request : Request}
    {notice : Notice} {account : Account}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (plan : Plan) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl (.ok plan), state⟩)
    (history : NativePoll.History) (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (handle : Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)]
    (denied : Refused) (current : Store) :=
  (handler.invocation reader notice held).publishCheckedGrant target targetGate
    (fun _ => readProfile) (fun _ => false) targetInvoice reader notice
    (fun {_} answer => writes keys answer)
    (handler.invocation_ready reader notice (fun {_} answer => writes keys answer) held
      (executed.ready (.ok plan) state finished))
    history authority point requirement handle denied current

theorem publishVia_commutes {keys : Keys} {request : Request}
    {notice : Notice} {account : Account}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (plan : Plan) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl (.ok plan), state⟩)
    (history : NativePoll.History) (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (handle : Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)]
    (denied : Refused) (current : Store) :
    handler.publication reader notice
      (publish executed plan state finished history authority point requirement handle denied current) =
      publishVia handler executed plan state finished history authority point requirement handle denied current :=
  handler.publishCheckedGrant reader notice (fun {_} answer => writes keys answer)
    held (executed.ready (.ok plan) state finished) history authority point requirement handle denied current

theorem publishVia_committed_iff {keys : Keys} {request : Request}
    {notice : Notice} {account : Account}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (plan : Plan) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl (.ok plan), state⟩)
    (history : NativePoll.History) (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (handle : Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)]
    (denied : Refused) (current next : Store) :
    publishVia handler executed plan state finished history authority point requirement handle denied current =
        .committed next history ↔
      publish executed plan state finished history authority point requirement handle denied current =
        .committed next history := by
  rw [← publishVia_commutes]
  cases publication : publish executed plan state finished history authority point requirement handle denied current <;>
    simp [Indexed.HandlerHom.publication]

/-- Substituting a locally justified handler preserves current-generation
settlement and the actual receiver meaning, including the selected successful
task and direction. It cannot turn a revoked/refused publication into one. -/
theorem publishVia_current_settlement {keys : Keys} {request : Request}
    {notice : Notice} {account : Account}
    {held : Invocation snapshot gate origin notice}
    (executed : Executed snapshot keys request origin notice account held)
    (plan : Plan) (state : ReadOnlyQuery.Reads Nat Cell × Account)
    (finished : held.outcome = .done ⟨.unit, .inl (.ok plan), state⟩)
    (history : NativePoll.History) (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (handle : Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)]
    (denied : Refused) (current next : Store)
    (accepted : publishVia handler executed plan state finished history authority point requirement handle denied current =
      .committed next history) :
    requirement.handle = handle ∧ FrameUpdate point.authority requirement.required ∧
      current keys.policy = .policy plan.authority ∧
      next keys.localState = .localState plan.after ∧
      plan.after = plan.before.adopt plan.authority request.actor request.occurrence request.purpose ∧
      ∃ row receipt, plan.before.ledger.rows[request.occurrence]? = some row ∧
        (row.task request.purpose).task.phase = .terminal (.completed (.value receipt)) ∧
        receipt.valid plan.receiver = true ∧ direction row.cancelled request.purpose = true := by
  have sourceAccepted := (publishVia_committed_iff handler executed plan state finished history
    authority point requirement handle denied current next).1 accepted
  obtain ⟨same, permitted, _, policy, _, written, adopted, _⟩ :=
    publish_fresh executed plan state finished history authority point requirement handle denied current next sourceAccepted
  exact ⟨same, permitted, policy, written, adopted,
    publish_has_receiver_evidence executed plan state finished history authority point requirement handle denied
      current next sourceAccepted⟩

end Handler

end RetainedSettlement

end DurableEscrow

end Mettapedia.Machines.ErrorBoundaryContracts.DispatchPermit
