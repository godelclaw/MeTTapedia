import Std
import Mettapedia.Machines.AsyncWait
import Mettapedia.Machines.AdmissionFrontier
import Mettapedia.Machines.CooperativeQueue

/-!
Adapted from godelclaw/MeTTapedia commit
562e3c8af4be9f2984bf7783eb71771ce9417d2a.

# Owned events, safe suspension and bounded cooperative service

This is an executable contract for the agent integration, not a verification
of Erlang, Tokio, RSpace or the native executor. It borrows owner-local
mailboxes/selective receive, bounded polls with retained pending tasks, and
recorded occurrence identities. Multi-channel matching is in `ChannelJoin`.

* https://www.erlang.org/doc/system/conc_prog.html
* https://docs.rs/tokio/latest/tokio/runtime/index.html
* https://rholang.github.io/docs/rspace-intro/

An accepted event is an immutable journal row with a delivery phase. Claiming
it is distinct from settling it. Recovery can requeue a local claim; it cannot
reopen settlement. Journal/phase changes and effect intentions must be committed
atomically by the host. Wakes are hints: durable readiness and an epoch check
decide whether sleeping is legal. Payloads are opaque natural-number codes.

The scheduling theorem permits arrivals after every quantum. New arrivals
join the tail, and a yielding task also joins the tail. A finite queued prefix
receives service even with continuing arrivals. Wall time additionally requires
an enforced bound for the whole slot, including event/storage/evaluator work.
No result promises provider completion or success of an arbitrary task.
-/

namespace Mettapedia.Machines.EventPump

open CooperativeQueue

abbrev Key := AsyncWait.Identity

structure Event where
  serial : Nat
  owner : Key
  payload : Nat
  deriving DecidableEq, Repr

inductive Delivery where
  | queued | claimed | settled
  deriving DecidableEq, Repr

structure Inbox where
  owner : Key
  journal : List Event := []
  phase : Nat → Option Delivery := fun _ => none
  epoch : Nat := 0
  sleeping : Bool := false
  receipts : List Nat := []

structure WaitTicket where
  owner : Key
  epoch : Nat
  deriving DecidableEq, Repr

def pending (s : Inbox) : List Event :=
  s.journal.filter fun e => decide (s.phase e.serial = some .queued)

def arm (s : Inbox) : WaitTicket := ⟨s.owner, s.epoch⟩

def park (s : Inbox) (ticket : WaitTicket) : Inbox :=
  { s with sleeping := decide (ticket.owner = s.owner ∧
      ticket.epoch = s.epoch ∧ pending s = []) }

def record (s : Inbox) (event : Event) : Inbox :=
  if event.owner = s.owner ∧ s.phase event.serial = none then
    { s with journal := s.journal ++ [event]
             phase := fun id => if id = event.serial then some .queued else s.phase id
             epoch := s.epoch + 1, sleeping := false }
  else s

def claim (s : Inbox) (id : Nat) : Inbox :=
  if s.phase id = some .queued then
    { s with phase := fun other => if other = id then some .claimed else s.phase other
             epoch := s.epoch + 1, sleeping := false }
  else s

def settle (s : Inbox) (id : Nat) : Inbox :=
  if s.phase id = some .claimed then
    { s with phase := fun other => if other = id then some .settled else s.phase other
             epoch := s.epoch + 1, sleeping := false
             receipts := s.receipts ++ [id] }
  else s

def recover (s : Inbox) : Inbox :=
  { s with phase := fun id =>
      if s.phase id = some .claimed then some .queued else s.phase id
           epoch := s.epoch + 1, sleeping := false }

def firstMatching (s : Inbox) (accepts : Event → Bool) : Option Event :=
  (pending s).find? accepts

def receive (s : Inbox) (accepts : Event → Bool) : Inbox :=
  match firstMatching s accepts with
  | none => s
  | some event => claim s event.serial

def accounted (s : Inbox) : Prop :=
  ∀ e ∈ s.journal, s.phase e.serial ≠ none

def owned (s : Inbox) : Prop := ∀ e ∈ s.journal, e.owner = s.owner

def safeSleep (s : Inbox) : Prop := s.sleeping = true → pending s = []

def invariant (s : Inbox) : Prop := accounted s ∧ owned s ∧ safeSleep s

inductive Action where
  | arrival (event : Event)
  | claim (serial : Nat)
  | settle (serial : Nat)
  | park (ticket : WaitTicket)
  | wake
  | recover

def step (s : Inbox) : Action → Inbox
  | .arrival e => record s e
  | .claim id => claim s id
  | .settle id => settle s id
  | .park ticket => park s ticket
  | .wake => { s with sleeping := false }
  | .recover => recover s

def run : List Action → Inbox → Inbox
  | [], s => s
  | a :: rest, s => run rest (step s a)

/-- Logical mailbox ownership does not impose operating-system isolation or
restrict an agent's separately authorized workspace capabilities. -/
def route (mailboxes : Key → Inbox) (target : Key) (action : Action) : Key → Inbox :=
  fun key => if key = target then step (mailboxes key) action else mailboxes key

theorem actor_step_preserves_other_mailboxes (mailboxes : Key → Inbox)
    (target other : Key) (action : Action) (different : other ≠ target) :
    route mailboxes target action other = mailboxes other := by simp [route, different]

theorem independent_mailbox_steps_commute (mailboxes : Key → Inbox)
    (first second : Key) (a b : Action) (different : first ≠ second) :
    route (route mailboxes first a) second b = route (route mailboxes second b) first a := by
  funext key
  by_cases left : key = first
  · subst key; simp [route, different]
  · by_cases right : key = second
    · subst key; simp [route, left]
    · simp [route, left, right]

theorem foreign_arrival_is_rejected (s : Inbox) (e : Event)
    (h : e.owner ≠ s.owner) : record s e = s := by simp [record, h]

theorem duplicate_arrival_is_idempotent (s : Inbox) (e : Event) :
    record (record s e) e = record s e := by
  by_cases h : e.owner = s.owner ∧ s.phase e.serial = none
  · simp [record, h]
  · simp [record, h]

theorem accepted_event_is_queued (s : Inbox) (e : Event)
    (h : e.owner = s.owner ∧ s.phase e.serial = none) :
    e ∈ (record s e).journal ∧ (record s e).phase e.serial = some .queued := by
  simp [record, h]

theorem step_preserves_owner (s : Inbox) (a : Action) :
    (step s a).owner = s.owner := by
  cases a <;> simp only [step, record, claim, settle, park, recover]
  all_goals first | rfl | (split <;> rfl)

theorem phase_never_forgotten (s : Inbox) (a : Action) (id : Nat)
    (h : s.phase id ≠ none) : (step s a).phase id ≠ none := by
  cases a <;> simp only [step, record, claim, settle, park, recover]
  all_goals repeat' first | (split <;> simp_all) | simp_all

theorem journal_never_erased (s : Inbox) (a : Action) (e : Event)
    (h : e ∈ s.journal) : e ∈ (step s a).journal := by
  cases a <;> simp only [step, record, claim, settle, park, recover]
  all_goals first | exact h | (split <;> simp_all)

theorem settlement_never_reopened (s : Inbox) (a : Action) (id : Nat)
    (h : s.phase id = some .settled) : (step s a).phase id = some .settled := by
  cases a with
  | arrival e =>
    by_cases same : id = e.serial
    · subst id; simp [step, record, h]
    · simp only [step, record]; split <;> simp_all
  | claim serial =>
    by_cases same : id = serial
    · subst id; simp [step, claim, h]
    · simp only [step, claim]; split <;> simp_all
  | settle serial =>
    by_cases same : id = serial
    · subst id; simp [step, settle, h]
    · simp only [step, settle]; split <;> simp_all
  | park ticket => exact h
  | wake => exact h
  | recover => simp [step, recover, h]

theorem step_preserves_accounting (s : Inbox) (a : Action) (h : accounted s) :
    accounted (step s a) := by
  cases a with
  | arrival e =>
    simp only [step, record]
    split
    · intro other member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · simp only
        split <;> simp_all [accounted]
      · simp
    · exact h
  | claim id =>
    intro e member
    have old : e ∈ s.journal := by
      simp only [step, claim] at member
      split at member <;> exact member
    exact phase_never_forgotten s (.claim id) e.serial (h e old)
  | settle id =>
    intro e member
    have old : e ∈ s.journal := by
      simp only [step, settle] at member
      split at member <;> exact member
    exact phase_never_forgotten s (.settle id) e.serial (h e old)
  | park ticket => exact h
  | wake => exact h
  | recover =>
    intro e member
    exact phase_never_forgotten s .recover e.serial (h e member)

theorem step_preserves_ownership (s : Inbox) (a : Action) (h : owned s) :
    owned (step s a) := by
  cases a with
  | arrival e =>
    simp only [step, record]
    split
    · rename_i accepted
      intro other member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact h other old
      · exact accepted.1
    · exact h
  | claim id => simp only [step, claim]; split <;> exact h
  | settle id => simp only [step, settle]; split <;> exact h
  | park ticket => exact h
  | wake => exact h
  | recover => exact h

theorem park_rechecks_durable_readiness (s : Inbox) (ticket : WaitTicket) :
    safeSleep (park s ticket) := by
  intro sleeping
  change decide (ticket.owner = s.owner ∧ ticket.epoch = s.epoch ∧ pending s = []) = true at sleeping
  exact (of_decide_eq_true sleeping).2.2

theorem step_preserves_safe_sleep (s : Inbox) (a : Action) (h : safeSleep s) :
    safeSleep (step s a) := by
  cases a with
  | park t => exact park_rechecks_durable_readiness s t
  | arrival e => simp only [step, record]; split <;> simp_all [safeSleep]
  | claim id => simp only [step, claim]; split <;> simp_all [safeSleep]
  | settle id => simp only [step, settle]; split <;> simp_all [safeSleep]
  | wake => simp [step, safeSleep]
  | recover => simp [step, recover, safeSleep]

/-- Every interleaving of arrival, claim, settlement, suspension and recovery
retains accepted evidence and cannot leave queued work sleeping. -/
theorem arbitrary_trace_preserves_invariant (actions : List Action) (s : Inbox)
    (h : invariant s) : invariant (run actions s) := by
  induction actions generalizing s with
  | nil => exact h
  | cons a rest ih =>
    exact ih (step s a) ⟨step_preserves_accounting s a h.1,
      step_preserves_ownership s a h.2.1, step_preserves_safe_sleep s a h.2.2⟩

theorem accepted_evidence_survives_trace (actions : List Action) (s : Inbox)
    (e : Event) (member : e ∈ s.journal) (hasPhase : s.phase e.serial ≠ none) :
    e ∈ (run actions s).journal ∧ (run actions s).phase e.serial ≠ none := by
  induction actions generalizing s with
  | nil => exact ⟨member, hasPhase⟩
  | cons a rest ih =>
    exact ih (step s a) (journal_never_erased s a e member)
      (phase_never_forgotten s a e.serial hasPhase)

theorem settled_step_cannot_add_another_receipt (s : Inbox) (a : Action) (id : Nat)
    (done : s.phase id = some .settled) :
    (step s a).receipts.count id = s.receipts.count id := by
  cases a with
  | settle other =>
    simp only [step, settle]
    split
    · rename_i claimed
      have different : other ≠ id := by intro same; subst other; simp [done] at claimed
      simp [different]
    · rfl
  | arrival e => simp only [step, record]; split <;> rfl
  | claim other => simp only [step, claim]; split <;> rfl
  | park t => rfl
  | wake => rfl
  | recover => rfl

theorem settled_event_has_no_second_receipt (s : Inbox) (actions : List Action) (id : Nat)
    (done : s.phase id = some .settled) :
    (run actions s).receipts.count id = s.receipts.count id := by
  induction actions generalizing s with
  | nil => rfl
  | cons a rest ih =>
    rw [run, ih (step s a) (settlement_never_reopened s a id done)]
    exact settled_step_cannot_add_another_receipt s a id done

theorem stale_sleep_ticket_cannot_park (s : Inbox) (t : WaitTicket)
    (stale : t.epoch ≠ s.epoch) : (park s t).sleeping = false := by
  simp [park, stale]

theorem arrival_between_arm_and_park_is_not_lost (s : Inbox) (e : Event)
    (h : e.owner = s.owner ∧ s.phase e.serial = none) :
    (park (record s e) (arm s)).sleeping = false := by
  simp [park, arm, record, h]

theorem arrival_after_park_wakes (s : Inbox) (e : Event)
    (h : e.owner = s.owner ∧ s.phase e.serial = none) :
    (record (park s (arm s)) e).sleeping = false := by
  simp [record, park, arm, h]

theorem unrelated_claim_does_not_consume (s : Inbox) (id other : Nat)
    (different : other ≠ id) : (claim s id).phase other = s.phase other := by
  simp only [claim]; split <;> simp_all

theorem selective_receive_is_owned (s : Inbox) (accepts : Event → Bool) (e : Event)
    (h : firstMatching s accepts = some e) (ownership : owned s) :
    e.owner = s.owner ∧ accepts e = true ∧ s.phase e.serial = some .queued := by
  have found := List.find?_some h
  have member := List.mem_of_find?_eq_some h
  have source := List.mem_filter.mp member
  exact ⟨ownership e source.1, found, of_decide_eq_true source.2⟩

theorem selective_receive_uses_oldest_match (s : Inbox) (accepts : Event → Bool) (e : Event)
    (h : firstMatching s accepts = some e) :
    ∃ before after, pending s = before ++ e :: after ∧
      ∀ earlier ∈ before, accepts earlier = false := by
  obtain ⟨_, before, after, shape, skipped⟩ := List.find?_eq_some_iff_append.mp h
  exact ⟨before, after, shape, fun earlier member => by simpa using skipped earlier member⟩

theorem event_disposition_removes_only_its_pending_serial (s : Inbox) (id : Nat)
    (queued : s.phase id = some .queued) :
    pending (settle (claim s id) id) = (pending s).filter (fun e => decide (e.serial ≠ id)) := by
  simp only [pending, claim, queued, if_pos, settle, List.filter_filter]
  apply congrArg (fun predicate => s.journal.filter predicate)
  funext e
  by_cases same : e.serial = id
  · simp [same]
  · simp [same]

/-- A disposition slot records handling/rejection, not fulfillment of the
agent's task. This local drain assumes each chosen handler returns and commits.
An indefinitely waiting external call is not one of these disposition slots. -/
def drain : Nat → Inbox → Inbox
  | 0, s => s
  | n + 1, s =>
    match pending s with
    | [] => s
    | e :: _ => drain n (settle (claim s e.serial) e.serial)

theorem finite_inbox_drains_within_committed_slots (s : Inbox) (slots : Nat)
    (enough : (pending s).length ≤ slots) : pending (drain slots s) = [] := by
  induction slots generalizing s with
  | zero =>
    simpa [drain] using List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
  | succ slots ih =>
    cases shape : pending s with
    | nil => simp [drain, shape]
    | cons e rest =>
      have member : e ∈ pending s := by simp [shape]
      have queued : s.phase e.serial = some .queued :=
        of_decide_eq_true (List.mem_filter.mp member).2
      have count : (pending (settle (claim s e.serial) e.serial)).length ≤ slots := by
        rw [event_disposition_removes_only_its_pending_serial s e.serial queued, shape]
        simp only [List.filter_cons, ne_self_iff_false, decide_false, Bool.false_eq_true,
          ↓reduceIte]
        have remaining := List.length_filter_le (fun x : Event => decide (x.serial ≠ e.serial)) rest
        simp only [shape, List.length_cons] at enough
        omega
      simpa only [drain, shape] using ih (settle (claim s e.serial) e.serial) count

/-- Extracting an answer consumes local adoption authority exactly once.
Transport completion itself remains immutable evidence. -/
def takeAnswer (call : AsyncWait.Call) (revision : Nat) : Option (Nat × AsyncWait.Call) :=
  match call.terminal with
  | some (.answer value) =>
    if call.capturedRevision = revision ∧ call.adopted = false then
      some (value, AsyncWait.adopt call revision)
    else none
  | _ => none

theorem answer_adoption_is_once (call : AsyncWait.Call) (revision value : Nat)
    (next : AsyncWait.Call) (h : takeAnswer call revision = some (value, next)) :
    next.id = call.id ∧ next.terminal = call.terminal ∧
      next.adopted = true ∧ takeAnswer next revision = none := by
  unfold takeAnswer at h
  split at h
  · rename_i result complete
    split at h
    · rename_i current
      simp [AsyncWait.adopt, complete, current.1] at h
      rcases h with ⟨rfl, rfl⟩
      simp [takeAnswer]
      exact complete.symm
    · contradiction
  · contradiction

theorem stale_answer_cannot_be_taken (call : AsyncWait.Call) (revision : Nat)
    (h : call.capturedRevision ≠ revision) : takeAnswer call revision = none := by
  simp only [takeAnswer]; split <;> simp_all

def effectAnswer (call : AsyncWait.Call) (revision : Nat)
    (effects : List AdmissionFrontier.Attempt) : Option (Nat × AsyncWait.Call) :=
  if AdmissionFrontier.mayIssue effects .effect then takeAnswer call revision else none

theorem missing_effect_receipt_blocks_adoption (call : AsyncWait.Call) (revision : Nat)
    (effects : List AdmissionFrontier.Attempt)
    (h : effects.any AdmissionFrontier.blocker = true) :
    effectAnswer call revision effects = none := by
  simp [effectAnswer, AdmissionFrontier.unresolved_effect_prevents_mutation effects h]

/-- The integration obligation is to append a newly ready owner to the queue.
Readiness comes from durable rows rather than a transient wake bit. -/
def wakeReady (queue : List Key) (inbox : Inbox) : List Key :=
  if pending inbox = [] ∨ inbox.owner ∈ queue then queue else queue ++ [inbox.owner]

theorem ready_owner_is_queued (queue : List Key) (inbox : Inbox)
    (ready : pending inbox ≠ []) : inbox.owner ∈ wakeReady queue inbox := by
  simp only [wakeReady, ready, false_or]
  split <;> simp_all

theorem accepted_event_is_wakeable_and_serviced (s : Inbox) (e : Event)
    (accepted : e.owner = s.owner ∧ s.phase e.serial = none)
    (queue : List Key) (arrivals : Nat → List Key) :
    (record s e).sleeping = false ∧
    ∃ slots ≤ (wakeReady queue (record s e)).length,
      s.owner ∈ services slots arrivals (wakeReady queue (record s e)) := by
  have queued := accepted_event_is_queued s e accepted
  have member : e ∈ pending (record s e) := by
    exact List.mem_filter.mpr ⟨queued.1, by simp [queued.2]⟩
  have nonempty : pending (record s e) ≠ [] := by
    intro empty; simp [empty] at member
  have owner : (record s e).owner = s.owner := step_preserves_owner s (.arrival e)
  have ready : s.owner ∈ wakeReady queue (record s e) := by
    simpa only [owner] using ready_owner_is_queued queue (record s e) nonempty
  refine ⟨?_, queued_task_gets_bounded_service _ _ arrivals ready⟩
  simp [record, accepted]

def admit {α : Type} [DecidableEq α] (capacity : Nat) (queue : List α) (task : α) :
    Option (List α) :=
  if queue.length > capacity then none
  else if task ∈ queue then some queue
  else if queue.length < capacity then some (queue ++ [task]) else none

theorem admission_preserves_capacity {α : Type} [DecidableEq α] (capacity : Nat)
    (queue next : List α) (task : α) (h : admit capacity queue task = some next) :
    next.length ≤ capacity := by
  unfold admit at h
  split at h
  · contradiction
  · split at h
    · cases h; omega
    · split at h
      · cases h; simp; omega
      · contradiction

theorem admission_preserves_unique_tasks {α : Type} [DecidableEq α] (capacity : Nat)
    (queue next : List α) (task : α) (unique : queue.Nodup)
    (h : admit capacity queue task = some next) : next.Nodup := by
  unfold admit at h
  split at h
  · contradiction
  · split at h
    · cases h; exact unique
    · rename_i fresh
      split at h
      · cases h
        apply List.nodup_append.mpr
        refine ⟨unique, by simp, ?_⟩
        intro other member last lastMember equal
        simp only [List.mem_singleton] at lastMember
        exact fresh (lastMember ▸ (equal ▸ member))
      · contradiction

/-- Slot durations include all pump, storage and evaluation overhead. The bound
is a host obligation, not a consequence of counting language reductions. -/
theorem bounded_slot_time (durations : List Nat) (q : Nat)
    (bounded : ∀ d ∈ durations, d ≤ q) : durations.sum ≤ durations.length * q := by
  induction durations with
  | nil => simp
  | cons d ds ih =>
    have first : d ≤ q := bounded d (by simp)
    have rest := ih (fun x hx => bounded x (by simp [hx]))
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add first rest

theorem bounded_service_latency {α : Type} (queue : List α) (target : α)
    (arrivals : Nat → List α) (member : target ∈ queue) (capacity q p : Nat)
    (capacityBound : queue.length ≤ capacity)
    (durations : List Nat) (durationCount : durations.length = queue.length)
    (slotBound : ∀ d ∈ durations, d ≤ q) :
    (∃ slots ≤ capacity, target ∈ services slots arrivals queue) ∧
      p + durations.sum ≤ p + capacity * q := by
  obtain ⟨slots, bound, served⟩ := queued_task_gets_bounded_service queue target arrivals member
  refine ⟨⟨slots, Nat.le_trans bound capacityBound, served⟩, ?_⟩
  have time := bounded_slot_time durations q slotBound
  rw [durationCount] at time
  exact Nat.add_le_add_left (Nat.le_trans time (Nat.mul_le_mul_right q capacityBound)) p

/-- A host adapter must establish this equation for its actual transition
function. Unobservable bookkeeping may stutter; semantic steps must be exactly
the modeled transition. This field is an obligation, not an axiom about C. -/
structure HostAdapter (Host Input : Type) where
  project : Host → Inbox
  advance : Host → Input → Host
  decode : Input → Option Action
  refines : ∀ host input, project (advance host input) =
    match decode input with
    | none => project host
    | some action => step (project host) action

def hostRun {Host Input : Type} (adapter : HostAdapter Host Input) :
    List Input → Host → Host
  | [], host => host
  | input :: rest, host => hostRun adapter rest (adapter.advance host input)

theorem host_trace_refines_recorded_contract {Host Input : Type}
    (adapter : HostAdapter Host Input) (inputs : List Input) (host : Host) :
    adapter.project (hostRun adapter inputs host) =
      run (inputs.filterMap adapter.decode) (adapter.project host) := by
  induction inputs generalizing host with
  | nil => rfl
  | cons input rest ih =>
    rw [hostRun, ih, adapter.refines]
    cases decoded : adapter.decode input <;> simp [decoded, run]

theorem refining_host_inherits_evidence_and_wakeup_safety {Host Input : Type}
    (adapter : HostAdapter Host Input) (inputs : List Input) (host : Host)
    (h : invariant (adapter.project host)) :
    invariant (adapter.project (hostRun adapter inputs host)) := by
  rw [host_trace_refines_recorded_contract]
  exact arbitrary_trace_preserves_invariant _ _ h


namespace FiniteBurst

/-- Mailbox evidence has unique physical serials and receipts. Every live
phase belongs to admitted source evidence; settled receipts are permanent. -/
def WellFormed (s : Inbox) : Prop :=
  invariant s ∧ (s.journal.map Event.serial).Nodup ∧
    (∀ id, s.phase id ≠ none → id ∈ s.journal.map Event.serial) ∧
    s.receipts.Nodup ∧ (∀ id ∈ s.receipts, s.phase id = some .settled)

def initial (owner : Key) : Inbox := { owner := owner }

theorem initial_wellFormed (owner : Key) : WellFormed (initial owner) := by
  simp [WellFormed, initial, invariant, accounted, owned, safeSleep]

private theorem fresh_serial_not_in_journal (s : Inbox) (id : Nat)
    (accounting : accounted s) (fresh : s.phase id = none) : id ∉ s.journal.map Event.serial := by
  intro member
  obtain ⟨event, present, same⟩ := List.mem_map.mp member
  exact accounting event present (same ▸ fresh)

private theorem step_serials_unique (s : Inbox) (action : Action)
    (accounting : accounted s) (unique : (s.journal.map Event.serial).Nodup) :
    ((step s action).journal.map Event.serial).Nodup := by
  cases action with
  | arrival event =>
      by_cases accepted : event.owner = s.owner ∧ s.phase event.serial = none
      · have fresh := fresh_serial_not_in_journal s event.serial accounting accepted.2
        simpa [step, record, accepted, List.nodup_append] using And.intro unique fresh
      · simpa [step, record, accepted] using unique
  | claim id => simp only [step, claim]; split <;> exact unique
  | settle id => simp only [step, settle]; split <;> exact unique
  | park ticket => exact unique
  | wake => exact unique
  | recover => exact unique

private theorem step_phase_origin (s : Inbox) (action : Action)
    (known : ∀ id, s.phase id ≠ none → id ∈ s.journal.map Event.serial) :
    ∀ id, (step s action).phase id ≠ none → id ∈ (step s action).journal.map Event.serial := by
  intro id live
  cases action with
  | arrival event =>
      by_cases accepted : event.owner = s.owner ∧ s.phase event.serial = none
      · by_cases same : id = event.serial
        · simp [step, record, accepted, same]
        · have old : s.phase id ≠ none := by simpa [step, record, accepted, same] using live
          simpa [step, record, accepted] using List.mem_append_left [event.serial] (known id old)
      · simpa [step, record, accepted] using known id (by simpa [step, record, accepted] using live)
  | claim serial =>
      by_cases queued : s.phase serial = some .queued
      · by_cases same : id = serial
        · simpa [step, claim, queued, same] using known serial (by simp [queued])
        · simpa [step, claim, queued] using known id (by simpa [step, claim, queued, same] using live)
      · simpa [step, claim, queued] using known id (by simpa [step, claim, queued] using live)
  | settle serial =>
      by_cases claimed : s.phase serial = some .claimed
      · by_cases same : id = serial
        · simpa [step, settle, claimed, same] using known serial (by simp [claimed])
        · simpa [step, settle, claimed] using known id (by simpa [step, settle, claimed, same] using live)
      · simpa [step, settle, claimed] using known id (by simpa [step, settle, claimed] using live)
  | park ticket => exact known id live
  | wake => exact known id live
  | recover =>
      apply known id
      intro absent
      simp [step, recover, absent] at live

private theorem step_receipts_sound (s : Inbox) (action : Action)
    (sound : ∀ id ∈ s.receipts, s.phase id = some .settled) :
    ∀ id ∈ (step s action).receipts, (step s action).phase id = some .settled := by
  intro id member
  cases action with
  | settle serial =>
      by_cases claimed : s.phase serial = some .claimed
      · have received : id ∈ s.receipts ++ [serial] := by simpa [step, settle, claimed] using member
        rcases List.mem_append.mp received with old | new
        · exact settlement_never_reopened s (.settle serial) id (sound id old)
        · have same : id = serial := List.mem_singleton.mp new
          simp [step, settle, claimed, same]
      · exact settlement_never_reopened s (.settle serial) id (sound id (by simpa [step, settle, claimed] using member))
  | arrival event =>
      have old : id ∈ s.receipts := by
        simp only [step, record] at member
        split at member <;> exact member
      exact settlement_never_reopened s (.arrival event) id (sound id old)
  | claim serial =>
      have old : id ∈ s.receipts := by
        simp only [step, claim] at member
        split at member <;> exact member
      exact settlement_never_reopened s (.claim serial) id (sound id old)
  | park ticket => exact sound id member
  | wake => exact sound id member
  | recover => exact settlement_never_reopened s .recover id (sound id member)

private theorem step_receipts_unique (s : Inbox) (action : Action)
    (unique : s.receipts.Nodup) (sound : ∀ id ∈ s.receipts, s.phase id = some .settled) :
    (step s action).receipts.Nodup := by
  cases action with
  | settle serial =>
      by_cases claimed : s.phase serial = some .claimed
      · have fresh : serial ∉ s.receipts := by
          intro present
          have done := sound serial present
          simp [claimed] at done
        simp only [step, settle, claimed, if_pos]
        apply List.nodup_append.mpr
        refine ⟨unique, by simp, ?_⟩
        intro a present b last equal
        have same : b = serial := List.mem_singleton.mp last
        exact fresh (same ▸ (equal ▸ present))
      · simpa [step, settle, claimed] using unique
  | arrival event => simp only [step, record]; split <;> exact unique
  | claim serial => simp only [step, claim]; split <;> exact unique
  | park ticket => exact unique
  | wake => exact unique
  | recover => exact unique

theorem step_wellFormed (s : Inbox) (action : Action) (well : WellFormed s) :
    WellFormed (step s action) := by
  exact ⟨⟨step_preserves_accounting s action well.1.1,
    step_preserves_ownership s action well.1.2.1, step_preserves_safe_sleep s action well.1.2.2⟩,
    step_serials_unique s action well.1.1 well.2.1,
    step_phase_origin s action well.2.2.1,
    step_receipts_unique s action well.2.2.2.1 well.2.2.2.2,
    step_receipts_sound s action well.2.2.2.2⟩

theorem run_wellFormed (actions : List Action) (s : Inbox) (well : WellFormed s) :
    WellFormed (run actions s) := by
  induction actions generalizing s with
  | nil => exact well
  | cons action rest ih => exact ih _ (step_wellFormed s action well)

/-- Each finite burst is admitted through the actual serial/owner checks. -/
def recordBurst (s : Inbox) : List Event → Inbox
  | [] => s
  | event :: rest => recordBurst (record s event) rest

theorem recordBurst_wellFormed (s : Inbox) (events : List Event) (well : WellFormed s) :
    WellFormed (recordBurst s events) := by
  induction events generalizing s with
  | nil => exact well
  | cons event rest ih => exact ih _ (step_wellFormed s (.arrival event) well)

theorem record_pending_append (s : Inbox) (event : Event) (accounting : accounted s)
    (accepted : event.owner = s.owner ∧ s.phase event.serial = none) :
    pending (record s event) = pending s ++ [event] := by
  have unchanged : s.journal.filter (fun old => decide
      ((if old.serial = event.serial then some Delivery.queued else s.phase old.serial) = some .queued)) = pending s := by
    apply List.filter_congr
    intro old member
    have different : old.serial ≠ event.serial := by
      intro same
      exact accounting old member (same ▸ accepted.2)
    simp [different]
  simpa [record, accepted, pending] using congrArg (· ++ [event]) unchanged

/-- The accepted suffix is derived from real record calls. Rejected or
repeated serials cannot move or replace an earlier pending occurrence. -/
theorem recordBurst_extends (s : Inbox) (events : List Event) (well : WellFormed s) :
    ∃ accepted, (recordBurst s events).journal = s.journal ++ accepted ∧
      pending (recordBurst s events) = pending s ++ accepted ∧ accepted.Sublist events := by
  induction events generalizing s with
  | nil => exact ⟨[], by simp [recordBurst], by simp [recordBurst], .refl _⟩
  | cons event rest ih =>
      obtain ⟨later, journal, queue, included⟩ := ih (record s event) (step_wellFormed s (.arrival event) well)
      by_cases accepted : event.owner = s.owner ∧ s.phase event.serial = none
      · refine ⟨event :: later, ?_, ?_, included.cons_cons event⟩
        · simpa [recordBurst, record, accepted, List.append_assoc] using journal
        · simpa only [recordBurst, record_pending_append s event well.1.1 accepted, List.append_assoc, List.singleton_append] using queue
      · refine ⟨later, ?_, ?_, included.cons event⟩
        · simpa [recordBurst, record, accepted] using journal
        · simpa [recordBurst, record, accepted] using queue


theorem firstMatching_all (s : Inbox) : firstMatching s (fun _ => true) = (pending s).head? := by
  cases queue : pending s <;> simp [firstMatching, queue]

private theorem receive_oldest (s : Inbox) (event : Event) (rest : List Event)
    (queue : pending s = event :: rest) : receive s (fun _ => true) = claim s event.serial := by
  simp only [receive, firstMatching_all, queue, List.head?_cons]

/-- One committed disposition slot. The selected handler and its acknowledgment
must return and permit settlement; a waiting or withheld commit is no slot. -/
def serveOldest (s : Inbox) : Option Event × Inbox :=
  match pending s with
  | [] => (none, s)
  | event :: _ => (some event, settle (receive s (fun _ => true)) event.serial)

private theorem pending_serials_unique (s : Inbox) (well : WellFormed s) :
    ((pending s).map Event.serial).Nodup :=
  well.2.1.sublist (List.filter_sublist.map Event.serial)

theorem serveOldest_wellFormed (s : Inbox) (well : WellFormed s) :
    WellFormed (serveOldest s).2 := by
  cases queue : pending s with
  | nil => simpa only [serveOldest, queue] using well
  | cons event rest =>
      simpa only [serveOldest, queue, receive_oldest s event rest queue, step] using
        step_wellFormed (claim s event.serial) (.settle event.serial) (step_wellFormed s (.claim event.serial) well)

/-- Both the exact queue residual and the actual acknowledgment list are
projected from receive/claim/settle, with no equality of payloads involved. -/
theorem serveOldest_projection (s : Inbox) (well : WellFormed s) :
    pending (serveOldest s).2 = (pending s).drop 1 ∧
      (serveOldest s).2.receipts = s.receipts ++ ((pending s).take 1).map Event.serial := by
  cases queue : pending s with
  | nil => simp [serveOldest, queue]
  | cons event rest =>
      have member : event ∈ pending s := by simp [queue]
      have queued : s.phase event.serial = some .queued := of_decide_eq_true (List.mem_filter.mp member).2
      have distinct : event.serial ∉ rest.map Event.serial := by
        have unique := pending_serials_unique s well
        rw [queue, List.map_cons] at unique
        exact (List.nodup_cons.mp unique).1
      have unchanged : rest.filter (fun e => decide (e.serial ≠ event.serial)) = rest := by
        apply List.filter_eq_self.mpr
        intro other present
        apply decide_eq_true
        intro same
        exact distinct (List.mem_map.mpr ⟨other, present, same⟩)
      simp only [serveOldest, queue, receive_oldest s event rest queue]
      refine ⟨?_, ?_⟩
      · rw [event_disposition_removes_only_its_pending_serial s event.serial queued, queue]
        simpa using unchanged
      · simp [claim, settle, queued]

theorem served_event_origin (s : Inbox) (well : WellFormed s) (event : Event)
    (served : (serveOldest s).1 = some event) :
    event ∈ s.journal ∧ event.owner = s.owner ∧ s.phase event.serial = some .queued ∧
      (serveOldest s).2.phase event.serial = some .settled := by
  cases queue : pending s with
  | nil => simp [serveOldest, queue] at served
  | cons chosen rest =>
      simp only [serveOldest, queue] at served
      cases served
      have member : event ∈ pending s := by simp [queue]
      have source := List.mem_filter.mp member
      have queued : s.phase event.serial = some .queued := of_decide_eq_true source.2
      exact ⟨source.1, well.1.2.1 event source.1, queued, by
        simp [serveOldest, queue, receive_oldest s event rest queue, claim, settle, queued]⟩

private theorem serveOldest_journal (s : Inbox) : (serveOldest s).2.journal = s.journal := by
  cases queue : pending s with
  | nil => simp only [serveOldest, queue]
  | cons event rest =>
      simp only [serveOldest, queue, receive_oldest s event rest queue, claim, settle]
      split <;> (first | rfl | (split <;> rfl))

private theorem serveOldest_owner (s : Inbox) : (serveOldest s).2.owner = s.owner := by
  cases queue : pending s with
  | nil => simp only [serveOldest, queue]
  | cons event rest =>
      simp only [serveOldest, queue, receive_oldest s event rest queue, claim, settle]
      split <;> (first | rfl | (split <;> rfl))

private theorem recordBurst_receipts (s : Inbox) (events : List Event) :
    (recordBurst s events).receipts = s.receipts := by
  induction events generalizing s with
  | nil => rfl
  | cons event rest ih =>
      rw [recordBurst, ih]
      unfold record
      split <;> rfl

private theorem recordBurst_owner (s : Inbox) (events : List Event) :
    (recordBurst s events).owner = s.owner := by
  induction events generalizing s with
  | nil => rfl
  | cons event rest ih =>
      exact (ih (record s event)).trans (step_preserves_owner s (.arrival event))

/-- The oldest pending occurrence is committed before any later burst is
admitted through record. Equal payloads still have separate stable serials. -/
def slot (events : List Event) (s : Inbox) : Inbox := recordBurst (serveOldest s).2 events

def pump : Nat → (Nat → List Event) → Inbox → Inbox
  | 0, _, s => s
  | slots + 1, arrivals, s => pump slots (fun i => arrivals (i + 1)) (slot (arrivals 0) s)

theorem slot_wellFormed (events : List Event) (s : Inbox) (well : WellFormed s) :
    WellFormed (slot events s) :=
  recordBurst_wellFormed _ events (serveOldest_wellFormed s well)

theorem pump_wellFormed (slots : Nat) (arrivals : Nat → List Event) (s : Inbox) (well : WellFormed s) :
    WellFormed (pump slots arrivals s) := by
  induction slots generalizing arrivals s with
  | zero => exact well
  | succ slots ih => exact ih _ _ (slot_wellFormed _ s well)

theorem pump_preserves_owner (slots : Nat) (arrivals : Nat → List Event) (s : Inbox) :
    (pump slots arrivals s).owner = s.owner := by
  induction slots generalizing arrivals s with
  | zero => rfl
  | succ slots ih =>
      exact (ih _ _).trans ((recordBurst_owner (serveOldest s).2 (arrivals 0)).trans (serveOldest_owner s))

/-- Every field of the actual Inbox survives bounded slicing, including phase,
serial evidence, receipts, epoch and sleep state. The later burst schedule
starts at the resumed slot; this is not a wall-clock latency assertion. -/
theorem pump_add (first second : Nat) (arrivals : Nat → List Event) (s : Inbox) :
    pump (first + second) arrivals s = pump second (fun i => arrivals (i + first)) (pump first arrivals s) := by
  induction first generalizing arrivals s with
  | zero => simp [pump]
  | succ first ih =>
      simpa only [Nat.succ_add, Nat.zero_add, pump, Nat.add_assoc, Nat.add_comm first 1] using
        ih (fun i => arrivals (i + 1)) (slot (arrivals 0) s)

/-- Full payload evidence is retained by these actual operations. The suffix
is proof data, not another runtime journal. -/
theorem pump_journal_extends (slots : Nat) (arrivals : Nat → List Event) (s : Inbox) (well : WellFormed s) :
    ∃ suffix, (pump slots arrivals s).journal = s.journal ++ suffix := by
  induction slots generalizing arrivals s with
  | zero => exact ⟨[], by simp [pump]⟩
  | succ slots ih =>
      obtain ⟨fresh, journal, _, _⟩ := recordBurst_extends (serveOldest s).2 (arrivals 0) (serveOldest_wellFormed s well)
      obtain ⟨later, retained⟩ := ih (fun i => arrivals (i + 1)) (slot (arrivals 0) s) (slot_wellFormed _ s well)
      refine ⟨fresh ++ later, ?_⟩
      simpa only [pump, slot, journal, serveOldest_journal, List.append_assoc] using retained



/-- The comparison schedule is constructed from accepted record suffixes of
this actual pump. It is proof data, never a source oracle used by the runner. -/
theorem pump_cooperative (slots : Nat) (arrivals : Nat → List Event) (s : Inbox) (well : WellFormed s) :
    ∃ accepted : Nat → List Event,
      pending (pump slots arrivals s) = remainingRetiring slots (fun _ => false) accepted (pending s) ∧
      (pump slots arrivals s).receipts = s.receipts ++
        (servicesRetiring slots (fun _ => false) accepted (pending s)).map Event.serial ∧
      ∀ i, i < slots → (accepted i).Sublist (arrivals i) := by
  induction slots generalizing arrivals s with
  | zero => exact ⟨fun _ => [], rfl, by simp [pump, servicesRetiring], by simp⟩
  | succ slots ih =>
      let next := slot (arrivals 0) s
      have nextWell : WellFormed next := slot_wellFormed _ s well
      obtain ⟨fresh, _, queue, included⟩ := recordBurst_extends (serveOldest s).2 (arrivals 0) (serveOldest_wellFormed s well)
      have nextQueue : pending next = (pending s).drop 1 ++ fresh := by
        exact queue.trans (congrArg (· ++ fresh) (serveOldest_projection s well).1)
      have nextReceipts : next.receipts = s.receipts ++ ((pending s).take 1).map Event.serial :=
        (recordBurst_receipts _ _).trans (serveOldest_projection s well).2
      obtain ⟨later, retained, paid, origins⟩ := ih (fun i => arrivals (i + 1)) next nextWell
      let accepted : Nat → List Event := fun | 0 => fresh | i + 1 => later i
      refine ⟨accepted, ?_, ?_, ?_⟩
      · change pending (pump slots (fun i => arrivals (i + 1)) next) = _
        rw [retained, nextQueue]
        cases shape : pending s <;>
          simp [remainingRetiring, rotateRetiring, accepted]
      · change (pump slots (fun i => arrivals (i + 1)) next).receipts = _
        rw [paid, nextReceipts, nextQueue]
        cases shape : pending s <;>
          simp [servicesRetiring, accepted, List.append_assoc]
      · intro i bound
        cases i with
        | zero => exact included
        | succ i => exact origins i (by omega)

/-- A specific queued occurrence is settled within its original FIFO position.
Arbitrary later finite bursts are already included in the actual transition. -/
theorem pending_prefix_service (s : Inbox) (well : WellFormed s) (arrivals : Nat → List Event)
    (before after : List Event) (event : Event) (queue : pending s = before ++ event :: after) :
    let final := pump (before.length + 1) arrivals s
    final.phase event.serial = some .settled ∧ final.receipts.count event.serial = 1 ∧
      event ∈ final.journal ∧ event.owner = final.owner := by
  obtain ⟨accepted, _, receipts, _⟩ := pump_cooperative (before.length + 1) arrivals s well
  have serviced := prefix_served_despite_retirement_and_arrivals before after event (fun _ => false) accepted
  rw [← queue] at serviced
  have receipt : event.serial ∈ (pump (before.length + 1) arrivals s).receipts := by
    rw [receipts]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨event, serviced, rfl⟩)
  have finalWell := pump_wellFormed (before.length + 1) arrivals s well
  have member : event ∈ pending s := by simp [queue]
  have old : event ∈ s.journal := (List.mem_filter.mp member).1
  obtain ⟨suffix, extended⟩ := pump_journal_extends (before.length + 1) arrivals s well
  refine ⟨finalWell.2.2.2.2 event.serial receipt, ?_, ?_, ?_⟩
  · simpa only [if_pos receipt] using finalWell.2.2.2.1.count (a := event.serial)
  · rw [extended]
    exact List.mem_append_left _ old
  · exact (well.1.2.1 event old).trans (pump_preserves_owner _ arrivals s).symm

theorem queued_message_service_bound (s : Inbox) (well : WellFormed s) (arrivals : Nat → List Event)
    (event : Event) (queued : event ∈ pending s) :
    ∃ slots ≤ (pending s).length,
      (pump slots arrivals s).phase event.serial = some .settled ∧
      (pump slots arrivals s).receipts.count event.serial = 1 ∧
      event ∈ (pump slots arrivals s).journal ∧ event.owner = (pump slots arrivals s).owner := by
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp queued
  refine ⟨before.length + 1, ?_, pending_prefix_service s well arrivals before after event shape⟩
  simp [shape]

/-- For every newly admitted physical event, the current pending prefix plus
one committed settlement slot suffices. Equal client labels or payload codes
supply no identity; only the admitted serial identifies this occurrence. -/
theorem admitted_message_service_bound (s : Inbox) (well : WellFormed s) (event : Event)
    (admitted : event.owner = s.owner ∧ s.phase event.serial = none) (arrivals : Nat → List Event) :
    let final := pump ((pending s).length + 1) arrivals (record s event)
    final.phase event.serial = some .settled ∧ final.receipts.count event.serial = 1 ∧
      event ∈ final.journal ∧ event.owner = final.owner := by
  exact pending_prefix_service (record s event) (step_wellFormed s (.arrival event) well) arrivals
    (pending s) [] event (by simpa using record_pending_append s event well.1.1 admitted)

/-- Receipts refer to unique actual source evidence owned by the same mailbox.
The payload is that evidence's payload, rather than a lookup by equal label. -/
theorem pump_receipt_origin (slots : Nat) (arrivals : Nat → List Event) (s : Inbox) (well : WellFormed s)
    (serial : Nat) (received : serial ∈ (pump slots arrivals s).receipts) :
    ∃ event ∈ (pump slots arrivals s).journal,
      event.serial = serial ∧ event.owner = s.owner ∧
      (pump slots arrivals s).phase serial = some .settled ∧
      (pump slots arrivals s).receipts.count serial = 1 := by
  have finalWell := pump_wellFormed slots arrivals s well
  have settled := finalWell.2.2.2.2 serial received
  have known := finalWell.2.2.1 serial (by simp [settled])
  obtain ⟨event, member, same⟩ := List.mem_map.mp known
  refine ⟨event, member, same, ?_, settled, ?_⟩
  · exact (finalWell.1.2.1 event member).trans (pump_preserves_owner slots arrivals s)
  · simpa only [if_pos received] using finalWell.2.2.2.1.count (a := serial)


private theorem recordBurst_preserves_settlement (events : List Event) (s : Inbox)
    (serial : Nat) (done : s.phase serial = some .settled) :
    (recordBurst s events).phase serial = some .settled ∧
      (recordBurst s events).receipts.count serial = s.receipts.count serial := by
  induction events generalizing s with
  | nil => exact ⟨done, rfl⟩
  | cons event rest ih =>
      have kept := settlement_never_reopened s (.arrival event) serial done
      obtain ⟨settled, count⟩ := ih (record s event) kept
      exact ⟨settled, count.trans (settled_step_cannot_add_another_receipt s (.arrival event) serial done)⟩

private theorem serveOldest_preserves_settlement (s : Inbox) (serial : Nat)
    (done : s.phase serial = some .settled) :
    (serveOldest s).2.phase serial = some .settled ∧
      (serveOldest s).2.receipts.count serial = s.receipts.count serial := by
  cases queue : pending s with
  | nil => simp [serveOldest, queue, done]
  | cons event rest =>
      have claimed := settlement_never_reopened s (.claim event.serial) serial done
      have settled := settlement_never_reopened (claim s event.serial) (.settle event.serial) serial claimed
      have count := (settled_step_cannot_add_another_receipt (claim s event.serial) (.settle event.serial) serial claimed).trans
        (settled_step_cannot_add_another_receipt s (.claim event.serial) serial done)
      simpa only [serveOldest, queue, receive_oldest s event rest queue, step] using And.intro settled count

/-- Once settled, an occurrence cannot receive another receipt even across
arbitrary later finite bursts and resumptions. -/
theorem pump_preserves_settlement (slots : Nat) (arrivals : Nat → List Event) (s : Inbox)
    (serial : Nat) (done : s.phase serial = some .settled) :
    (pump slots arrivals s).phase serial = some .settled ∧
      (pump slots arrivals s).receipts.count serial = s.receipts.count serial := by
  induction slots generalizing arrivals s with
  | zero => exact ⟨done, rfl⟩
  | succ slots ih =>
      have served := serveOldest_preserves_settlement s serial done
      have admitted := recordBurst_preserves_settlement (arrivals 0) (serveOldest s).2 serial served.1
      have resumed := ih (fun i => arrivals (i + 1)) (slot (arrivals 0) s) admitted.1
      exact ⟨resumed.1, resumed.2.trans (admitted.2.trans served.2)⟩

namespace Controls

private def owner : Key := ⟨1, 0, 0⟩
private def event (serial : Nat) (payload : Nat := 42) : Event := ⟨serial, owner, payload⟩
private def two : Inbox := recordBurst (initial owner) [event 7, event 8]
private def bursts : Nat → List Event
  | 0 => [⟨9, ⟨2, 0, 0⟩, 42⟩, event 7 999, event 9]
  | 1 => [event 8 999, event 10]
  | _ => []

/-- Equal payloads remain distinct occurrences. Foreign/repeated serials do not
replace either original or jump the older pending prefix. -/
theorem equal_payloads_late_bursts :
    let final := pump 2 bursts two
    final.receipts = [7, 8] ∧ pending final = [event 9, event 10] ∧
      final.journal = [event 7, event 8, event 9, event 10] ∧
      final.phase 7 = some .settled ∧ final.phase 8 = some .settled := by decide

/-- With no queued work a slot admits its later burst; zero allowance leaves
that complete mailbox untouched, and the next resumed slot settles it. -/
theorem idle_arrival_zero_resume :
    let arrivals : Nat → List Event := fun | 0 => [event 7] | _ => []
    let arrived := pump 1 arrivals (initial owner)
    pending arrived = [event 7] ∧ arrived.receipts = [] ∧
      pump 0 arrivals arrived = arrived ∧
      (pump 1 (fun i => arrivals (i + 1)) arrived).receipts = [7] ∧
      pump 2 arrivals (initial owner) = pump 1 (fun i => arrivals (i + 1)) arrived := by
  refine ⟨by decide, rfl, rfl, by decide, ?_⟩
  exact pump_add 1 1 _ _

/-- Claiming alone is not settlement. Waiting without a settlement action
keeps the claim and produces no acknowledgment; recovery can retry it once. -/
theorem claim_wait_recover_settle :
    let claimed := receive two (fun _ => true)
    let waiting := run [.wake, .arrival (event 9)] claimed
    let retried := (serveOldest (recover waiting)).2
    claimed.phase 7 = some .claimed ∧ claimed.receipts = [] ∧
      waiting.phase 7 = some .claimed ∧ waiting.receipts = [] ∧
      pending (recover waiting) = [event 7, event 8, event 9] ∧
      retried.phase 7 = some .settled ∧ retried.receipts = [7] ∧
      (settle retried 7).receipts = [7] := by decide

/-- The older accounting predicate alone admits forged duplicate serials.
The preserved stronger invariant excludes that state before a FIFO bound. -/
theorem forged_serial_rejected_by_invariant :
    let forged : Inbox := {
      owner := owner
      journal := [event 7, event 7 999]
      phase := fun id => if id = 7 then some .queued else none }
    invariant forged ∧ ¬ WellFormed forged := by
  constructor
  · simp [invariant, accounted, owned, safeSleep, event]
  · intro well
    have unique := well.2.1
    simp [event] at unique

end Controls

#print axioms initial_wellFormed
#print axioms step_wellFormed
#print axioms run_wellFormed
#print axioms recordBurst_extends
#print axioms serveOldest_projection
#print axioms served_event_origin
#print axioms pump_wellFormed
#print axioms pump_add
#print axioms pump_journal_extends
#print axioms pump_cooperative
#print axioms pending_prefix_service
#print axioms queued_message_service_bound
#print axioms admitted_message_service_bound
#print axioms pump_receipt_origin
#print axioms pump_preserves_settlement
#print axioms Controls.equal_payloads_late_bursts
#print axioms Controls.idle_arrival_zero_resume
#print axioms Controls.claim_wait_recover_settle
#print axioms Controls.forged_serial_rejected_by_invariant

end FiniteBurst

end Mettapedia.Machines.EventPump
