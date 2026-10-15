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

end Mettapedia.Machines.EventPump
