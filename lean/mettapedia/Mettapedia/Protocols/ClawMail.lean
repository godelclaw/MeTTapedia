import Mettapedia.Protocols.Mail.Mailbox
import Mettapedia.Machines.SpaceService

/-!
# claw-mail: native agent mailboxes

The agent mailbox of CeTTa's `lib/mailbox.metta`, the protocol behind the
`claw-mail` command. A space holds a delivery ledger with one record per
occurrence (`MailboxMessage`) and a stage for each occurrence: pending,
ready (taken by its recipient, not yet acknowledged) or settled.
- `send` accepts a new occurrence identity, treats an identical resend as a
  duplicate, and refuses a changed recipient, sender or body as a conflict.
- `post` is the send of another account. The service writes the authenticated
  account into the sender, so only the agent name inside an account is the
  caller's claim.
- `next` first presents an unacknowledged ready delivery again; otherwise it
  takes the recipient's first pending occurrence in arrival order.
- `ack` settles a ready delivery.

The native service commits each transition as one conditional batch against
the revision it read, by the laws of `Machines.SpaceService.conditionalWrite`.
`commitAt` is that law for content of any type, a mailbox state included
(`commitAt_eq_conditionalWrite`). `run_no_lost_update` shows what it buys:
however clients interleave their reads and writes, the committed transitions
form a chain, each applied to the content its client read. Without the check
an update can be lost, and an example shows one.

The theorems: transitions preserve the ledger invariant; resends are
idempotent and conflicts change nothing; a posted sender's account is the
authenticated one; `next` is stable until `ack`, never presents a settled
delivery, and takes pending mail in arrival order; and each inbox is a
`Mail.Mailbox` whose deliveries and acknowledgements claw-mail refines.

Not modelled: waits, listeners and cancellation (the selective-receive layer
used for stored continuations), `watch`, retention, and the transport.
-/

namespace Mettapedia.Protocols.ClawMail

open Mettapedia.Protocols.Mail

/-- An account the service authenticated from the connection's credentials. -/
abbrev Account := String
/-- The name an agent gives itself within its account. -/
abbrev Agent := String
/-- The identity a sender chooses for one send. -/
abbrev Occurrence := String
/-- A recipient name; the recipient is the channel. -/
abbrev Channel := String

/-- A sender as the ledger records it. -/
structure Sender where
  account : Account
  agent : Agent
deriving DecidableEq, Repr

/-- One ledger record. -/
structure Delivery where
  id : Occurrence
  channel : Channel
  sender : Sender
  body : String
deriving DecidableEq, Repr

/-- Where an occurrence is in its life. -/
inductive Stage | pending | ready | settled
deriving DecidableEq, Repr

/-- A mailbox space: the ledger in arrival order and each occurrence's stage. -/
structure State where
  ledger : List Delivery
  stage : Occurrence → Option Stage

namespace State

/-- The empty space. -/
def empty : State := ⟨[], fun _ => none⟩

/-- Ledger identities in arrival order. -/
def ids (s : State) : List Occurrence := s.ledger.map Delivery.id

/-- The ledger record of an occurrence. -/
def find (s : State) (id : Occurrence) : Option Delivery := s.ledger.find? (fun d => d.id = id)

/-- The ledger invariant: one record per identity, and exactly the recorded
identities have a stage. -/
structure Valid (s : State) : Prop where
  unique : s.ids.Nodup
  staged : ∀ id, (s.stage id).isSome ↔ id ∈ s.ids

/-- The answer to a send. -/
inductive SendResult | accepted | duplicate | conflict
deriving DecidableEq, Repr

/-- Accept a new occurrence, recognise a resend, refuse a changed one. -/
def send (s : State) (d : Delivery) : SendResult × State :=
  match s.find d.id with
  | none => (.accepted, ⟨s.ledger ++ [d], Function.update s.stage d.id (some .pending)⟩)
  | some old => if old = d then (.duplicate, s) else (.conflict, s)

/-- A send from another account: the service binds the sender's account to the
authenticated principal, whatever the caller wrote there. -/
def post (s : State) (principal : Account) (claimed : Delivery) : SendResult × State :=
  s.send { claimed with sender := { claimed.sender with account := principal } }

/-- The answer to `next`. -/
inductive NextResult | delivery (d : Delivery) | idle
deriving DecidableEq, Repr

/-- The owner's first delivery at a stage, in arrival order. -/
def firstAt (s : State) (owner : Channel) (st : Stage) : Option Delivery :=
  s.ledger.find? (fun d => d.channel = owner ∧ s.stage d.id = some st)

/-- Present the owner's unacknowledged delivery again, or take its first pending one. -/
def next (s : State) (owner : Channel) : NextResult × State :=
  match s.firstAt owner .ready with
  | some d => (.delivery d, s)
  | none =>
    match s.firstAt owner .pending with
    | some d => (.delivery d, { s with stage := Function.update s.stage d.id (some .ready) })
    | none => (.idle, s)

/-- The answer to `ack`. -/
inductive AckResult | settled | duplicate
deriving DecidableEq, Repr

/-- Settle the owner's ready delivery; anything else is a duplicate acknowledgement. -/
def ack (s : State) (owner : Channel) (id : Occurrence) : AckResult × State :=
  match s.find id with
  | some d =>
    if d.channel = owner ∧ s.stage id = some .ready then
      (.settled, { s with stage := Function.update s.stage id (some .settled) })
    else (.duplicate, s)
  | none => (.duplicate, s)

/-! ## Ledger lemmas -/

theorem find_none {s : State} {id : Occurrence} : s.find id = none ↔ id ∉ s.ids := by
  simp [find, ids, List.find?_eq_none]

theorem find_some {s : State} {id : Occurrence} {d : Delivery} (h : s.find id = some d) :
    d ∈ s.ledger ∧ d.id = id := by
  unfold find at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem empty_valid : empty.Valid := ⟨List.nodup_nil, by simp [empty, ids]⟩

/-! ## Sending -/

theorem send_valid {s : State} (hs : s.Valid) (d : Delivery) : (s.send d).2.Valid := by
  unfold send
  split
  · next hnone =>
    have fresh : d.id ∉ s.ids := find_none.mp hnone
    refine ⟨?_, ?_⟩
    · simpa [ids] using List.Nodup.append hs.unique (List.nodup_singleton _) (by simpa using fresh)
    · intro id
      by_cases h : id = d.id
      · subst h; simp [ids]
      · simp [ids, hs.staged id, h]
  · split <;> exact hs

/-- A resend after an accepted or duplicate send is a duplicate and changes nothing. -/
theorem send_again {s : State} (d : Delivery) (h : (s.send d).1 ≠ .conflict) :
    (s.send d).2.send d = (.duplicate, (s.send d).2) := by
  unfold send at *
  split at h
  · next hnone =>
    have : (⟨s.ledger ++ [d], Function.update s.stage d.id (some .pending)⟩ : State).find d.id = some d := by
      unfold find
      rw [List.find?_append]
      have : s.ledger.find? (fun x => decide (x.id = d.id)) = none := by simpa [find] using hnone
      simp [this]
    simp only [this, if_true]
  · next old hold =>
    split at h
    · next heq => subst heq; simp [hold]
    · exact absurd rfl h

/-- A changed occurrence is refused and changes nothing. -/
theorem send_conflict {s : State} {d old : Delivery} (hold : s.find d.id = some old) (ne : old ≠ d) :
    s.send d = (.conflict, s) := by
  simp [send, hold, ne]

/-- A posted sender's account is the authenticated principal. -/
theorem post_account {s : State} (principal : Account) (claimed : Delivery)
    (h : (s.post principal claimed).1 = .accepted) :
    (s.post principal claimed).2.find claimed.id =
      some { claimed with sender := { claimed.sender with account := principal } } := by
  unfold post send at *
  split at h
  · next hnone =>
    unfold find
    rw [List.find?_append]
    have : s.ledger.find? (fun x => decide (x.id = claimed.id)) = none := by simpa [find] using hnone
    simp [this]
  · split at h <;> cases h

/-! ## Taking and acknowledging -/

theorem firstAt_some {s : State} {owner : Channel} {st : Stage} {d : Delivery}
    (h : s.firstAt owner st = some d) : d ∈ s.ledger ∧ d.channel = owner ∧ s.stage d.id = some st := by
  unfold firstAt at h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

theorem next_valid {s : State} (hs : s.Valid) (owner : Channel) : (s.next owner).2.Valid := by
  unfold next
  split
  · exact hs
  · split
    · next d hd =>
      obtain ⟨mem, -, staged⟩ := firstAt_some hd
      refine ⟨hs.unique, fun id => ?_⟩
      by_cases h : id = d.id
      · subst h
        simp only [Function.update_self, Option.isSome_some, true_iff]
        exact (hs.staged d.id).mp (by simp [staged])
      · simp only [Function.update_of_ne h]
        exact hs.staged id
    · exact hs

/-- `next` never presents a settled delivery. -/
theorem next_not_settled {s : State} {owner : Channel} {d : Delivery} {s' : State}
    (h : s.next owner = (.delivery d, s')) : s.stage d.id ≠ some .settled := by
  unfold next at h
  split at h
  · next d' hd => cases h; obtain ⟨-, -, st⟩ := firstAt_some hd; simp [st]
  · split at h
    · next d' hd => cases h; obtain ⟨-, -, st⟩ := firstAt_some hd; simp [st]
    · cases h

/-- Recovery: until it is acknowledged, `next` presents the same delivery again,
so a restart between `next` and `ack` loses nothing. -/
theorem next_stable {s : State} {owner : Channel} {d : Delivery} {s' : State}
    (h : s.next owner = (.delivery d, s')) : s'.next owner = (.delivery d, s') := by
  unfold next at h
  split at h
  · next d' hd => cases h; simp [next, hd]
  · next hnone =>
    split at h
    · next d' hd =>
      cases h
      obtain ⟨-, hch, -⟩ := firstAt_some hd
      -- After the take, the owner's ready deliveries are exactly this one.
      have this : ({ s with stage := Function.update s.stage d.id (some .ready) } : State).firstAt owner .ready
          = some d := by
        unfold firstAt at hnone hd ⊢
        rw [List.find?_eq_none] at hnone
        obtain ⟨hpd, pre, post, hsplit, hpre⟩ := List.find?_eq_some_iff_append.mp hd
        have hpend : s.stage d.id = some .pending := by simp at hpd; exact hpd.2
        refine List.find?_eq_some_iff_append.mpr ⟨by simp [hch], pre, post, hsplit, ?_⟩
        intro a ha
        have ha' : a ∈ s.ledger := by rw [hsplit]; simp [ha]
        by_cases hid : a.id = d.id
        · have hp := hpre a ha
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_and] at hp
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_and, hid,
            Function.update_self]
          intro hc
          exact absurd (hid ▸ hpend) (hp hc)
        · have hn := hnone a ha'
          simp only [decide_eq_true_eq, not_and] at hn
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_and,
            Function.update_of_ne hid]
          exact hn
      simp [next, this]
    · cases h

/-- `next` takes pending mail in arrival order: a taken delivery is the owner's
first pending one in the ledger. -/
theorem next_takes_first {s : State} {owner : Channel} {d : Delivery} {s' : State}
    (h : s.next owner = (.delivery d, s')) (hready : s.firstAt owner .ready = none) :
    s.firstAt owner .pending = some d := by
  unfold next at h
  rw [hready] at h
  simp only at h
  cases hp : s.firstAt owner .pending with
  | none => rw [hp] at h; cases h
  | some d' => rw [hp] at h; cases h; rfl

theorem ack_valid {s : State} (hs : s.Valid) (owner : Channel) (id : Occurrence) :
    (s.ack owner id).2.Valid := by
  unfold ack
  split
  · next d hd =>
    split
    · next hc =>
      refine ⟨hs.unique, fun x => ?_⟩
      by_cases hx : x = id
      · subst hx
        simp only [Function.update_self, Option.isSome_some, true_iff]
        exact (hs.staged x).mp (by simp [hc.2])
      · simp only [Function.update_of_ne hx]
        exact hs.staged x
    · exact hs
  · exact hs

/-- After a settling `ack`, the occurrence is settled and `next` never presents it. -/
theorem ack_settles {s : State} {owner : Channel} {id : Occurrence} {s' : State}
    (h : s.ack owner id = (.settled, s')) : s'.stage id = some .settled := by
  unfold ack at h
  split at h
  · split at h
    · cases h; simp
    · cases h
  · cases h

/-! ## Each inbox is a mailbox -/

/-- A ledger record read as an internet message. -/
def toMessage (d : Delivery) : Message :=
  { id := d.id, originator := d.sender.account ++ "/" ++ d.sender.agent, recipients := [d.channel],
    date := 0, subject := "", inReplyTo := [], references := [], body := d.body }

/-- The owner's inbox as a store-and-forward mailbox: its deliveries, and the
settled ones as handled. -/
def inbox (s : State) (owner : Channel) : Mailbox :=
  let mine := s.ledger.filter (fun d => d.channel = owner)
  { stored := mine.map toMessage,
    seen := (mine.filter (fun d => s.stage d.id = some .settled)).map Delivery.id }

theorem inbox_ids (s : State) (owner : Channel) :
    (s.inbox owner).ids = (s.ledger.filter (fun d => d.channel = owner)).map Delivery.id := by
  simp [inbox, Mailbox.ids, toMessage, Function.comp_def]

/-- Every inbox of a valid space is a valid mailbox. -/
theorem inbox_valid {s : State} (hs : s.Valid) (owner : Channel) : (s.inbox owner).Valid := by
  have nd : ((s.ledger.filter (fun d => d.channel = owner)).map Delivery.id).Nodup :=
    List.Nodup.sublist ((List.filter_sublist (l := s.ledger)).map Delivery.id) (by simpa [ids] using hs.unique)
  refine ⟨by rw [inbox_ids]; exact nd, ?_, ?_⟩
  · intro id hid
    rw [inbox_ids]
    simp only [inbox, List.mem_map, List.mem_filter] at hid ⊢
    obtain ⟨d, hd, rfl⟩ := hid
    exact ⟨d, hd.1, rfl⟩
  · simp only [inbox]
    exact List.Nodup.sublist ((List.filter_sublist).map Delivery.id) nd

end State

/-! ## Conditional commits: no lost update -/

/-- Content at a revision, as the native service versions a space. -/
structure Versioned (α : Type) where
  revision : Nat
  content : α

/-- Write a value computed from the content read at `read`: refused unless the
space is still at that revision. -/
def commitAt {α : Type} (v : Versioned α) (read : Nat) (value : α) : Option (Versioned α) :=
  if read = v.revision then some ⟨v.revision + 1, value⟩ else none

theorem commitAt_stale {α : Type} (v : Versioned α) (read : Nat) (value : α) (h : read ≠ v.revision) :
    commitAt v read value = none := by simp [commitAt, h]

theorem commitAt_current {α : Type} (v : Versioned α) (value : α) :
    commitAt v v.revision value = some ⟨v.revision + 1, value⟩ := by simp [commitAt]

/-- On the service's own rows, `commitAt` is `SpaceService.conditionalWrite`. -/
theorem commitAt_eq_conditionalWrite (store : Machines.SpaceService.Store) (read : Nat)
    (rows : List Nat) :
    commitAt ⟨store.revision, store.rows⟩ read rows =
      match Machines.SpaceService.conditionalWrite store store.identity read rows with
      | .ok s => some ⟨s.revision, s.rows⟩
      | .error _ => none := by
  by_cases h : read = store.revision <;> simp [commitAt, Machines.SpaceService.conditionalWrite, h]

/-- A client reads the space, or writes a transition of the content it last read. -/
inductive Event (κ α : Type)
  | read (client : κ)
  | write (client : κ) (step : α → α)

/-- The space, each client's last read, and the transitions committed so far. -/
structure World (κ α : Type) where
  space : Versioned α
  views : κ → Option (Versioned α)
  committed : List (α → α)

namespace World

variable {κ α : Type} [DecidableEq κ]

/-- A space no client has read yet. -/
def start (v : Versioned α) : World κ α := ⟨v, fun _ => none, []⟩

/-- One event under conditional commits. -/
def step (w : World κ α) : Event κ α → World κ α
  | .read c => { w with views := Function.update w.views c (some w.space) }
  | .write c f =>
    match w.views c with
    | none => w
    | some seen =>
      match commitAt w.space seen.revision (f seen.content) with
      | some v => { w with space := v, committed := w.committed ++ [f] }
      | none => w

/-- Events in order. -/
def run (w : World κ α) (events : List (Event κ α)) : World κ α := events.foldl step w

/-- Every view is from the past, and a view at the current revision shows the
current content. Revisions advancing on every commit is what keeps this true. -/
def Fresh (w : World κ α) : Prop :=
  ∀ c seen, w.views c = some seen →
    seen.revision ≤ w.space.revision ∧ (seen.revision = w.space.revision → seen.content = w.space.content)

/-- The space is the committed transitions applied in order to `init`. -/
def Chain (w : World κ α) (init : Versioned α) : Prop :=
  w.space.content = w.committed.foldl (fun x f => f x) init.content ∧
    w.space.revision = init.revision + w.committed.length

theorem step_preserves {w : World κ α} {init : Versioned α} (hf : w.Fresh) (hc : w.Chain init)
    (e : Event κ α) : (w.step e).Fresh ∧ (w.step e).Chain init := by
  cases e with
  | read c =>
    refine ⟨fun c' seen hv => ?_, hc⟩
    simp only [step] at hv ⊢
    by_cases h : c' = c
    · subst h
      simp only [Function.update_self, Option.some.injEq] at hv
      subst hv
      exact ⟨le_refl _, fun _ => rfl⟩
    · rw [Function.update_of_ne h] at hv
      exact hf c' seen hv
  | write c f =>
    simp only [step]
    split
    · exact ⟨hf, hc⟩
    · next seen hseen =>
      split
      · next v hv =>
        unfold commitAt at hv
        split at hv
        · next hread =>
          cases hv
          have same : seen.content = w.space.content := (hf c seen hseen).2 hread
          refine ⟨fun c' seen' hv' => ?_, ?_, ?_⟩
          · have := (hf c' seen' hv').1
            exact ⟨by simp only; omega, fun heq => absurd heq (by simp only; omega)⟩
          · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, same, hc.1]
          · simp only [List.length_append, List.length_singleton, hc.2]
            omega
        · cases hv
      · exact ⟨hf, hc⟩

/-- No lost update: from a space no client has read, whatever the interleaving
of reads and writes, the space holds the committed transitions applied in order
to its initial content, each to the content its client read, and the revision
counts them. -/
theorem run_no_lost_update (v : Versioned α) (events : List (Event κ α)) :
    ((start v : World κ α).run events).Chain v := by
  suffices ∀ (w : World κ α), w.Fresh → w.Chain v → (w.run events).Fresh ∧ (w.run events).Chain v from
    (this _ (fun _ _ h => by cases h) ⟨rfl, by simp [start]⟩).2
  induction events with
  | nil => exact fun w hf hc => ⟨hf, hc⟩
  | cons e rest ih =>
    intro w hf hc
    obtain ⟨hf', hc'⟩ := step_preserves hf hc e
    exact ih _ hf' hc'

/-- The same world with writes that skip the revision check. -/
def stepBlind (w : World κ α) : Event κ α → World κ α
  | .read c => { w with views := Function.update w.views c (some w.space) }
  | .write c f =>
    match w.views c with
    | none => w
    | some seen => { w with space := ⟨w.space.revision + 1, f seen.content⟩, committed := w.committed ++ [f] }

/-- Two clients read the same revision of a counter and each adds one. -/
def raceEvents : List (Event Nat Nat) := [.read 0, .read 1, .write 0 (· + 1), .write 1 (· + 1)]

/-- Without the check an update is lost: both writes go through, yet the counter
ends at one, not at the two that the committed transitions add up to. -/
example : let w := raceEvents.foldl stepBlind (start ⟨0, 0⟩ : World Nat Nat)
    w.space.content = 1 ∧ w.committed.foldl (fun x f => f x) 0 = 2 := by decide

/-- With the check, the second write is refused as stale and nothing is lost. -/
example : let w := (start ⟨0, 0⟩ : World Nat Nat).run raceEvents
    w.space.content = 1 ∧ w.committed.length = 1 := by decide

end World

end Mettapedia.Protocols.ClawMail
