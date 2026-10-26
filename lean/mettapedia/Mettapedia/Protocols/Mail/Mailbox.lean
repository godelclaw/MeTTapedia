import Mettapedia.Protocols.Mail.Message

/-!
# A store-and-forward mailbox

The delivery side that an SMTP receiver and an IMAP mailbox share. An accepted
message is stored before anything acknowledges it, a message that arrives twice
is filed once, and the reader marks what it has handled. Receipts follow the
same order: a delivery receipt only for a stored message, a read receipt only
for a handled one (the disposition-notification discipline of RFC 8098).

Affeldt and Kobayashi verified an SMTP receiver in Coq ("A Coq Library for
Verification of Concurrent Programs", 2004), with reliability meaning that
accepted mail is saved to the queue. `deliver_holds` and `deliver_keeps` state
that property for this mailbox. Identifier-based deduplication then turns
at-least-once arrival into exactly-once filing (`deliverAll_ids`).
-/

namespace Mettapedia.Protocols.Mail

/-- Stored messages in arrival order, and the identifiers the reader has handled. -/
structure Mailbox where
  stored : Log
  seen : List MessageId
deriving Repr

namespace Mailbox

/-- The empty mailbox. -/
def empty : Mailbox := ⟨[], []⟩

/-- Identifiers of the stored messages, in arrival order. -/
def ids (b : Mailbox) : List MessageId := b.stored.map Message.id

/-- Accept a message: file it unless one with its identifier is already stored. -/
def deliver (b : Mailbox) (m : Message) : Mailbox :=
  if m.id ∈ b.ids then b else { b with stored := b.stored ++ [m] }

/-- Mark a stored, unhandled message as handled; anything else changes nothing. -/
def ack (b : Mailbox) (id : MessageId) : Mailbox :=
  if id ∈ b.ids ∧ id ∉ b.seen then { b with seen := b.seen ++ [id] } else b

/-- Stored messages not yet handled, oldest first. -/
def unread (b : Mailbox) : List Message := b.stored.filter (fun m => m.id ∉ b.seen)

/-- A delivery receipt may be sent exactly for stored messages. -/
def mayReceiptDelivered (b : Mailbox) (id : MessageId) : Bool := id ∈ b.ids

/-- A read receipt may be sent exactly for handled messages. -/
def mayReceiptRead (b : Mailbox) (id : MessageId) : Bool := id ∈ b.seen

/-- Deliver a sequence of messages in order, duplicates included. -/
def deliverAll (b : Mailbox) (ms : List Message) : Mailbox := ms.foldl deliver b

/-- The mailbox invariant: unique stored identifiers, and handled ⊆ stored. -/
structure Valid (b : Mailbox) : Prop where
  unique : b.ids.Nodup
  seenStored : ∀ id ∈ b.seen, id ∈ b.ids
  seenUnique : b.seen.Nodup

theorem empty_valid : empty.Valid := ⟨List.nodup_nil, by simp [empty], List.nodup_nil⟩

theorem ids_deliver (b : Mailbox) (m : Message) :
    (b.deliver m).ids = if m.id ∈ b.ids then b.ids else b.ids ++ [m.id] := by
  unfold deliver ids; split <;> simp

/-- Reliability: an accepted message is stored. -/
theorem deliver_holds (b : Mailbox) (m : Message) : m.id ∈ (b.deliver m).ids := by
  rw [ids_deliver]; split
  · assumption
  · simp

/-- Nothing stored is lost by a delivery. -/
theorem deliver_keeps (b : Mailbox) (m : Message) {id : MessageId} (h : id ∈ b.ids) :
    id ∈ (b.deliver m).ids := by
  rw [ids_deliver]; split
  · exact h
  · exact List.mem_append_left _ h

/-- Delivering the same message again changes nothing. -/
theorem deliver_idempotent (b : Mailbox) (m : Message) : (b.deliver m).deliver m = b.deliver m := by
  have := deliver_holds b m
  unfold deliver at *
  simp only [this, if_true]

theorem deliver_valid {b : Mailbox} (hb : b.Valid) (m : Message) : (b.deliver m).Valid := by
  by_cases h : m.id ∈ b.ids
  · simpa [deliver, h] using hb
  · refine ⟨?_, ?_, ?_⟩
    · rw [ids_deliver, if_neg h]
      exact List.Nodup.append hb.unique (List.nodup_singleton _) (by simpa using h)
    · intro id hid
      exact deliver_keeps b m (hb.seenStored id (by simpa [deliver, h] using hid))
    · simpa [deliver, h] using hb.seenUnique

theorem ack_valid {b : Mailbox} (hb : b.Valid) (id : MessageId) : (b.ack id).Valid := by
  unfold ack
  split
  · next h =>
    refine ⟨by simpa [ids] using hb.unique, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · simpa [ids] using hb.seenStored x hx
      · simpa [ids] using h.1
    · exact List.Nodup.append hb.seenUnique (List.nodup_singleton _) (by simpa using h.2)
  · exact hb

/-- Handling a message never changes what is stored. -/
theorem ack_stored (b : Mailbox) (id : MessageId) : (b.ack id).stored = b.stored := by
  unfold ack; split <;> rfl

/-- Receipt soundness: a delivery receipt implies the message is stored, and a
read receipt, in a valid mailbox, implies it was stored and handled. -/
theorem receiptDelivered_sound {b : Mailbox} {id : MessageId}
    (h : b.mayReceiptDelivered id = true) : id ∈ b.ids := by
  simpa [mayReceiptDelivered] using h

theorem receiptRead_sound {b : Mailbox} (hb : b.Valid) {id : MessageId}
    (h : b.mayReceiptRead id = true) : id ∈ b.seen ∧ id ∈ b.ids := by
  have hs : id ∈ b.seen := by simpa [mayReceiptRead] using h
  exact ⟨hs, hb.seenStored id hs⟩

theorem deliverAll_valid {b : Mailbox} (hb : b.Valid) (ms : List Message) :
    (b.deliverAll ms).Valid := by
  induction ms generalizing b with
  | nil => exact hb
  | cons m ms ih => exact ih (deliver_valid hb m)

theorem mem_ids_deliverAll (b : Mailbox) (ms : List Message) (id : MessageId) :
    id ∈ (b.deliverAll ms).ids ↔ id ∈ b.ids ∨ id ∈ ms.map Message.id := by
  induction ms generalizing b with
  | nil => simp [deliverAll]
  | cons m ms ih =>
    show id ∈ ((b.deliver m).deliverAll ms).ids ↔ _
    rw [ih, ids_deliver]
    by_cases h : m.id ∈ b.ids
    · rw [if_pos h]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | rfl | h1)
        · exact Or.inl h1
        · exact Or.inl h
        · exact Or.inr h1
    · rw [if_neg h]
      simp only [List.map_cons, List.mem_cons, List.mem_append]
      tauto

/-- Exactly once: delivering any sequence, repetitions included, files each
identifier that arrived exactly once and nothing else. -/
theorem deliverAll_ids (ms : List Message) :
    (empty.deliverAll ms).ids.Nodup ∧
      ∀ id, id ∈ (empty.deliverAll ms).ids ↔ id ∈ ms.map Message.id := by
  refine ⟨(deliverAll_valid empty_valid ms).unique, fun id => ?_⟩
  rw [mem_ids_deliverAll]; simp [empty, ids]

end Mailbox

end Mettapedia.Protocols.Mail
