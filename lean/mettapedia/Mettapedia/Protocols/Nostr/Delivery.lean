import Mettapedia.Protocols.Nostr.Mailbox
import Mettapedia.Protocols.Options.Weakest

/-!
# Delivery evidence: what a sender and a reader can know

A relay can store a message and never show it: nothing in Nostr obliges it. This file states what
follows for the reader, which cannot learn what is missing, and for the sender, which cannot take
the relay's word for delivery. It also says what remedies each: several relays, and keeping the
message until a receipt signed by the recipient arrives.

The worlds are whether the message was sent to each relay, and whether each relay hides it from
the reader. Policies decide from what is observable (`Options.Weakest`).

The theorems:
- `one_relay_cannot_certify`: from one relay's empty answer, no safe policy concludes that nothing
  is missing, since a relay that hides the message answers the same.
- `honest_relay_certifies`: when the message goes to every relay and one relay does not hide it,
  an empty answer from all of them means nothing was sent, and the weakest policy accepts it.
  `all_hide_breaks` is the mutant: if every relay hides it, the answers are empty although the
  message was sent.
- Three levels of evidence:
  - a relay's acceptance shows nothing of the recipient (`relay_ok_not_ingested`);
  - a receipt signed by the recipient's uncompromised key was composed by the recipient
    (`receipt_composed`, from `Nostr.Mailbox.receipt_sound`'s assumption);
  - so a sender that keeps a message until such a receipt arrives never drops a message the
    recipient lacks (`custody_until_receipt`), and it is the weakest release that never does
    (`safe_release_le`). The mutant, which drops at the relay's acceptance, loses a message that a
    hiding relay accepted (`drop_at_ok_loses`).

When receipts travel in NIP-17 gift wraps, `receipt_composed` applies to the inner seal, as
`Nostr.GiftWrap.unwrap_authentic` gives it, and never to the wrap, whose key is nobody's.

Not modelled: timing and liveness, the network between relays, and readers that read only some of
the relays.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.Delivery

open Mettapedia.Protocols.Options.Weakest

/-! ## The reader -/

/-- A world with `n` relays: for each, whether the message was sent there, and whether the relay
hides it from the reader. -/
structure World (n : ℕ) where
  sent : Fin n → Bool
  hides : Fin n → Bool

/-- What the reader sees: for each relay, whether it shows the message. -/
def World.shows {n : ℕ} (w : World n) : Fin n → Bool := fun i => w.sent i && !w.hides i

/-- Nothing is missing: if the message was sent anywhere, some relay shows it. -/
def World.Complete {n : ℕ} (w : World n) : Prop :=
  (∃ i, w.sent i = true) → ∃ i, w.shows i = true

/-- The answers in which no relay shows the message. -/
def empty (n : ℕ) : Fin n → Bool := fun _ => false

/-- **One relay.** From an empty answer, no safe policy concludes that nothing is missing: a
relay that received the message and hides it gives the same answer. -/
theorem one_relay_cannot_certify :
    ¬ weakest (World.shows : World 1 → Fin 1 → Bool) World.Complete (empty 1) := by
  refine refuse_iff.2 ⟨⟨fun _ => true, fun _ => true⟩, ?_, ?_⟩
  · funext i
    simp [World.shows, empty]
  · intro h
    obtain ⟨i, hi⟩ := h ⟨0, rfl⟩
    simp [World.shows] at hi

/-- The worlds the sender's rule allows: the message goes to every relay, and some relay does
not hide it. -/
def World.Covered {n : ℕ} (w : World n) : Prop := (∀ i, w.sent i = true) ∧ ∃ i, w.hides i = false

/-- **Several relays.** Among covered worlds, every answer is trustworthy: the weakest policy
accepts the empty answer, since in a covered world the honest relay shows the message. -/
theorem honest_relay_certifies {n : ℕ} :
    weakest (fun w : {w : World n // w.Covered} => w.1.shows) (fun w => w.1.Complete) (empty n) := by
  intro w _ _
  obtain ⟨hs, i, hi⟩ := w.2
  exact ⟨i, by simp [World.shows, hs i, hi]⟩

/-- In a covered world nothing is missing. -/
theorem covered_complete {n : ℕ} {w : World n} (h : w.Covered) : w.Complete := by
  intro _
  obtain ⟨hs, i, hi⟩ := h
  exact ⟨i, by simp [World.shows, hs i, hi]⟩

/-- **Mutant: every relay hides.** The message went to both relays, both hide it, and the reader's
answer is empty. -/
theorem all_hide_breaks :
    ∃ w : World 2, (∀ i, w.sent i = true) ∧ w.shows = empty 2 ∧ ¬ w.Complete := by
  refine ⟨⟨fun _ => true, fun _ => true⟩, fun _ => rfl, ?_, ?_⟩
  · funext i
    simp [World.shows, empty]
  · intro h
    obtain ⟨i, hi⟩ := h ⟨0, rfl⟩
    simp [World.shows] at hi

/-! ## The sender -/

/-- What becomes of one message: whether the relay accepted it, whether the relay showed it to
the recipient, whether the recipient ingested it, and whether the recipient's receipt reached the
sender. The recipient ingests only what it is shown, and a receipt, signed by the recipient
(`receipt_composed`), comes only for what it ingested. A receipt can be lost or hidden. -/
structure Fate where
  accepted : Bool
  shown : Bool
  ingested : Bool
  receipt : Bool
  ingest_shown : ingested = true → shown = true
  receipt_ingested : receipt = true → ingested = true

/-- **A relay's acceptance shows nothing of the recipient.** A relay can accept a message and never
show it. -/
theorem relay_ok_not_ingested : ∃ f : Fate, f.accepted = true ∧ f.ingested = false :=
  ⟨⟨true, false, false, false, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
    rfl, rfl⟩

open Mettapedia.Protocols.Nostr in
/-- **A signed receipt.** A valid receipt under the recipient's uncompromised key was composed by
the recipient, exactly as it reads (`Nostr.authentic`). An honest recipient composes a receipt only
for what it ingested, so the receipt is evidence of ingestion. -/
theorem receipt_composed {P : Primitives} (A : Authorship P) (cf : P.CollisionFree) {r : Event}
    (hv : r.Valid P) (hk : ¬ A.compromised r.pubkey) : A.authored r.toUnsigned :=
  authentic A cf hv hk

/-- A sender's rule for releasing a message from its custody, given what it has seen: the relay's
acceptance, and a receipt from the recipient. -/
abbrev Release := Bool → Bool → Bool

/-- Keep the message until the recipient's receipt arrives. -/
def untilReceipt : Release := fun _ receipt => receipt

/-- Drop it once the relay accepts it. -/
def atAccept : Release := fun accepted _ => accepted

/-- A release is safe when it never lets go of a message the recipient lacks. -/
def SafeRelease (rel : Release) : Prop := ∀ f : Fate, rel f.accepted f.receipt = true → f.ingested = true

/-- **Custody until the receipt** never drops a message the recipient lacks. -/
theorem custody_until_receipt : SafeRelease untilReceipt := fun f h => f.receipt_ingested h

/-- **Mutant: dropping at the relay's acceptance** loses a message the relay accepted and hid. -/
theorem drop_at_ok_loses : ¬ SafeRelease atAccept := by
  intro h
  have := h ⟨true, false, false, false, fun h => absurd h (by decide),
    fun h => absurd h (by decide)⟩ rfl
  exact absurd this (by decide)

/-- Custody until the receipt is the weakest safe release: whenever any safe release lets a
message go, so does it. -/
theorem safe_release_le {rel : Release} (h : SafeRelease rel) {accepted receipt : Bool}
    (hr : rel accepted receipt = true) : untilReceipt accepted receipt = true := by
  cases receipt
  · have := h ⟨accepted, false, false, false, fun h => absurd h (by simp),
      fun h => absurd h (by simp)⟩ hr
    exact absurd this (by simp)
  · rfl

end Mettapedia.Protocols.Nostr.Delivery
