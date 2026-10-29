import Mettapedia.Protocols.ClawMail

/-!
# Idempotent submission: an uncertain send can be retried

A sender whose request got no answer does not know whether it took effect.
- RFC 5322 §3.6.4: a `Message-ID` is unique, guaranteed by the host that makes
  it, and names exactly one version of one message.
- RFC 8621 §4.8 (`Email/import`): a server MAY refuse a second Email with the
  same Message-ID; it then answers `alreadyExists` with the id of the existing
  one.
- RFC 8620 §5.3: a creation id names a record for the rest of one API request.
  The server keeps the map for the duration of the request, so it gives a
  retried request nothing to recognise.

The model: a sender retries one message until an answer arrives; each attempt
either reaches the server or is lost, and an answer may be lost too. The
server is claw-mail's ledger (`ClawMail.State.send`), which deduplicates by the
occurrence identity the sender chose, as a Message-ID deduplicating store
does.

The theorems:
- `retry_once`: retried under one identity, however the attempts and answers
  fall, the message is in the ledger exactly once, as sent, and every answer the
  sender sees is `accepted` or `duplicate`.
- Mutants: a fresh identity for each attempt makes a second message when an
  answer is lost (`fresh_ids_duplicate`), and so do request-scoped creation ids
  (`creation_ids_duplicate`). A server that refuses a second Email with the
  same Message-ID keeps one (`import_dedup_once`).

§5's statement names JMAP creation ids among the mechanisms. Across requests
they do not have the property (`creation_ids_duplicate`): the identity must be
one the server keeps beyond the request.

Not modelled: the answer's content beyond its kind, and conflicting resends,
which `ClawMail.send_conflict` covers.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Mail.Submission

open Mettapedia.Protocols

/-- Attempts in order: `true` reached the server. The ledger after them, and the
answers produced, lost or not. -/
def attempts (d : ClawMail.Delivery) : ClawMail.State → List Bool →
    ClawMail.State × List ClawMail.State.SendResult
  | s, [] => (s, [])
  | s, true :: rest =>
    ((attempts d (s.send d).2 rest).1, (s.send d).1 :: (attempts d (s.send d).2 rest).2)
  | s, false :: rest => attempts d s rest

/-- How many ledger records carry an identity. -/
def count (s : ClawMail.State) (id : ClawMail.Occurrence) : Nat := (s.ids.filter (· = id)).length

theorem send_fresh {s : ClawMail.State} {d : ClawMail.Delivery} (h : s.find d.id = none) :
    s.send d = (.accepted, ⟨s.ledger ++ [d], Function.update s.stage d.id (some .pending)⟩) := by
  simp [ClawMail.State.send, h]

theorem find_after_send {s : ClawMail.State} {d : ClawMail.Delivery} (h : s.find d.id = none) :
    (s.send d).2.find d.id = some d := by
  rw [send_fresh h]
  unfold ClawMail.State.find at *
  rw [List.find?_append, h]
  simp

/-- Once the message is in the ledger as sent, further attempts change nothing
and are answered `duplicate`. -/
theorem attempts_stored {d : ClawMail.Delivery} :
    ∀ (bs : List Bool) (s : ClawMail.State), s.find d.id = some d →
      attempts d s bs = (s, bs.filter id |>.map fun _ => .duplicate)
  | [], _, _ => rfl
  | true :: rest, s, h => by
    have hs : s.send d = (.duplicate, s) := by simp [ClawMail.State.send, h]
    simp only [attempts, hs, attempts_stored rest s h]
    simp
  | false :: rest, s, h => by
    simp only [attempts, attempts_stored rest s h]
    simp

theorem count_send {s : ClawMail.State} {d : ClawMail.Delivery} (h : s.find d.id = none) :
    count (s.send d).2 d.id = count s d.id + 1 := by
  rw [send_fresh h]
  simp [count, ClawMail.State.ids, List.filter_append]

/-- **Retrying is safe**: from a ledger without the identity, any pattern of
attempts that reaches the server at least once leaves the message in the
ledger exactly once, as sent; the first answer is `accepted`, every later one
`duplicate`. -/
theorem retry_once (d : ClawMail.Delivery) :
    ∀ (bs : List Bool) (s : ClawMail.State), s.Valid → s.find d.id = none → true ∈ bs →
      (attempts d s bs).1.find d.id = some d ∧ count (attempts d s bs).1 d.id = 1 ∧
        (attempts d s bs).2 = .accepted :: ((bs.filter id).tail.map fun _ => .duplicate)
  | [], _, _, _, h => by simp at h
  | false :: rest, s, hv, hn, h => by
    simp only [attempts, List.filter_cons, Bool.false_eq_true, if_false, id]
    exact retry_once d rest s hv hn (by simpa using h)
  | true :: rest, s, hv, hn, _ => by
    have hst := attempts_stored rest (s.send d).2 (find_after_send hn)
    have hc : count s d.id = 0 := by
      simp only [count, List.length_eq_zero_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
      exact fun x hx heq => ClawMail.State.find_none.mp hn (heq ▸ hx)
    refine ⟨?_, ?_, ?_⟩
    · simp only [attempts, hst]; exact find_after_send hn
    · simp only [attempts, hst]; rw [count_send hn, hc]
    · simp only [attempts]
      rw [hst]
      simp [send_fresh hn]

/-! ## Examples and mutants -/

/-- A delivery. -/
def note : ClawMail.Delivery := ⟨"m1", "inbox", ⟨"account", "agent"⟩, "hello"⟩

/-- Lost, then reached with the answer lost, then reached: the hypotheses of
`retry_once` meet, there is one record, and the sender's answer is `duplicate`. -/
example : count (attempts note .empty [false, true, true]).1 "m1" = 1 ∧
    (attempts note .empty [false, true, true]).2 = [.accepted, .duplicate] := by
  obtain ⟨-, h1, h2⟩ := retry_once note [false, true, true] .empty ClawMail.State.empty_valid rfl (by decide)
  exact ⟨h1, h2⟩

/-- Each attempt under a fresh identity. -/
def attemptsFresh (d : ClawMail.Delivery) : Nat → ClawMail.State → List Bool → ClawMail.State
  | _, s, [] => s
  | n, s, true :: rest => attemptsFresh d (n + 1) (s.send { d with id := d.id ++ "." ++ toString n }).2 rest
  | n, s, false :: rest => attemptsFresh d (n + 1) s rest

/-- With a fresh identity per attempt, a lost answer and a retry make two
records of one message. -/
theorem fresh_ids_duplicate :
    ((attemptsFresh note 0 .empty [true, true]).ledger.filter (·.body = "hello")).length = 2 := by
  decide

/-- A server that assigns its own ids, with creation ids that last one request
(RFC 8620 §5.3), and optionally refusing a second Email with a Message-ID it
holds (RFC 8621 §4.8). -/
structure Jmap where
  next : Nat
  records : List (Nat × MessageId)

/-- One request creating an Email with Message-ID `mid`. Its creation id is
forgotten when the request ends, so it plays no part here. -/
def Jmap.create (dedup : Bool) (S : Jmap) (mid : MessageId) : Jmap :=
  if dedup && S.records.any (·.2 == mid) then S else ⟨S.next + 1, S.records ++ [(S.next, mid)]⟩

/-- A request retried after its answer was lost makes a second Email. -/
theorem creation_ids_duplicate : (((Jmap.mk 0 []).create false "m1").create false "m1").records.length = 2 := by
  decide

/-- A server refusing a second Email with the same Message-ID keeps one. -/
theorem import_dedup_once : (((Jmap.mk 0 []).create true "m1").create true "m1").records.length = 1 := by
  decide

end Mettapedia.Protocols.Mail.Submission
