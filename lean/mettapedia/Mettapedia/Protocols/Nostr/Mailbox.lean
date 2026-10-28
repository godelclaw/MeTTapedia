import Mettapedia.Protocols.Nostr.Event
import Mettapedia.Protocols.Mail.Message

/-!
# Agent mail over Nostr

The mailbox of NuNet's agent fabric (`nostr-mailbox`). A message is a kind-3838
event addressed to one recipient by a `p` tag. Its content is the NIP-44
encryption, for that recipient, of a small record: subject, body, and for team
messages a type and a task. A reply names its parent in an `e` tag. Receipts are
kind-7 reactions that name the message (`e`), its author (`p`) and the fact they
report (`ack`: delivered or read). Members find each other in a registry of
names and keys.

The client keeps a fetched message when it is well formed and signed, addressed
to the reader, signed by a registered key, and opens (`accept`). The model files
each kept message as an internet message (`Mail.Message`) whose originator is
the registry name of the signing key (`render`). The archived originator drives
what follows: the team protocol's check of who may send which type, reply
routing, and the watcher's control mail, such as a parent's `limits`.

The theorems:
- `no_impersonation`: mail archived as from a member whose key is uncompromised
  was composed by that member, given a registry that names each member once.
- `limits_from_parent`: the watcher's authority follows. Limits applied as a
  parent's were composed by the parent.
- `receipt_sound`: a receipt is believed only from the addressee of the message
  it names, and when the addressee's key is uncompromised, the addressee
  composed it.

The identity of a sender rests on the key alone. A tag is only the signer's
claim, so no tag may name the originator.

Encryption appears only as the reader's opening function. Its secrecy is a
separate question.
-/

namespace Mettapedia.Protocols.Nostr

/-- Kind 3838: an agent mail message. -/
def kindMail : Nat := 3838

/-- The sealed record a message carries. -/
structure Letter where
  subject : String
  body : String
  /-- A team message's type, such as `limits` or `reset`. -/
  type : Option String := none
  task : Option String := none
deriving DecidableEq, Repr

/-- NIP-44 opening by the reader's key and the peer's key; `none` when the
ciphertext does not open to a letter. -/
abbrev Opener := PubKey → PubKey → String → Option Letter

/-- The registry: member names with their keys. -/
abbrev Registry := List (String × PubKey)

/-- The first name the registry gives a key. -/
def nameOf (reg : Registry) (k : PubKey) : Option String := (reg.find? (·.2 = k)).map (·.1)

theorem nameOf_some {reg : Registry} {k : PubKey} {n : String} (h : nameOf reg k = some n) :
    (n, k) ∈ reg := by
  unfold nameOf at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have hk : p.2 = k := by simpa using List.find?_some hp
  rw [← hk]
  exact List.mem_of_find?_eq_some hp

/-- In a registry that names each member once, a name has one key. -/
theorem key_unique {reg : Registry} (hu : (reg.map Prod.fst).Nodup) {n : String} {k k' : PubKey}
    (h : (n, k) ∈ reg) (h' : (n, k') ∈ reg) : k = k' := by
  have := List.inj_on_of_nodup_map hu h h' rfl
  simpa using this

/-- The key whose secret opens a message for its reader: the author's, or for the
reader's own sent copy, the addressee's. -/
def peerOf (me : PubKey) (e : Event) : PubKey :=
  if e.pubkey = me then (tagValues e.tags "p").headD "" else e.pubkey

/-- A fetched event the client keeps, with its letter: a well-formed signed mail
addressed to the reader, signed by a registered key, that opens. -/
def accept (P : Primitives) (opener : Opener) (reg : Registry) (me : PubKey) (e : Event) :
    Option Letter :=
  if e.check P && e.kind == kindMail && (tagValues e.tags "p").contains me && (nameOf reg e.pubkey).isSome
  then opener me (peerOf me e) e.content
  else none

theorem accept_some {P : Primitives} {opener : Opener} {reg : Registry} {me : PubKey} {e : Event}
    {l : Letter} (h : accept P opener reg me e = some l) :
    e.Valid P ∧ e.kind = kindMail ∧ me ∈ tagValues e.tags "p" ∧ ∃ n, nameOf reg e.pubkey = some n := by
  unfold accept at h
  split at h
  · next hc =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, Option.isSome_iff_exists] at hc
    obtain ⟨⟨⟨hv, hk⟩, hp⟩, hn⟩ := hc
    exact ⟨(Event.check_iff P e).mp hv, hk, hp, hn⟩
  · cases h

/-- The archived message, with the originator named by the signing key. -/
def render (reg : Registry) (e : Event) (l : Letter) : Mail.Message :=
  { id := e.id
    originator := (nameOf reg e.pubkey).getD "unknown"
    recipients := ((tagValues e.tags "p").head?.map fun k => (nameOf reg k).getD k).toList
    date := e.createdAt.toNat
    subject := l.subject
    inReplyTo := (tagValues e.tags "e").head?.toList
    references := []
    body := l.body }

/-- The watcher applies a `limits` message from the avatar's parent, as the
archive names the sender. -/
def appliesLimits (parent : String) (m : Mail.Message) (l : Letter) : Bool :=
  m.originator == parent && l.type == some "limits"

/-- No impersonation: mail archived as from a member whose key is uncompromised
was signed by that member's key and composed by its owner. -/
theorem no_impersonation {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    {opener : Opener} {reg : Registry} (hu : (reg.map Prod.fst).Nodup) {me : PubKey} {e : Event}
    {l : Letter} (ha : accept P opener reg me e = some l) {n : String} {k : PubKey}
    (hn : (render reg e l).originator = n) (hk : (n, k) ∈ reg) (hc : ¬ A.compromised k) :
    e.pubkey = k ∧ A.authored e.toUnsigned := by
  obtain ⟨hv, -, -, n', hn'⟩ := accept_some ha
  have : n' = n := by simpa [render, hn'] using hn
  subst this
  have hpk : e.pubkey = k := key_unique hu (nameOf_some hn') hk
  exact ⟨hpk, authentic A cf hv (hpk ▸ hc)⟩

/-- The watcher's authority follows: limits applied as a parent's were composed
by the parent. -/
theorem limits_from_parent {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    {opener : Opener} {reg : Registry} (hu : (reg.map Prod.fst).Nodup) {me : PubKey} {e : Event}
    {l : Letter} (ha : accept P opener reg me e = some l) {parent : String} {k : PubKey}
    (hk : (parent, k) ∈ reg) (hc : ¬ A.compromised k)
    (h : appliesLimits parent (render reg e l) l = true) : A.authored e.toUnsigned := by
  simp only [appliesLimits, Bool.and_eq_true, beq_iff_eq] at h
  exact (no_impersonation A cf hu ha h.1 hk hc).2

/-! ## Receipts -/

/-- The message a receipt names and the fact it reports, delivered or read. -/
def receiptFor (r : Event) : Option (EventId × String) :=
  match (tagValues r.tags "e").head?, (tagValues r.tags "ack").head? with
  | some m, some st => if st = "delivered" ∨ st = "read" then some (m, st) else none
  | _, _ => none

/-- The sender records a receipt that is a well-formed signed reaction from a
registered key, names a message it sent and a fact, and whose signer is the
addressee of that message. -/
def believes (P : Primitives) (reg : Registry) (sent : List Mail.Message) (r : Event) :
    Option (EventId × String) :=
  match receiptFor r, nameOf reg r.pubkey with
  | some (m, st), some who =>
    if r.check P && r.kind == kindReaction && sent.any (fun s => s.id == m && s.recipients.head? == some who)
    then some (m, st) else none
  | _, _ => none

/-- A believed receipt comes from the addressee of the message it names, and when
the addressee's key is uncompromised, the addressee composed it. -/
theorem receipt_sound {P : Primitives} (A : Authorship P) (cf : P.CollisionFree) {reg : Registry}
    {sent : List Mail.Message} {r : Event} {m : EventId} {st : String}
    (h : believes P reg sent r = some (m, st)) :
    ∃ s ∈ sent, s.id = m ∧ ∃ who, s.recipients.head? = some who ∧ (who, r.pubkey) ∈ reg ∧
      (¬ A.compromised r.pubkey → A.authored r.toUnsigned) := by
  unfold believes at h
  split at h
  · next m' st' who hr hwho =>
    split at h
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hc
      obtain ⟨⟨hv, -⟩, s, hs, hid, hto⟩ := hc
      exact ⟨s, hs, hid, who, hto, nameOf_some hwho,
        fun hcomp => authentic A cf ((Event.check_iff P r).mp hv) hcomp⟩
    · cases h
  · cases h

end Mettapedia.Protocols.Nostr
