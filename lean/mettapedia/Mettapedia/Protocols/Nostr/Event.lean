import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Fintype.EquivFin

/-!
# Nostr events (NIP-01)

A Nostr event is a signed record: an author key, a creation time, a kind, tags
and content. Its identifier is the SHA-256 hash of the serialization
`[0, pubkey, created_at, kind, tags, content]`, and its signature is a BIP-340
Schnorr signature on that identifier. Relays and clients accept an event when
both check (`Event.check`).

Hashing and signing are modelled symbolically, by the two properties the
protocols rely on, not as computations:
- the hash is collision free (`Primitives.CollisionFree`), so an identifier names
  one set of signed fields;
- a signature that verifies under a key whose secret the attacker lacks was made
  by the key's owner, on the identifier of an event that owner composed
  (`Authorship`).

Under these, a valid event is authentic in every signed field (`authentic`).
That includes its tags: a tag shows who wrote it, not that what it claims is
true, so a name the sender writes into a tag cannot establish who the sender is.
The signature itself is not signed. BIP-340 signing is randomized, so one event
can carry several valid signatures (`signature_not_unique`), and anything keyed
by the identifier must depend only on the signed fields (`signed_fields_eq`).
-/

namespace Mettapedia.Protocols.Nostr

/-- A 32-byte x-only public key, in hex. -/
abbrev PubKey := String
/-- An event identifier: 32 bytes of hash, in hex. -/
abbrev EventId := String
/-- A 64-byte Schnorr signature, in hex. -/
abbrev Sig := String
/-- A tag: a name followed by values. -/
abbrev Tag := List String

/-- The fields an event identifier commits to. -/
structure Unsigned where
  pubkey : PubKey
  /-- Seconds since the epoch. -/
  createdAt : Int
  kind : Nat
  tags : List Tag
  content : String
deriving DecidableEq, Repr

/-- A signed event. -/
structure Event extends Unsigned where
  id : EventId
  sig : Sig
deriving DecidableEq, Repr

/-- The values of the tags with a given name, in order: the second element of
each tag whose first element is the name. -/
def tagValues (tags : List Tag) (name : String) : List String :=
  tags.filterMap fun t =>
    match t with
    | n :: v :: _ => if n = name then some v else none
    | _ => none

/-- Kind 5: a deletion request (NIP-09). -/
def kindDeletion : Nat := 5
/-- Kind 7: a reaction (NIP-25). -/
def kindReaction : Nat := 7
/-- Kind 22242: a relay sign-in (NIP-42). -/
def kindAuth : Nat := 22242

/-- Ephemeral kinds (NIP-01) are relayed and not stored. -/
def ephemeral (kind : Nat) : Bool := 20000 ≤ kind && kind < 30000

/-- The two primitives an event depends on. -/
structure Primitives where
  /-- SHA-256 of the event serialization. -/
  hash : Unsigned → EventId
  /-- BIP-340 verification of a signature on an identifier under a key. -/
  verify : PubKey → EventId → Sig → Bool

/-- A well-formed event: the identifier hashes the signed fields, and the
signature verifies on the identifier under the event's key. -/
def Event.check (P : Primitives) (e : Event) : Bool :=
  e.id == P.hash e.toUnsigned && P.verify e.pubkey e.id e.sig

/-- `Event.check` as a proposition. -/
def Event.Valid (P : Primitives) (e : Event) : Prop :=
  e.id = P.hash e.toUnsigned ∧ P.verify e.pubkey e.id e.sig = true

theorem Event.check_iff (P : Primitives) (e : Event) : e.check P = true ↔ e.Valid P := by
  simp [Event.check, Event.Valid]

/-- Collision freedom, the symbolic reading of a collision-resistant hash. -/
def Primitives.CollisionFree (P : Primitives) : Prop := Function.Injective P.hash

/-- The symbolic signature assumption. `authored` holds of the events key owners
composed and signed, and `compromised` of the keys whose secrets the attacker
holds. A signature that verifies under any other key is its owner's, on the
identifier of an event the owner composed. -/
structure Authorship (P : Primitives) where
  authored : Unsigned → Prop
  compromised : PubKey → Prop
  sound : ∀ k d s, P.verify k d s = true → ¬ compromised k →
    ∃ u, authored u ∧ u.pubkey = k ∧ P.hash u = d

/-- A collision-free hash exists: events are countable and identifiers are not
finite in number. Used to build examples that satisfy `CollisionFree`. -/
theorem exists_injective_hash : ∃ h : Unsigned → EventId, Function.Injective h := by
  have hs : Function.Injective fun s : String => s.toList.map Char.toNat := fun a b hab =>
    String.toList_injective (List.map_injective_iff.mpr (fun _ _ h => Char.toNat_inj.mp h) hab)
  have : Countable String := hs.countable
  have hu : Function.Injective fun u : Unsigned => (u.pubkey, u.createdAt, u.kind, u.tags, u.content) := by
    rintro ⟨⟩ ⟨⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    rfl
  have : Countable Unsigned := hu.countable
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat Unsigned
  exact ⟨Infinite.natEmbedding String ∘ f, (Infinite.natEmbedding String).injective.comp hf⟩

/-- Authenticity: a valid event under an uncompromised key was composed by that
key's owner, exactly as it reads, tags and content included. -/
theorem authentic {P : Primitives} (A : Authorship P) (cf : P.CollisionFree) {e : Event}
    (hv : e.Valid P) (hk : ¬ A.compromised e.pubkey) : A.authored e.toUnsigned := by
  obtain ⟨u, hu, -, hh⟩ := A.sound e.pubkey e.id e.sig hv.2 hk
  have : u = e.toUnsigned := cf (hh.trans hv.1)
  exact this ▸ hu

/-- Valid events with one identifier agree on every signed field. -/
theorem signed_fields_eq {P : Primitives} (cf : P.CollisionFree) {e e' : Event}
    (hv : e.Valid P) (hv' : e'.Valid P) (h : e.id = e'.id) : e.toUnsigned = e'.toUnsigned :=
  cf (hv.1.symm.trans (h.trans hv'.1))

/-- The signature is not determined by the identifier: two valid copies of one
event can differ in their signatures alone. The hash plays no part; only the
verifier's acceptance of more than one signature does. -/
theorem signature_not_unique : ∃ (P : Primitives) (e e' : Event),
    e.Valid P ∧ e'.Valid P ∧ e.id = e'.id ∧ e ≠ e' := by
  let u : Unsigned := ⟨"k", 0, 1, [], ""⟩
  let P : Primitives := ⟨fun _ => "id", fun _ d s => d = "id" && (s = "s1" || s = "s2")⟩
  exact ⟨P, { u with id := "id", sig := "s1" }, { u with id := "id", sig := "s2" },
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, by simp⟩

end Mettapedia.Protocols.Nostr
