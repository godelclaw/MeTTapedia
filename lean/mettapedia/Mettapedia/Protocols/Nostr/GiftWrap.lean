import Mettapedia.Protocols.Nostr.Event
import Mettapedia.Protocols.Options.Weakest

/-!
# NIP-17 private messages: gift wrap, seal and rumor

A NIP-17 message travels in three layers (NIP-59). The *rumor* is the message itself, an unsigned
event, here of kind 14. The *seal* is a kind-13 event signed by the sender, whose content is the
rumor encrypted for the recipient (NIP-44). The *gift wrap* is a kind-1059 event signed by a fresh
key, with a `p` tag naming the recipient, whose content is the seal encrypted for the recipient.
NIP-59 also sets the wrap's time up to two days into the past.

`unwrap` is the reader's acceptance. It opens the wrap, checks that the seal is a valid kind-13
event, opens the seal, and checks that the rumor's key is the seal's. The message's identifier is
the hash of the rumor's fields. Nothing else is checked, since nothing else is needed for the
properties below (rule 7). In particular neither the wrap's kind, its `p` tag nor its signature
matters to the reader, because the wrap's key is nobody's.

Theorems:
- `unwrap_authentic`: a message unwrapped as from an uncompromised key was sealed by that key's
  owner. The owner composed a kind-13 seal whose content opens to exactly this rumor.
- Necessity:
  - without the check that the rumor's key is the seal's, any key can seal a rumor that claims
    another's (`key_check_necessary`);
  - without the seal's kind, a signed event of another kind whose content opens is taken as a
    seal (`seal_kind_necessary`).
- `id_eq_iff`: the identifier names the rumor, so deduplicating by it is exact. Two wraps of one
  rumor share it, while their own event identifiers differ (`wrap_ids_differ`). Receipts and
  replies must therefore name the rumor's identifier.
- `since_misses`: a reader that resumes with a `since` filter looking back less than two days can
  miss a new wrap. `since_complete`: looking back two days, it misses none.
- `relay_cannot_gate`: a relay sees nothing of the sender, so the weakest write rule that admits
  only allowed senders refuses every wrap. Standing is decided by the reader, by the seal's key
  (`Options.Weakest.verified_weakest`).

Encryption and parsing appear only as the reader's functions (`Unwrapping`). Their secrecy, and
what the relay learns from sizes and times, are separate questions.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.GiftWrap

open Mettapedia.Protocols.Nostr

/-- Kind 14: a chat message, the rumor (NIP-17). -/
def kindRumor : Nat := 14
/-- Kind 13: a seal (NIP-59). -/
def kindSeal : Nat := 13
/-- Kind 1059: a gift wrap (NIP-59). -/
def kindWrap : Nat := 1059

/-- The reader's functions: NIP-44 opening of a ciphertext for the reader `me` from the key `k`,
and the parsing of a seal and of a rumor. -/
structure Unwrapping where
  decrypt : PubKey → PubKey → String → Option String
  toSeal : String → Option Event
  toRumor : String → Option Unsigned

/-- A received message: the rumor and its identifier. -/
structure Received where
  rumor : Unsigned
  id : EventId
deriving DecidableEq

/-- The reader's acceptance of a gift wrap. -/
def unwrap (P : Primitives) (U : Unwrapping) (me : PubKey) (w : Event) : Option Received :=
  match U.decrypt me w.pubkey w.content >>= U.toSeal with
  | none => none
  | some s =>
    if s.check P && s.kind == kindSeal then
      match U.decrypt me s.pubkey s.content >>= U.toRumor with
      | some r => if r.pubkey == s.pubkey then some ⟨r, P.hash r⟩ else none
      | none => none
    else none

theorem unwrap_some {P : Primitives} {U : Unwrapping} {me : PubKey} {w : Event} {m : Received}
    (h : unwrap P U me w = some m) :
    ∃ s : Event, s.Valid P ∧ s.kind = kindSeal ∧
      (U.decrypt me s.pubkey s.content >>= U.toRumor) = some m.rumor ∧
      m.rumor.pubkey = s.pubkey ∧ m.id = P.hash m.rumor := by
  unfold unwrap at h
  split at h
  · cases h
  · next s _ =>
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      split at h
      · next r hr =>
        split at h
        · next hk =>
          cases h
          exact ⟨s, (Event.check_iff P s).mp hc.1, hc.2, hr, by simpa using hk, rfl⟩
        · cases h
      · cases h
    · cases h

/-- **Authentication.** A message unwrapped as from an uncompromised key was sealed by that key's
owner: the owner composed a kind-13 seal whose content opens to exactly this rumor. -/
theorem unwrap_authentic {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    {U : Unwrapping} {me : PubKey} {w : Event} {m : Received} (h : unwrap P U me w = some m)
    (hk : ¬ A.compromised m.rumor.pubkey) :
    ∃ s : Event, A.authored s.toUnsigned ∧ s.pubkey = m.rumor.pubkey ∧ s.kind = kindSeal ∧
      (U.decrypt me s.pubkey s.content >>= U.toRumor) = some m.rumor := by
  obtain ⟨s, hv, hkind, hr, hkey, -⟩ := unwrap_some h
  exact ⟨s, authentic A cf hv (hkey ▸ hk), hkey.symm, hkind, hr⟩

/-! ## The identifier -/

/-- The identifier names the rumor: two unwrapped messages share it exactly when they carry one
rumor. -/
theorem id_eq_iff {P : Primitives} (cf : P.CollisionFree) {U : Unwrapping} {me me' : PubKey}
    {w w' : Event} {m m' : Received} (h : unwrap P U me w = some m)
    (h' : unwrap P U me' w' = some m') : m.id = m'.id ↔ m.rumor = m'.rumor := by
  obtain ⟨-, -, -, -, -, hid⟩ := unwrap_some h
  obtain ⟨-, -, -, -, -, hid'⟩ := unwrap_some h'
  rw [hid, hid']
  exact ⟨fun e => cf e, fun e => e ▸ rfl⟩

/-! ## Necessity of the two checks -/

/-- `unwrap` without the check that the rumor's key is the seal's. -/
def unwrapAnyKey (P : Primitives) (U : Unwrapping) (me : PubKey) (w : Event) : Option Received :=
  match U.decrypt me w.pubkey w.content >>= U.toSeal with
  | none => none
  | some s =>
    if s.check P && s.kind == kindSeal then
      (U.decrypt me s.pubkey s.content >>= U.toRumor).map fun r => ⟨r, P.hash r⟩
    else none

/-- `unwrap` without the check of the seal's kind. -/
def unwrapAnyKind (P : Primitives) (U : Unwrapping) (me : PubKey) (w : Event) : Option Received :=
  match U.decrypt me w.pubkey w.content >>= U.toSeal with
  | none => none
  | some s =>
    if s.check P then
      match U.decrypt me s.pubkey s.content >>= U.toRumor with
      | some r => if r.pubkey == s.pubkey then some ⟨r, P.hash r⟩ else none
      | none => none
    else none

section Counterexamples

/-- A rumor claiming the key `a`. -/
private def rumorA : Unsigned := ⟨"a", 0, kindRumor, [], "hello"⟩

/-- The reader opens every ciphertext to itself, and parses `S` as the given seal and `R` as
`rumorA`. -/
private def unwrapping (s : Event) : Unwrapping :=
  ⟨fun _ _ c => some c, fun t => if t = "S" then some s else none,
    fun t => if t = "R" then some rumorA else none⟩

/-- A wrap from a fresh key whose content is the seal `S`. -/
private def wrapS (h : Unsigned → EventId) : Event :=
  { pubkey := "fresh", createdAt := 0, kind := kindWrap, tags := [["p", "me"]], content := "S",
    id := h ⟨"fresh", 0, kindWrap, [["p", "me"]], "S"⟩, sig := "" }

/-- **Necessity of the key check.** The attacker's key `c` seals a rumor that claims the key `a`.
Without the check, the reader takes the message as from `a`, which is uncompromised and composed
nothing. The hash is collision free and the signature assumption holds. `unwrap` refuses. -/
theorem key_check_necessary :
    ∃ (P : Primitives) (A : Authorship P) (U : Unwrapping) (w : Event) (m : Received),
      P.CollisionFree ∧ unwrapAnyKey P U "me" w = some m ∧ ¬ A.compromised m.rumor.pubkey ∧
      (¬ ∃ u : Unsigned, A.authored u ∧ u.pubkey = m.rumor.pubkey) ∧ unwrap P U "me" w = none := by
  obtain ⟨h, hinj⟩ := exists_injective_hash
  let sealU : Unsigned := ⟨"c", 0, kindSeal, [], "R"⟩
  let sealE : Event := { sealU with id := h sealU, sig := "sigC" }
  let P : Primitives := ⟨h, fun k _ s => k == "c" && s == "sigC"⟩
  let A : Authorship P :=
    { authored := fun u => u.pubkey = "c"
      compromised := fun k => k = "c"
      sound := fun k d s hv hc => by
        simp only [P, Bool.and_eq_true, beq_iff_eq] at hv
        exact absurd hv.1 hc }
  refine ⟨P, A, unwrapping sealE, wrapS h, ⟨rumorA, h rumorA⟩, hinj, ?_, ?_, ?_, ?_⟩
  · simp [unwrapAnyKey, unwrapping, wrapS, Event.check, sealE, sealU, P, kindSeal]
  · simp [A, rumorA]
  · rintro ⟨u, hu, hk⟩
    simp only [A] at hu
    simp [rumorA, hu] at hk
  · simp [unwrap, unwrapping, wrapS, Event.check, sealE, sealU, P, kindSeal, rumorA]

/-- **Necessity of the seal's kind.** `a` signed a kind-3838 mail whose content opens to a rumor
that claims `a`. Re-wrapped, it is taken as a seal without the kind check, so the reader holds a
message from `a`, uncompromised, although `a` sealed nothing. `unwrap` refuses. -/
theorem seal_kind_necessary :
    ∃ (P : Primitives) (A : Authorship P) (U : Unwrapping) (w : Event) (m : Received),
      P.CollisionFree ∧ unwrapAnyKind P U "me" w = some m ∧ ¬ A.compromised m.rumor.pubkey ∧
      (¬ ∃ s : Unsigned, A.authored s ∧ s.pubkey = m.rumor.pubkey ∧ s.kind = kindSeal) ∧
      unwrap P U "me" w = none := by
  obtain ⟨h, hinj⟩ := exists_injective_hash
  let mailU : Unsigned := ⟨"a", 0, 3838, [["p", "me"]], "R"⟩
  let mail : Event := { mailU with id := h mailU, sig := "sigA" }
  let P : Primitives := ⟨h, fun k d s => k == "a" && d == h mailU && s == "sigA"⟩
  let A : Authorship P :=
    { authored := fun u => u = mailU
      compromised := fun k => k ≠ "a"
      sound := fun k d s hv hc => by
        simp only [P, Bool.and_eq_true, beq_iff_eq] at hv
        obtain ⟨⟨hk, hd⟩, -⟩ := hv
        exact ⟨mailU, rfl, hk ▸ rfl, hd.symm⟩ }
  refine ⟨P, A, unwrapping mail, wrapS h, ⟨rumorA, h rumorA⟩, hinj, ?_, ?_, ?_, ?_⟩
  · simp [unwrapAnyKind, unwrapping, wrapS, Event.check, mail, mailU, P, rumorA]
  · simp [A, rumorA]
  · rintro ⟨s, hs, -, hk⟩
    simp only [A] at hs
    subst hs
    simp [mailU, kindSeal] at hk
  · simp [unwrap, unwrapping, wrapS, Event.check, mail, mailU, P, kindSeal]

/-- Two wraps of one rumor, made at different times, have different event identifiers under a
collision-free hash, while both unwrap to the rumor's one identifier. A mailbox keyed by event
identifier would show the message twice. -/
theorem wrap_ids_differ :
    ∃ (P : Primitives) (U : Unwrapping) (w w' : Event) (m : Received),
      P.CollisionFree ∧ unwrap P U "me" w = some m ∧ unwrap P U "me" w' = some m ∧ w.id ≠ w'.id := by
  obtain ⟨h, hinj⟩ := exists_injective_hash
  let sealU : Unsigned := ⟨"a", 0, kindSeal, [], "R"⟩
  let sealE : Event := { sealU with id := h sealU, sig := "sigA" }
  let P : Primitives := ⟨h, fun k _ s => k == "a" && s == "sigA"⟩
  let w' : Event := { wrapS h with createdAt := 1, id := h ⟨"fresh", 1, kindWrap, [["p", "me"]], "S"⟩ }
  refine ⟨P, unwrapping sealE, wrapS h, w', ⟨rumorA, h rumorA⟩, hinj, ?_, ?_, ?_⟩
  · simp [unwrap, unwrapping, wrapS, Event.check, sealE, sealU, P, kindSeal, rumorA]
  · simp [unwrap, unwrapping, wrapS, w', Event.check, sealE, sealU, P, kindSeal, rumorA]
  · intro he
    have := hinj he
    simp at this

end Counterexamples

/-! ## Times -/

/-- NIP-59 sets a wrap's time up to two days into the past. -/
def twoDays : ℤ := 2 * 24 * 60 * 60

/-- A wrap made at `made` may show any time from two days earlier up to `made`. -/
def Tweaked (made shown : ℤ) : Prop := made - twoDays ≤ shown ∧ shown ≤ made

/-- A reader that has everything made before `c` and resumes with `since = c - lookback` misses a
wrap made at `c` when it looks back less than two days. -/
theorem since_misses {c lookback : ℤ} (h : lookback < twoDays) :
    ∃ made shown, c ≤ made ∧ Tweaked made shown ∧ shown < c - lookback :=
  ⟨c, c - twoDays, le_rfl, ⟨le_rfl, by unfold twoDays; omega⟩, by omega⟩

/-- Looking back two days, it misses no wrap made at `c` or later. -/
theorem since_complete {c lookback made shown : ℤ} (h : twoDays ≤ lookback) (hm : c ≤ made)
    (ht : Tweaked made shown) : c - lookback ≤ shown := by
  obtain ⟨h1, -⟩ := ht
  omega

/-! ## The relay -/

open Mettapedia.Protocols.Options.Weakest in
/-- A relay sees a wrap and nothing of its sender: any sender can make any wrap. If some sender is
not allowed, the weakest write rule that stores only allowed senders' messages refuses every
wrap. -/
theorem relay_cannot_gate {allowed : PubKey → Prop} (hbad : ∃ k, ¬ allowed k) (w : Event) :
    ¬ weakest (Prod.snd : PubKey × Event → Event) (fun x => allowed x.1) w := by
  obtain ⟨k, hk⟩ := hbad
  exact refuse_iff.2 ⟨(k, w), rfl, hk⟩

/-! ## Non-vacuity -/

/-- Primitives for the example: an event's identifier is its content, and `a` signs with `sigA`. -/
private def primsA : Primitives := ⟨fun u => u.content, fun k _ s => k == "a" && s == "sigA"⟩

/-- `a`'s seal of the rumor `R`. -/
private def sealA : Event :=
  { pubkey := "a", createdAt := 0, kind := kindSeal, tags := [], content := "R", id := "R",
    sig := "sigA" }

/-- A wrap from a fresh key carrying the seal `S`. -/
private def wrapA : Event :=
  { pubkey := "fresh", createdAt := 0, kind := kindWrap, tags := [["p", "me"]], content := "S",
    id := "w", sig := "" }

/-- An honest message unwraps, as from its sealer. -/
example : unwrap primsA (unwrapping sealA) "me" wrapA = some ⟨rumorA, "hello"⟩ := by decide

end Mettapedia.Protocols.Nostr.GiftWrap
