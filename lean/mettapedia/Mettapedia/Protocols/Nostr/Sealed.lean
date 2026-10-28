import Mettapedia.Protocols.Nostr.Mailbox
import Mettapedia.Protocols.Symbolic.Message
import Mettapedia.Protocols.Symbolic.Reading

/-!
# Sealed agent mail over Nostr, symbolically

Agent mail as NuNet's `nostr-mailbox` client builds it, in the symbolic model of
`Protocols.Symbolic`. The client encrypts and then signs: the content of a kind-3838 event is the
NIP-44 sealing of the letter for the recipient `b`, authenticated encryption under the
conversation key `convKey a b = hash (dh (sk a) (pk (sk b)))`; the event commits to its author's
key, its time, its kind, its tags, with a `p` tag naming `b`, and its content; and `a` signs the
event's identifier, the hash of those fields (BIP-340). A receipt is a kind-7 event, signed by the
addressee, whose tags name the mail (`e`), its author (`p`) and the fact (`ack`).

Events here are the string-level `Nostr.Event`s of `Protocols.Nostr.Event`, read symbolically
through a `Reading`: a bijection between strings and symbolic messages in which the literal strings
the client writes (`p`, `e`, `ack`, `delivered`, and the empty content of a receipt) denote public
literals (`Symbolic.Reading`). Readings exist whenever principals are countable
(`Reading.nonempty`). An unsigned event denotes the nested pair of its fields (`Reading.event`), a
signed event on the network the event with its identifier and signature (`Reading.wire`); both
denotations are injective.

The attacker is the network, applies every operation of the message algebra and may corrupt any
principal at any time, learning its secret key. Honest principals mail fresh letters; accept a
delivered event as mail from `a` when it is a kind-3838 event whose key is `a`'s, whose `p` tag
names them, whose identifier hashes its fields, whose signature verifies under `a`'s key and whose
content opens with the conversation key; acknowledge accepted mail with a receipt; and believe a
receipt from `b` naming a mail they sent to `b` when it is a kind-7 event signed by `b`.

Proved for every reachable trace:
* secrecy (`secrecy`): if the attacker knows the letter `letterOf a b i`, then `a` or `b` has
  been corrupted;
* unforgeability (`knows_sign`): a signature under a principal's key that the attacker knows is
  on the identifier of an event the principal signed, or the principal is corrupted;
* authentication (`authentication`): if `b` accepted the letter `ℓ` as mail from `a`, then earlier
  `a` mailed `ℓ` to `b`, or `a` had been corrupted;
* receipts (`receipt_authentic`): if `a` believes that `b` received mail `m`, then earlier `b`
  accepted `m` as mail from `a`, or `b` had been corrupted;
* the attacker holds `p`'s secret key exactly when `p` has been corrupted (`knows_sk_iff`).
Non-vacuity: an honest run is reachable and ends with the receipt believed (`honest_run`);
corrupting the sender after a mail reveals the letter (`corrupt_reveals`); corrupting the sender
lets the attacker make `b` accept mail `a` never sent (`corrupt_forges_mail`); corrupting the
addressee lets the attacker make `a` believe a receipt for mail `b` never accepted
(`corrupt_forges_receipt`).

The proof is an instance of `Symbolic.InvariantProof` (`proof`): names are labelled by whom they
are readable by, a principal signs only the events it composes (`preds`), and the entry invariant
records, for each signature, acceptance and belief, the honest act it rests on (`inv`).

Not modelled: the relay and its NIP-42 sign-in, deletions, gift wraps, the structure of letters
(subject, body, team types), replay (acceptance is not injective; the archive deduplicates by
identifier), timing, and anything computational. There is no forward secrecy, as
`corrupt_reveals` shows.

`Protocols.Nostr.SymbolicAuthorship` derives from this semantics the signature assumption
(`Authorship`) on which the string-level relay, client and bridge theorems rest.

The symbolic method is the one distilled from LeanDY (Jeanteur, Veronese, Solitro, Maffei,
arXiv:2607.03406) and DyLean (Wallez, Cremers, IACR ePrint 2026/1493); see `Protocols.Symbolic`.
-/

namespace Mettapedia.Protocols.Nostr.Sealed

open Mettapedia.Protocols.Symbolic (Msg Label ThreatModel Reachable DYStep standardThreat
  standardThreat_knows_sent standardThreat_knows_secret Publishability InvariantProof CryptoPreds
  DYRule Holds)

/-- Names: long-term secret keys, letters, the attacker's own names, and public literals,
numbers, times and the end of a list. -/
inductive Name (P : Type) where
  | sk (p : P)
  | letter (a b : P) (i : ℕ)
  | adv (i : ℕ)
  | lit (s : String)
  | num (n : ℕ)
  | time (t : ℤ)
  | nil
deriving DecidableEq

/-- Messages of the model. -/
abbrev M (P : Type) := Msg (Name P)

/-- The literal strings an honest client writes into the events it signs. -/
def literals : List String := ["p", "e", "ack", "delivered", ""]

/-- A reading of strings as symbolic messages in which the client's literal strings denote
public literals. -/
structure Reading (P : Type) where
  /-- The message each string denotes. -/
  denote : String ≃ M P
  literal : ∀ s ∈ literals, denote s = .name (.lit s)

namespace Reading

variable {P : Type} (R : Reading P)

/-- The message a string denotes. -/
def read (s : String) : M P := R.denote s

/-- The string that writes a message. -/
def write (m : M P) : String := R.denote.symm m

@[simp] theorem read_write (m : M P) : R.read (R.write m) = m := R.denote.apply_symm_apply m

@[simp] theorem write_read (s : String) : R.write (R.read s) = s := R.denote.symm_apply_apply s

theorem read_injective : Function.Injective R.read := R.denote.injective

theorem write_injective : Function.Injective R.write := R.denote.symm.injective

@[simp] theorem read_p : R.read "p" = .name (.lit "p") := R.literal _ (by simp [literals])
@[simp] theorem read_e : R.read "e" = .name (.lit "e") := R.literal _ (by simp [literals])
@[simp] theorem read_ack : R.read "ack" = .name (.lit "ack") := R.literal _ (by simp [literals])
@[simp] theorem read_delivered : R.read "delivered" = .name (.lit "delivered") :=
  R.literal _ (by simp [literals])
@[simp] theorem read_empty : R.read "" = .name (.lit "") := R.literal _ (by simp [literals])

/-- A list of strings, as nested pairs ending in `nil`. -/
def strings : List String → M P
  | [] => .name .nil
  | s :: ss => .pair (R.read s) (strings ss)

/-- A list of tags, as nested pairs ending in `nil`. -/
def tags : List (List String) → M P
  | [] => .name .nil
  | t :: ts => .pair (R.strings t) (tags ts)

/-- The message an unsigned event denotes: its key, time, kind, tags and content. -/
def event (u : Unsigned) : M P :=
  .pair (R.read u.pubkey) (.pair (.name (.time u.createdAt)) (.pair (.name (.num u.kind))
    (.pair (R.tags u.tags) (R.read u.content))))

/-- The message a signed event denotes on the network: the event, its identifier and its
signature. -/
def wire (e : Nostr.Event) : M P :=
  .pair (R.event e.toUnsigned) (.pair (R.read e.id) (R.read e.sig))

theorem strings_injective : Function.Injective R.strings := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all [strings]
  | cons s l ih =>
      intro l' h
      cases l' with
      | nil => simp [strings] at h
      | cons s' l' =>
          simp only [strings, Msg.pair.injEq] at h
          rw [R.read_injective h.1, ih h.2]

theorem tags_injective : Function.Injective R.tags := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all [tags]
  | cons t l ih =>
      intro l' h
      cases l' with
      | nil => simp [tags] at h
      | cons t' l' =>
          simp only [tags, Msg.pair.injEq] at h
          rw [R.strings_injective h.1, ih h.2]

theorem event_injective : Function.Injective R.event := by
  rintro ⟨k, t, n, g, c⟩ ⟨k', t', n', g', c'⟩ h
  simp only [event, Msg.pair.injEq, Msg.name.injEq, Name.time.injEq, Name.num.injEq] at h
  obtain ⟨hk, ht, hn, hg, hc⟩ := h
  rw [R.read_injective hk, ht, hn, R.tags_injective hg, R.read_injective hc]

theorem wire_injective : Function.Injective R.wire := by
  rintro ⟨u, i, s⟩ ⟨u', i', s'⟩ h
  simp only [wire, Msg.pair.injEq] at h
  obtain ⟨hu, hi, hs⟩ := h
  rw [R.event_injective hu, R.read_injective hi, R.read_injective hs]

end Reading

/-! ## Keys, letters and events -/

section

variable {P : Type}

/-- The secret key of `p`. -/
def skOf (p : P) : M P := .name (.sk p)

/-- The public key of `p`. -/
def pkOf (p : P) : M P := .pk (skOf p)

/-- The `i`-th letter from `a` to `b`. -/
def letterOf (a b : P) (i : ℕ) : M P := .name (.letter a b i)

/-- The NIP-44 conversation key of `a` with `b`: a hash of their Diffie–Hellman secret. -/
def convKey (a b : P) : M P := .hash (Msg.dh (skOf a) (pkOf b))

theorem convKey_eq (a b : P) : convKey a b = .hash (.shared s(.sk a, .sk b)) := rfl

/-- Both parties derive the same conversation key. -/
theorem convKey_comm (a b : P) : convKey a b = convKey b a := by
  simp only [convKey_eq, Sym2.eq_swap]

/-- NIP-44 sealing of `ℓ` from `a` for `b`: authenticated encryption under their conversation
key. -/
def nip44 (a b : P) (ℓ : M P) : M P := .senc (convKey a b) ℓ

/-- What a principal records: that it signed an event, mailed a letter, accepted a letter as
mail from `a` in the event with identifier `m`, or believes that `b` received mail `m`. -/
inductive Signal (P : Type) where
  | signed (u : Unsigned)
  | mailed (b : P) (ℓ : M P)
  | accepted (a : P) (ℓ : M P) (m : EventId)
  | believes (b : P) (m : EventId)

/-- Trace events of the model. -/
abbrev Ev (P : Type) := Symbolic.Event P (M P) (Signal P)

end

variable {P : Type} (R : Reading P)

/-- The kind-3838 event in which `a` mails `ℓ` to `b` at time `t`, as the client composes it. -/
def mailEvent (a b : P) (t : ℤ) (ℓ : M P) : Unsigned where
  pubkey := R.write (pkOf a)
  createdAt := t
  kind := kindMail
  tags := [["p", R.write (pkOf b)]]
  content := R.write (nip44 a b ℓ)

/-- The kind-7 receipt in which `b` tells `a` that the mail with identifier `m` was delivered. -/
def receiptEvent (b a : P) (t : ℤ) (m : EventId) : Unsigned where
  pubkey := R.write (pkOf b)
  createdAt := t
  kind := kindReaction
  tags := [["e", m], ["p", R.write (pkOf a)], ["ack", "delivered"]]
  content := ""

/-- The identifier of an event: the hash of its denotation, written as a string. -/
def idOf (u : Unsigned) : EventId := R.write (.hash (R.event u))

/-- The event `u` with the identifier and the signature `p` attaches to it. -/
def signEvent (p : P) (u : Unsigned) : Nostr.Event :=
  { u with id := idOf R u, sig := R.write (.sign (skOf p) (.hash (R.event u))) }

theorem event_mailEvent (a b : P) (t : ℤ) (ℓ : M P) :
    R.event (mailEvent R a b t ℓ) =
      .pair (pkOf a) (.pair (.name (.time t)) (.pair (.name (.num kindMail))
        (.pair (.pair (.pair (.name (.lit "p")) (.pair (pkOf b) (.name .nil))) (.name .nil))
          (nip44 a b ℓ)))) := by
  simp [Reading.event, mailEvent, Reading.tags, Reading.strings]

theorem event_receiptEvent (b a : P) (t : ℤ) (m : EventId) :
    R.event (receiptEvent R b a t m) =
      .pair (pkOf b) (.pair (.name (.time t)) (.pair (.name (.num kindReaction))
        (.pair (.pair (.pair (.name (.lit "e")) (.pair (R.read m) (.name .nil)))
          (.pair (.pair (.name (.lit "p")) (.pair (pkOf a) (.name .nil)))
            (.pair (.pair (.name (.lit "ack")) (.pair (.name (.lit "delivered")) (.name .nil)))
              (.name .nil))))
          (.name (.lit ""))))) := by
  simp [Reading.event, receiptEvent, Reading.tags, Reading.strings]

/-! ## Threat model and protocol -/

/-- Public data: every public key, the attacker's own names, literals, numbers, times and the end
of a list. -/
def initialKnowledge : Set (M P) :=
  {m | (∃ p, m = pkOf p) ∨ (∃ i, m = .name (.adv i)) ∨ (∃ s, m = .name (.lit s)) ∨
    (∃ n, m = .name (.num n)) ∨ (∃ t, m = .name (.time t)) ∨ m = .name .nil}

variable [DecidableEq P]

/-- The standard threat model: the attacker is the network, applies every operation of the
algebra, and corrupting `p` reveals `p`'s secret key. -/
def threat : ThreatModel (Ev P) (M P) :=
  standardThreat DYRule initialKnowledge (fun p => {skOf p})

/-- The honest steps of the mail protocol. -/
inductive Step : List (Ev P) → List (Ev P) → Prop
  /-- `a` mails its `i`-th letter for `b` at time `t`: it records the mail, signs the event and
  publishes it. -/
  | mail (τ : List (Ev P)) (a b : P) (t : ℤ) (i : ℕ) :
      Step τ [.signal a (.mailed b (letterOf a b i)),
        .signal a (.signed (mailEvent R a b t (letterOf a b i))),
        .send (R.wire (signEvent R a (mailEvent R a b t (letterOf a b i))))]
  /-- `b` takes the signed event `e` from the network and accepts `ℓ` as mail from `a`: `e` is a
  kind-3838 event with `a`'s key, its `p` tag names `b`, its identifier hashes its fields, its
  signature verifies under `a`'s key, and its content opens to `ℓ`. -/
  | accept (τ : List (Ev P)) (b a : P) (e : Nostr.Event) (ℓ : M P) :
      threat.Knows τ (R.wire e) → e.kind = kindMail → R.read e.pubkey = pkOf a →
      R.write (pkOf b) ∈ tagValues e.tags "p" → R.read e.id = .hash (R.event e.toUnsigned) →
      Msg.verify (pkOf a) (R.read e.sig) = R.read e.id →
      Msg.sdec (convKey b a) (R.read e.content) = ℓ → ℓ ≠ .fail →
      Step τ [.recv b (R.wire e), .signal b (.accepted a ℓ e.id)]
  /-- `b` acknowledges to `a` the delivery of mail `m` that it accepted from `a`. -/
  | receipt (τ : List (Ev P)) (b a : P) (t : ℤ) (m : EventId) (ℓ : M P) :
      Symbolic.Event.signal b (.accepted a ℓ m) ∈ τ →
      Step τ [.signal b (.signed (receiptEvent R b a t m)),
        .send (R.wire (signEvent R b (receiptEvent R b a t m)))]
  /-- `a` takes the signed event `r` from the network and believes that `b` received mail `m`:
  `r` is a kind-7 event with `b`'s key, its identifier hashes its fields, its signature verifies
  under `b`'s key, it names `m` and a fact, and `m` identifies a mail `a` signed for `b`. -/
  | believe (τ : List (Ev P)) (a b : P) (r : Nostr.Event) (m : EventId) (st : String)
      (u : Unsigned) :
      threat.Knows τ (R.wire r) → r.kind = kindReaction → R.read r.pubkey = pkOf b →
      R.read r.id = .hash (R.event r.toUnsigned) →
      Msg.verify (pkOf b) (R.read r.sig) = R.read r.id → receiptFor r = some (m, st) →
      Symbolic.Event.signal a (.signed u) ∈ τ → u.kind = kindMail →
      R.write (pkOf b) ∈ tagValues u.tags "p" → m = idOf R u →
      Step τ [.recv a (R.wire r), .signal a (.believes b m)]

/-! ## The invariant -/

/-- Intended secrecy of names: `sk p` is readable by `p`, a letter from `a` to `b` by `a` and
`b`; everything else is public. -/
noncomputable def nameLabel : Name P → Label (Ev P)
  | .sk p => Label.after (.corrupt p)
  | .letter a b _ => Label.after (.corrupt a) ⊔ Label.after (.corrupt b)
  | .adv _ => ⊤
  | .lit _ => ⊤
  | .num _ => ⊤
  | .time _ => ⊤
  | .nil => ⊤

/-- A principal signs only the identifiers of events it composed, under its own key; encryption
is unrestricted. -/
def preds : CryptoPreds (Ev P) (M P) where
  sign τ k x := ∃ p u, k = skOf p ∧ x = .hash (R.event u) ∧ R.read u.pubkey = pkOf p ∧
    Symbolic.Event.signal p (.signed u) ∈ τ
  enc _ _ _ := True
  sign_mono h := fun ⟨p, u, hk, hx, hpk, hin⟩ => ⟨p, u, hk, hx, hpk, List.IsPrefix.mem hin h⟩
  enc_mono _ _ := trivial

/-- Publishability for the model. -/
noncomputable def pub : Publishability (Ev P) (M P) DYRule := Msg.publishability nameLabel (preds R)

/-- The entry invariant: what is sent or received is publishable; a principal signs its own
mail, or a receipt for mail it accepted; an acceptance from `a` is of a publishable identifier
that hashes an event with `a`'s key, and follows `a`'s mail or `a`'s corruption; a belief that
`b` received `m` follows `b`'s acceptance of `m` as mail from the believer, or `b`'s corruption;
nobody generates or stores anything. -/
noncomputable def inv : List (Ev P) → Ev P → Prop
  | τ, .send m => (pub R).Pub τ m
  | τ, .recv _ m => (pub R).Pub τ m
  | τ, .signal p (.signed u) =>
      (∃ b t i, u = mailEvent R p b t (letterOf p b i) ∧
        Symbolic.Event.signal p (.mailed b (letterOf p b i)) ∈ τ) ∨
      (∃ a t m ℓ, u = receiptEvent R p a t m ∧ Symbolic.Event.signal p (.accepted a ℓ m) ∈ τ)
  | τ, .signal b (.accepted a ℓ m) =>
      (pub R).Pub τ (R.read m) ∧ (∃ u, R.read m = .hash (R.event u) ∧ R.read u.pubkey = pkOf a) ∧
      (Symbolic.Event.signal a (.mailed b ℓ) ∈ τ ∨ Symbolic.Event.corrupt a ∈ τ)
  | τ, .signal a (.believes b m) =>
      (∃ ℓ, Symbolic.Event.signal b (.accepted a ℓ m) ∈ τ) ∨ Symbolic.Event.corrupt b ∈ τ
  | _, .signal _ (.mailed _ _) => True
  | _, .corrupt _ => True
  | _, .gen _ _ => False
  | _, .state _ _ => False

/-! ## Honest events are publishable -/

omit [DecidableEq P] in
theorem wire_signEvent (p : P) (u : Unsigned) :
    R.wire (signEvent R p u) =
      .pair (R.event u) (.pair (.hash (R.event u)) (.sign (skOf p) (.hash (R.event u)))) := by
  simp [Reading.wire, signEvent, idOf]

/-- A signed event is publishable when its denotation is, and its signer signed it. -/
theorem signed_pub {τ : List (Ev P)} {p : P} {u : Unsigned}
    (hu : (pub R).Pub τ (R.event u)) (hpk : R.read u.pubkey = pkOf p)
    (hs : Symbolic.Event.signal p (.signed u) ∈ τ) :
    (pub R).Pub τ (R.wire (signEvent R p u)) := by
  rw [wire_signEvent]
  exact ⟨⟨hu.1, hu.1, hu.1⟩, hu.2, hu.2, trivial, hu.2, Or.inr ⟨p, u, rfl, rfl, hpk, hs⟩⟩

/-- A mail event denotes a publishable message: its letter is sealed under a key exactly as
readable as the letter. -/
theorem mailEvent_pub (τ : List (Ev P)) (a b : P) (t : ℤ) (i : ℕ) :
    (pub R).Pub τ (R.event (mailEvent R a b t (letterOf a b i))) := by
  rw [event_mailEvent]
  refine ⟨by simp [pub, Msg.publishability, nameLabel, pkOf, skOf, nip44]; trivial, ?_⟩
  simp only [pub, Msg.publishability, Msg.WellFormed, nip44, convKey_eq, pkOf, skOf, letterOf,
    and_true, true_and]
  exact ⟨Label.flowsAt_of_le le_rfl, Or.inr trivial⟩

/-- A receipt event denotes a publishable message when the identifier it names does. -/
theorem receiptEvent_pub {τ : List (Ev P)} (b a : P) (t : ℤ) {m : EventId}
    (hm : (pub R).Pub τ (R.read m)) :
    (pub R).Pub τ (R.event (receiptEvent R b a t m)) := by
  rw [event_receiptEvent]
  refine ⟨?_, ?_⟩
  · have := hm.1
    simp only [pub, Msg.publishability] at this
    simp [pub, Msg.publishability, nameLabel, pkOf, skOf, this]; trivial
  · have := hm.2
    simp only [pub, Msg.publishability] at this
    simp [pub, Msg.publishability, pkOf, skOf, this]

/-! ## Signatures -/

omit [DecidableEq P] in
/-- A well-formed signature under `p`'s key is on the identifier of an event `p` signed, or `p`
is corrupted. -/
theorem signed_of_sign {τ : List (Ev P)} {p : P} {x : M P}
    (h : Msg.WellFormed nameLabel (preds R) τ (.sign (skOf p) x)) :
    Symbolic.Event.corrupt p ∈ τ ∨
      ∃ u, x = .hash (R.event u) ∧ R.read u.pubkey = pkOf p ∧
        Symbolic.Event.signal p (.signed u) ∈ τ := by
  rcases h.sign_allowed with hc | ⟨p', u, hk, hx, hpk, hin⟩
  · exact Or.inl hc
  · simp only [skOf, Msg.name.injEq, Name.sk.injEq] at hk
    subst hk
    exact Or.inr ⟨u, hx, hpk, hin⟩

/-- A publishable signed event whose identifier hashes its fields and whose signature verifies
under `a`'s key was signed by `a`, or `a` is corrupted. -/
theorem signed_of_wire {τ : List (Ev P)} {e : Nostr.Event} {a : P}
    (hw : (pub R).Pub τ (R.wire e)) (hid : R.read e.id = .hash (R.event e.toUnsigned))
    (hv : Msg.verify (pkOf a) (R.read e.sig) = R.read e.id) :
    Symbolic.Event.corrupt a ∈ τ ∨ Symbolic.Event.signal a (.signed e.toUnsigned) ∈ τ := by
  obtain ⟨k, hsig, hk⟩ := Msg.eq_sign_of_verify hv (by rw [hid]; simp)
  have hk' : k = skOf a := by
    simp only [pkOf, Msg.pk.injEq] at hk
    exact hk.symm
  subst hk'
  have hwf : Msg.WellFormed nameLabel (preds R) τ (R.read e.sig) := hw.2.2.2
  rw [hsig] at hwf
  rcases signed_of_sign R hwf with hc | ⟨u, hx, -, hin⟩
  · exact Or.inl hc
  · rw [hid] at hx
    have hu : e.toUnsigned = u := R.event_injective (Msg.hash.inj hx)
    rw [hu]
    exact Or.inr hin

/-! ## Reading the invariant -/

/-- What a signature recorded on a trace satisfying the invariant rests on. -/
theorem signed_rests {τ : List (Ev P)} (hτ : Holds (inv R) τ) {p : P} {u : Unsigned}
    (h : Symbolic.Event.signal p (.signed u) ∈ τ) :
    (∃ b t i, u = mailEvent R p b t (letterOf p b i) ∧
        Symbolic.Event.signal p (.mailed b (letterOf p b i)) ∈ τ) ∨
      (∃ a t m ℓ, u = receiptEvent R p a t m ∧
        Symbolic.Event.signal p (.accepted a ℓ m) ∈ τ) := by
  obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp h
  rcases (hτ.entry rfl : inv R pre _) with ⟨b, t, i, hu, hm⟩ | ⟨a, t, m, ℓ, hu, hm⟩
  · exact Or.inl ⟨b, t, i, hu, List.mem_append_left _ hm⟩
  · exact Or.inr ⟨a, t, m, ℓ, hu, List.mem_append_left _ hm⟩

/-- What an acceptance recorded on a trace satisfying the invariant rests on. -/
theorem accepted_rests {τ : List (Ev P)} (hτ : Holds (inv R) τ) {b a : P} {ℓ : M P}
    {m : EventId} (h : Symbolic.Event.signal b (.accepted a ℓ m) ∈ τ) :
    (pub R).Pub τ (R.read m) ∧ ∃ u, R.read m = .hash (R.event u) ∧ R.read u.pubkey = pkOf a := by
  obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp h
  obtain ⟨hp, hu, -⟩ := (hτ.entry rfl : inv R pre _)
  exact ⟨hp.mono (List.prefix_append _ _), hu⟩

/-- The identifier of a publishable signed event is publishable. -/
theorem pub_id {τ : List (Ev P)} {e : Nostr.Event} (hw : (pub R).Pub τ (R.wire e)) :
    (pub R).Pub τ (R.read e.id) := by
  have h₁ : (pub R).Pub τ (Msg.snd (R.wire e)) :=
    (pub R).closed τ (DYRule.snd _) (fun x hx => by simp at hx; subst hx; exact hw)
  have h₂ : (pub R).Pub τ (Msg.fst (Msg.snd (R.wire e))) :=
    (pub R).closed τ (DYRule.fst _) (fun x hx => by simp at hx; subst hx; exact h₁)
  simpa [Reading.wire] using h₂

theorem kindMail_ne_kindReaction : kindMail ≠ kindReaction := by decide

/-- The acceptance step keeps the invariant: what `b` accepts as mail from `a` was mailed by
`a` to `b`, or `a` is corrupted. -/
theorem accept_rests {τ : List (Ev P)} (hτ : Holds (inv R) τ) {b a : P} {e : Nostr.Event}
    {ℓ : M P} (hw : (pub R).Pub τ (R.wire e)) (hkind : e.kind = kindMail)
    (hp : R.write (pkOf b) ∈ tagValues e.tags "p")
    (hid : R.read e.id = .hash (R.event e.toUnsigned))
    (hv : Msg.verify (pkOf a) (R.read e.sig) = R.read e.id)
    (hℓ : Msg.sdec (convKey b a) (R.read e.content) = ℓ) :
    Symbolic.Event.signal a (.mailed b ℓ) ∈ τ ∨ Symbolic.Event.corrupt a ∈ τ := by
  rcases signed_of_wire R hw hid hv with hc | hs
  · exact Or.inr hc
  · rcases signed_rests R hτ hs with ⟨b', t, i, hu, hm⟩ | ⟨a', t, m, ℓ', hu, -⟩
    · have htags : e.tags = [["p", R.write (pkOf b')]] := by
        rw [show e.tags = e.toUnsigned.tags from rfl, hu]; rfl
      have hcontent : e.content = R.write (nip44 a b' (letterOf a b' i)) := by
        rw [show e.content = e.toUnsigned.content from rfl, hu]; rfl
      rw [htags] at hp
      simp only [tagValues, List.filterMap_cons, if_true, List.filterMap_nil,
        List.mem_singleton] at hp
      have hb : b = b' := by
        have := R.write_injective hp
        simpa [pkOf, skOf] using this
      subst hb
      rw [hcontent, Reading.read_write, nip44, convKey_comm b a, Msg.sdec_senc] at hℓ
      subst hℓ
      exact Or.inl hm
    · have : e.kind = kindReaction := by
        rw [show e.kind = e.toUnsigned.kind from rfl, hu]; rfl
      exact absurd (hkind.symm.trans this) kindMail_ne_kindReaction

omit [DecidableEq P] in
theorem receiptFor_receipt {r : Nostr.Event} {b a : P} {t : ℤ} {m' : EventId}
    (hu : r.toUnsigned = receiptEvent R b a t m') :
    receiptFor r = some (m', "delivered") := by
  have htags : r.tags = [["e", m'], ["p", R.write (pkOf a)], ["ack", "delivered"]] := by
    rw [show r.tags = r.toUnsigned.tags from rfl, hu]; rfl
  simp [receiptFor, htags, tagValues]

/-- The belief step keeps the invariant: a receipt believed from `b` for mail `m` that the
believer signed for `b` rests on `b`'s acceptance of `m` as mail from the believer, or on `b`'s
corruption. -/
theorem believe_rests {τ : List (Ev P)} (hτ : Holds (inv R) τ) {a b : P} {r : Nostr.Event}
    {m : EventId} {st : String} {u : Unsigned} (hw : (pub R).Pub τ (R.wire r))
    (hkind : r.kind = kindReaction) (hid : R.read r.id = .hash (R.event r.toUnsigned))
    (hv : Msg.verify (pkOf b) (R.read r.sig) = R.read r.id)
    (hrf : receiptFor r = some (m, st)) (hsu : Symbolic.Event.signal a (.signed u) ∈ τ)
    (hukind : u.kind = kindMail) (hm : m = idOf R u) :
    (∃ ℓ, Symbolic.Event.signal b (.accepted a ℓ m) ∈ τ) ∨ Symbolic.Event.corrupt b ∈ τ := by
  rcases signed_of_wire R hw hid hv with hc | hs
  · exact Or.inr hc
  · rcases signed_rests R hτ hs with ⟨b', t, i, hu, -⟩ | ⟨a', t, m', ℓ, hu, hacc⟩
    · have : r.kind = kindMail := by
        rw [show r.kind = r.toUnsigned.kind from rfl, hu]; rfl
      exact absurd (this.symm.trans hkind) kindMail_ne_kindReaction
    · rw [receiptFor_receipt R hu, Option.some.injEq, Prod.mk.injEq] at hrf
      obtain ⟨rfl, -⟩ := hrf
      -- `m'` identifies `a'`'s mail; it also identifies `u`, signed by `a`
      obtain ⟨-, u', hu', hpk'⟩ := accepted_rests R hτ hacc
      have hpk : R.read u.pubkey = pkOf a := by
        rcases signed_rests R hτ hsu with ⟨b'', t', i', rfl, -⟩ | ⟨a'', t', m'', ℓ'', rfl, -⟩
        · simp [mailEvent]
        · exact absurd hukind.symm kindMail_ne_kindReaction
      have hm' : R.read m' = .hash (R.event u) := by rw [hm, idOf, Reading.read_write]
      have huu : u' = u := R.event_injective (Msg.hash.inj (hu'.symm.trans hm'))
      subst huu
      have ha : a' = a := by
        have := hpk'.symm.trans hpk
        simpa [pkOf, skOf] using this
      subst ha
      exact Or.inl ⟨ℓ, hacc⟩

/-! ## The invariant holds -/

/-- The trace-invariant proof of sealed agent mail. -/
noncomputable def proof : InvariantProof (threat (P := P)) (Step R) where
  pub := pub R
  inv := inv R
  initial_pub := by
    rintro m (⟨p, rfl⟩ | ⟨i, rfl⟩ | ⟨s, rfl⟩ | ⟨n, rfl⟩ | ⟨t, rfl⟩ | rfl) <;>
      exact ⟨trivial, trivial⟩
  reveals_pub := by
    intro τ e hτ he m hm
    cases e with
    | send m' =>
        have hm' : m = m' := hm
        subst hm'
        exact Publishability.Pub.mono (List.prefix_append _ _) he
    | corrupt p =>
        rcases hm with hm | hm
        · have hm' : m = skOf p := hm
          subst hm'
          exact ⟨List.mem_append_right _ (List.mem_singleton_self _), trivial⟩
        · obtain ⟨pre, post, rfl⟩ :=
            List.mem_iff_append.mp (show Symbolic.Event.state p m ∈ τ from hm)
          exact absurd (hτ.entry rfl) id
    | gen => exact absurd hm id
    | recv => exact absurd hm id
    | state => exact absurd hm id
    | signal => exact absurd hm id
  inject_inv := fun _ _ _ hm => hm
  act_inv := by
    rintro τ e - ⟨p, rfl⟩
    trivial
  honest_inv := by
    intro τ new hτ hknows hstep
    cases hstep with
    | mail a b t i =>
        refine ⟨trivial, Or.inl ⟨b, t, i, rfl, List.mem_append_right _ (List.mem_singleton_self _)⟩,
          ?_, trivial⟩
        exact signed_pub R (mailEvent_pub R _ a b t i) (by simp [mailEvent])
          (List.mem_append_right _ (List.mem_singleton_self _))
    | accept b a e ℓ hk hkind hpk hp hid hv hℓ _ =>
        refine ⟨hknows _ hk, ⟨(pub_id R (hknows _ hk)).mono (List.prefix_append _ _),
          ⟨e.toUnsigned, hid, hpk⟩, ?_⟩, trivial⟩
        rcases accept_rests R hτ (hknows _ hk) hkind hp hid hv hℓ with h | h
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr (List.mem_append_left _ h)
    | receipt b a t m ℓ hacc =>
        refine ⟨Or.inr ⟨a, t, m, ℓ, rfl, hacc⟩, ?_, trivial⟩
        exact signed_pub R
          (receiptEvent_pub R b a t ((accepted_rests R hτ hacc).1.mono (List.prefix_append _ _)))
          (by simp [receiptEvent]) (List.mem_append_right _ (List.mem_singleton_self _))
    | believe a b r m st u hk hkind hpk hid hv hrf hsu hukind _ hm =>
        refine ⟨hknows _ hk, ?_, trivial⟩
        rcases believe_rests R hτ (hknows _ hk) hkind hid hv hrf hsu hukind hm with
          ⟨ℓ, h⟩ | h
        · exact Or.inl ⟨ℓ, List.mem_append_left _ h⟩
        · exact Or.inr (List.mem_append_left _ h)

/-! ## Security theorems -/

variable {R}

/-- Secrecy: if the attacker knows the letter from `a` to `b`, then `a` or `b` has been
corrupted. -/
theorem secrecy {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ) {a b : P} {i : ℕ}
    (hk : threat.Knows τ (letterOf a b i)) :
    Symbolic.Event.corrupt a ∈ τ ∨ Symbolic.Event.corrupt b ∈ τ :=
  (proof R).label_corrupt h hk

/-- The attacker holds `p`'s secret key exactly when `p` has been corrupted. -/
theorem knows_sk_iff {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ) (p : P) :
    threat.Knows τ (skOf p) ↔ Symbolic.Event.corrupt p ∈ τ := by
  constructor
  · exact (proof R).label_corrupt h
  · intro hc
    obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hc
    exact standardThreat_knows_secret rfl rfl

/-- Unforgeability: a signature under `p`'s key that the attacker knows is on the identifier of
an event `p` signed, or `p` has been corrupted. -/
theorem knows_sign {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ) {p : P}
    {x : M P} (hk : threat.Knows τ (.sign (skOf p) x)) :
    Symbolic.Event.corrupt p ∈ τ ∨
      ∃ u, x = .hash (R.event u) ∧ R.read u.pubkey = pkOf p ∧
        Symbolic.Event.signal p (.signed u) ∈ τ :=
  signed_of_sign R ((proof R).knows_wf h hk)

/-- Authentication: if `b` accepted `ℓ` as mail from `a`, then earlier `a` mailed `ℓ` to `b`, or
`a` had been corrupted. -/
theorem authentication {τ pre post : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ)
    {a b : P} {ℓ : M P} {m : EventId}
    (he : τ = pre ++ .signal b (.accepted a ℓ m) :: post) :
    Symbolic.Event.signal a (.mailed b ℓ) ∈ pre ∨ Symbolic.Event.corrupt a ∈ pre :=
  ((proof R).entry h he).2.2

/-- Receipts: if `a` believes that `b` received mail `m`, then earlier `b` accepted `m` as mail
from `a`, or `b` had been corrupted. -/
theorem receipt_authentic {τ pre post : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ)
    {a b : P} {m : EventId} (he : τ = pre ++ .signal a (.believes b m) :: post) :
    (∃ ℓ, Symbolic.Event.signal b (.accepted a ℓ m) ∈ pre) ∨ Symbolic.Event.corrupt b ∈ pre :=
  (proof R).entry h he

/-! ## Readings exist -/

/-- Names embed in a countable sum. -/
def Name.toSum {Q : Type} : Name Q → Q ⊕ (Q × Q × ℕ) ⊕ ℕ ⊕ String ⊕ ℕ ⊕ ℤ ⊕ Unit
  | .sk p => .inl p
  | .letter a b i => .inr (.inl (a, b, i))
  | .adv i => .inr (.inr (.inl i))
  | .lit s => .inr (.inr (.inr (.inl s)))
  | .num n => .inr (.inr (.inr (.inr (.inl n))))
  | .time t => .inr (.inr (.inr (.inr (.inr (.inl t)))))
  | .nil => .inr (.inr (.inr (.inr (.inr (.inr ())))))

theorem Name.toSum_injective {Q : Type} : Function.Injective (Name.toSum (Q := Q)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [Name.toSum]

/-- Readings exist whenever principals are countable. -/
theorem Reading.nonempty [Countable P] : Nonempty (Reading P) := by
  have := Symbolic.countable_string
  have : Countable (Name P) := Name.toSum_injective.countable
  obtain ⟨R, hR⟩ := Symbolic.exists_reading literals (by decide)
    (fun s => (Msg.name (Name.lit s) : M P)) (by intro a _ b _ h; simpa using h)
  exact ⟨⟨R, hR⟩⟩

/-! ## Non-vacuity -/

variable (R)

/-- `a`'s signed mail of its `i`-th letter for `b` at time `t`. -/
def mailMsg (a b : P) (t : ℤ) (i : ℕ) : Nostr.Event :=
  signEvent R a (mailEvent R a b t (letterOf a b i))

/-- `a` mails its `i`-th letter for `b` at time `t`. -/
def mailBlock (a b : P) (t : ℤ) (i : ℕ) : List (Ev P) :=
  [.signal a (.mailed b (letterOf a b i)), .signal a (.signed (mailEvent R a b t (letterOf a b i))),
    .send (R.wire (mailMsg R a b t i))]

/-- `b`'s signed receipt to `a`, at time `t`, for the mail with identifier `m`. -/
def receiptMsg (b a : P) (t : ℤ) (m : EventId) : Nostr.Event :=
  signEvent R b (receiptEvent R b a t m)

/-- An honest run: `a` mails, `b` accepts and acknowledges, `a` believes the receipt. -/
def honestRun (a b : P) (t t' : ℤ) (i : ℕ) : List (Ev P) :=
  mailBlock R a b t i ++
    [.recv b (R.wire (mailMsg R a b t i)),
      .signal b (.accepted a (letterOf a b i) (mailMsg R a b t i).id)] ++
    [.signal b (.signed (receiptEvent R b a t' (mailMsg R a b t i).id)),
      .send (R.wire (receiptMsg R b a t' (mailMsg R a b t i).id))] ++
    [.recv a (R.wire (receiptMsg R b a t' (mailMsg R a b t i).id)),
      .signal a (.believes b (mailMsg R a b t i).id)]

variable {R}

theorem knows_pair {τ : List (Ev P)} {x y : M P} (hx : threat.Knows τ x)
    (hy : threat.Knows τ y) : threat.Knows τ (.pair x y) :=
  ThreatModel.knows_rule (DYRule.pair x y) (by simp [hx, hy])

theorem knows_initial {τ : List (Ev P)} {m : M P} (h : m ∈ initialKnowledge) :
    threat.Knows τ m :=
  ThreatModel.knows_of_initial h

theorem knows_read_literal {τ : List (Ev P)} {s : String} (hs : s ∈ literals) :
    threat.Knows τ (R.read s) := by
  have h : R.read s = .name (.lit s) := R.literal s hs
  rw [h]
  exact knows_initial (Or.inr (Or.inr (Or.inl ⟨s, rfl⟩)))

theorem knows_strings {τ : List (Ev P)} :
    ∀ {ss : List String}, (∀ s ∈ ss, threat.Knows τ (R.read s)) →
      threat.Knows τ (R.strings ss)
  | [], _ => knows_initial (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  | s :: ss, h => knows_pair (h s (by simp)) (knows_strings fun x hx => h x (by simp [hx]))

theorem knows_tags {τ : List (Ev P)} :
    ∀ {ts : List (List String)}, (∀ t ∈ ts, ∀ s ∈ t, threat.Knows τ (R.read s)) →
      threat.Knows τ (R.tags ts)
  | [], _ => knows_initial (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  | t :: ts, h =>
      knows_pair (knows_strings (h t (by simp))) (knows_tags fun x hx => h x (by simp [hx]))

theorem knows_event {τ : List (Ev P)} {u : Unsigned} (hpk : threat.Knows τ (R.read u.pubkey))
    (ht : ∀ t ∈ u.tags, ∀ s ∈ t, threat.Knows τ (R.read s))
    (hc : threat.Knows τ (R.read u.content)) : threat.Knows τ (R.event u) :=
  knows_pair hpk (knows_pair (knows_initial (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))
    (knows_pair (knows_initial (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
      (knows_pair (knows_tags ht) hc)))

theorem knows_signEvent {τ : List (Ev P)} {p : P} {u : Unsigned} (hsk : threat.Knows τ (skOf p))
    (hu : threat.Knows τ (R.event u)) : threat.Knows τ (R.wire (signEvent R p u)) := by
  rw [wire_signEvent]
  have hh : threat.Knows τ (.hash (R.event u)) :=
    ThreatModel.knows_rule (DYRule.hash _) (by simp [hu])
  exact knows_pair hu (knows_pair hh (ThreatModel.knows_rule (DYRule.sign _ _) (by simp [hsk, hh])))

theorem knows_id {τ : List (Ev P)} {e : Nostr.Event} (h : threat.Knows τ (R.wire e)) :
    threat.Knows τ (R.read e.id) := by
  have h₁ : threat.Knows τ (Msg.snd (R.wire e)) :=
    ThreatModel.knows_rule (DYRule.snd _) (by simp [h])
  have h₂ : threat.Knows τ (Msg.fst (Msg.snd (R.wire e))) :=
    ThreatModel.knows_rule (DYRule.fst _) (by simp [h₁])
  simpa [Reading.wire] using h₂

theorem knows_content {τ : List (Ev P)} {e : Nostr.Event} (h : threat.Knows τ (R.wire e)) :
    threat.Knows τ (R.read e.content) := by
  have h₁ : threat.Knows τ (Msg.fst (R.wire e)) :=
    ThreatModel.knows_rule (DYRule.fst _) (by simp [h])
  have h₂ : threat.Knows τ (Msg.snd (Msg.fst (R.wire e))) :=
    ThreatModel.knows_rule (DYRule.snd _) (by simp [h₁])
  have h₃ : threat.Knows τ (Msg.snd (Msg.snd (Msg.fst (R.wire e)))) :=
    ThreatModel.knows_rule (DYRule.snd _) (by simp [h₂])
  have h₄ : threat.Knows τ (Msg.snd (Msg.snd (Msg.snd (Msg.fst (R.wire e))))) :=
    ThreatModel.knows_rule (DYRule.snd _) (by simp [h₃])
  have h₅ : threat.Knows τ (Msg.snd (Msg.snd (Msg.snd (Msg.snd (Msg.fst (R.wire e)))))) :=
    ThreatModel.knows_rule (DYRule.snd _) (by simp [h₄])
  simpa [Reading.wire, Reading.event] using h₅

theorem knows_convKey {τ : List (Ev P)} {a b : P} (hsk : threat.Knows τ (skOf a)) :
    threat.Knows τ (convKey a b) := by
  have hdh : threat.Knows τ (Msg.dh (skOf a) (pkOf b)) :=
    ThreatModel.knows_rule (DYRule.dh _ _) (by simp [hsk, knows_initial (Or.inl ⟨b, rfl⟩)])
  exact ThreatModel.knows_rule (DYRule.hash _) (by simp [hdh])

/-- The checks of an acceptance hold for `a`'s own signed mail. -/
theorem mail_checks (a b : P) (t : ℤ) (ℓ : M P) :
    let e := signEvent R a (mailEvent R a b t ℓ)
    e.kind = kindMail ∧ R.read e.pubkey = pkOf a ∧ R.write (pkOf b) ∈ tagValues e.tags "p" ∧
      R.read e.id = .hash (R.event e.toUnsigned) ∧
      Msg.verify (pkOf a) (R.read e.sig) = R.read e.id ∧
      Msg.sdec (convKey b a) (R.read e.content) = ℓ := by
  refine ⟨rfl, by simp [signEvent, mailEvent], by simp [signEvent, mailEvent, tagValues],
    by simp [signEvent, idOf], by simp [signEvent, idOf, pkOf], ?_⟩
  simp [signEvent, mailEvent, nip44, convKey_comm b a]

/-- The checks of a belief hold for `b`'s own signed receipt. -/
theorem receipt_checks (b a : P) (t : ℤ) (m : EventId) :
    let r := signEvent R b (receiptEvent R b a t m)
    r.kind = kindReaction ∧ R.read r.pubkey = pkOf b ∧
      R.read r.id = .hash (R.event r.toUnsigned) ∧
      Msg.verify (pkOf b) (R.read r.sig) = R.read r.id ∧ receiptFor r = some (m, "delivered") :=
  ⟨rfl, by simp [signEvent, receiptEvent], by simp [signEvent, idOf],
    by simp [signEvent, idOf, pkOf], receiptFor_receipt R rfl⟩

/-- An honest run is reachable: `b` accepts `a`'s letter, and `a` believes `b`'s receipt. -/
theorem honest_run (a b : P) (t t' : ℤ) (i : ℕ) :
    Reachable (DYStep threat (Step R)) (honestRun R a b t t' i) ∧
      Symbolic.Event.signal b (.accepted a (letterOf a b i) (mailMsg R a b t i).id) ∈
        honestRun R a b t t' i ∧
      Symbolic.Event.signal a (.believes b (mailMsg R a b t i).id) ∈ honestRun R a b t t' i := by
  refine ⟨?_, by simp [honestRun], by simp [honestRun]⟩
  set e := mailMsg R a b t i
  set m := e.id
  set r := receiptMsg R b a t' m
  have h₁ : Reachable (DYStep threat (Step R)) (mailBlock R a b t i) := by
    simpa [mailBlock, mailMsg] using
      Reachable.extend Reachable.nil (DYStep.honest (Step.mail (R := R) [] a b t i))
  have hk₁ : threat.Knows (mailBlock R a b t i) (R.wire e) :=
    standardThreat_knows_sent (pre := [_, _]) (post := []) rfl
  obtain ⟨hkind, hpk, hp, hid, hv, hℓ⟩ := mail_checks (R := R) a b t (letterOf a b i)
  set τ₂ := mailBlock R a b t i ++
    [.recv b (R.wire e), .signal b (.accepted a (letterOf a b i) m)]
  have h₂ : Reachable (DYStep threat (Step R)) τ₂ :=
    Reachable.extend h₁ (DYStep.honest (Step.accept _ b a e _ hk₁ hkind hpk hp hid hv hℓ
      (by simp [letterOf])))
  set τ₃ := τ₂ ++ [.signal b (.signed (receiptEvent R b a t' m)), .send (R.wire r)]
  have h₃ : Reachable (DYStep threat (Step R)) τ₃ :=
    Reachable.extend h₂ (DYStep.honest (Step.receipt _ b a t' m (letterOf a b i) (by simp [τ₂])))
  have hk₃ : threat.Knows τ₃ (R.wire r) :=
    standardThreat_knows_sent (pre := τ₂ ++ [.signal b (.signed (receiptEvent R b a t' m))])
      (post := []) (by simp [τ₃])
  obtain ⟨hkind', hpk', hid', hv', hrf⟩ := receipt_checks (R := R) b a t' m
  have h₄ := Reachable.extend h₃ (DYStep.honest (Step.believe _ a b r m "delivered"
    (mailEvent R a b t (letterOf a b i)) hk₃ hkind' hpk' hid' hv' hrf
    (by simp [τ₃, τ₂, mailBlock]) rfl (by simp [mailEvent, tagValues]) rfl))
  simpa [honestRun, τ₃, τ₂] using h₄

/-- Corrupting the sender after a mail reveals the letter: the exception in `secrecy` is
needed. -/
theorem corrupt_reveals (a b : P) (t : ℤ) (i : ℕ) :
    Reachable (DYStep threat (Step R)) (mailBlock R a b t i ++ [.corrupt a]) ∧
      threat.Knows (mailBlock R a b t i ++ [.corrupt a]) (letterOf a b i) := by
  refine ⟨Reachable.extend ?_ (DYStep.act ⟨a, rfl⟩), ?_⟩
  · simpa [mailBlock, mailMsg] using
      Reachable.extend Reachable.nil (DYStep.honest (Step.mail (R := R) [] a b t i))
  · set τ := mailBlock R a b t i ++ [Symbolic.Event.corrupt a]
    have hsk : threat.Knows τ (skOf a) :=
      standardThreat_knows_secret (pre := mailBlock R a b t i) (post := []) rfl rfl
    have hc : threat.Knows τ (R.read (mailMsg R a b t i).content) :=
      knows_content (standardThreat_knows_sent (pre := [_, _]) (post := [.corrupt a]) rfl)
    have hdec : threat.Knows τ (Msg.sdec (convKey a b) (R.read (mailMsg R a b t i).content)) :=
      ThreatModel.knows_rule (DYRule.sdec _ _) (by simp [knows_convKey hsk, hc])
    simpa [mailMsg, signEvent, mailEvent, nip44] using hdec

variable (R) in
/-- `a`'s key signing a mail for `b` whose letter is the attacker's own name. -/
def forgedMail (a b : P) (t : ℤ) : Nostr.Event :=
  signEvent R a (mailEvent R a b t (.name (.adv 0)))

/-- Corrupting the sender lets the attacker make `b` accept, as mail from `a`, a letter `a` never
mailed: the exception in `authentication` is needed. -/
theorem corrupt_forges_mail (a b : P) (t : ℤ) :
    Reachable (DYStep threat (Step R)) [.corrupt a, .recv b (R.wire (forgedMail R a b t)),
        .signal b (.accepted a (.name (.adv 0)) (forgedMail R a b t).id)] ∧
      Symbolic.Event.signal a (.mailed b (.name (.adv 0))) ∉
        ([.corrupt a, .recv b (R.wire (forgedMail R a b t)),
          .signal b (.accepted a (.name (.adv 0)) (forgedMail R a b t).id)] : List (Ev P)) := by
  refine ⟨?_, by simp⟩
  have h₁ : Reachable (DYStep threat (Step R)) [.corrupt a] := by
    simpa using Reachable.extend Reachable.nil
      (DYStep.act (T := threat) (honest := Step R) (τ := []) ⟨a, rfl⟩)
  have hsk : threat.Knows [Symbolic.Event.corrupt a] (skOf a) :=
    standardThreat_knows_secret (pre := []) (post := []) rfl rfl
  have hw : threat.Knows [Symbolic.Event.corrupt a] (R.wire (forgedMail R a b t)) := by
    refine knows_signEvent hsk (knows_event ?_ ?_ ?_)
    · simpa [mailEvent] using knows_initial (Or.inl ⟨a, rfl⟩)
    · intro tg htg s hs
      simp only [mailEvent, List.mem_singleton] at htg
      subst htg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact knows_read_literal (by simp [literals])
      · simpa using knows_initial (Or.inl ⟨b, rfl⟩)
    · simp only [mailEvent, Reading.read_write, nip44]
      exact ThreatModel.knows_rule (DYRule.senc _ _)
        (by simp [knows_convKey hsk, knows_initial (Or.inr (Or.inl ⟨0, rfl⟩))])
  obtain ⟨hkind, hpk, hp, hid, hv, hℓ⟩ := mail_checks (R := R) a b t (.name (.adv 0))
  simpa using Reachable.extend h₁ (DYStep.honest (Step.accept _ b a _ (.name (.adv 0)) hw hkind hpk
    hp hid hv hℓ (by simp)))

variable (R) in
/-- `b`'s key signing a receipt, for `a`, of `a`'s `i`-th mail. -/
def forgedReceipt (a b : P) (t t' : ℤ) (i : ℕ) : Nostr.Event :=
  receiptMsg R b a t' (mailMsg R a b t i).id

/-- Corrupting the addressee lets the attacker make `a` believe a receipt for mail `b` never
accepted: the exception in `receipt_authentic` is needed. -/
theorem corrupt_forges_receipt (a b : P) (t t' : ℤ) (i : ℕ) :
    Reachable (DYStep threat (Step R)) (mailBlock R a b t i ++ [.corrupt b] ++
        [.recv a (R.wire (forgedReceipt R a b t t' i)),
          .signal a (.believes b (mailMsg R a b t i).id)]) ∧
      ¬ ∃ a' ℓ, Symbolic.Event.signal b (.accepted a' ℓ (mailMsg R a b t i).id) ∈
        (mailBlock R a b t i ++ [.corrupt b] ++
          [.recv a (R.wire (forgedReceipt R a b t t' i)),
            .signal a (.believes b (mailMsg R a b t i).id)]) := by
  refine ⟨?_, by simp [mailBlock]⟩
  have h₀ : Reachable (DYStep threat (Step R)) (mailBlock R a b t i) := by
    simpa [mailBlock, mailMsg] using
      Reachable.extend Reachable.nil (DYStep.honest (Step.mail (R := R) [] a b t i))
  have h₁ : Reachable (DYStep threat (Step R)) (mailBlock R a b t i ++ [.corrupt b]) :=
    Reachable.extend h₀ (DYStep.act ⟨b, rfl⟩)
  set τ := mailBlock R a b t i ++ [Symbolic.Event.corrupt b]
  have hsk : threat.Knows τ (skOf b) :=
    standardThreat_knows_secret (pre := mailBlock R a b t i) (post := []) rfl rfl
  have hm : threat.Knows τ (R.read (mailMsg R a b t i).id) :=
    knows_id (standardThreat_knows_sent (pre := [_, _]) (post := [.corrupt b]) rfl)
  have hw : threat.Knows τ (R.wire (forgedReceipt R a b t t' i)) := by
    refine knows_signEvent hsk (knows_event ?_ ?_ ?_)
    · simpa [receiptEvent] using knows_initial (Or.inl ⟨b, rfl⟩)
    · intro tg htg s hs
      simp only [receiptEvent, List.mem_cons, List.not_mem_nil, or_false] at htg
      rcases htg with rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      · rcases hs with rfl | rfl
        · exact knows_read_literal (by simp [literals])
        · exact hm
      · rcases hs with rfl | rfl
        · exact knows_read_literal (by simp [literals])
        · simpa using knows_initial (Or.inl ⟨a, rfl⟩)
      · rcases hs with rfl | rfl <;> exact knows_read_literal (by simp [literals])
    · exact knows_read_literal (by simp [literals, receiptEvent])
  obtain ⟨hkind, hpk, hid, hv, hrf⟩ := receipt_checks (R := R) b a t' (mailMsg R a b t i).id
  exact Reachable.extend h₁ (DYStep.honest (Step.believe _ a b _ _ "delivered"
    (mailEvent R a b t (letterOf a b i)) hw hkind hpk hid hv hrf (by simp [τ, mailBlock]) rfl
    (by simp [mailEvent, tagValues]) rfl))

end Mettapedia.Protocols.Nostr.Sealed
