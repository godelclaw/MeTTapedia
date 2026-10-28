import Mettapedia.Protocols.Symbolic.Message

/-!
# Worked example: a signed and sealed message

`a` sends `b` a plaintext `m`, signed with `a`'s long-term key and encrypted under a key that
only `a` and `b` can derive:

  `sealMsg a b m = senc (convKey a b) ⟨m, sign (sk a) ⟨pk (sk b), m⟩⟩`,
  `convKey a b = hash (dh (sk a) (pk (sk b)))`.

This is the shape of a sealed direct message on Nostr: NIP-44's conversation key is derived by
a hash (HKDF) from the ECDH secret of sender and recipient, the content is encrypted under it with
authenticated encryption, and the sender's BIP-340 signature authenticates the sender. The
recipient's public key is part of the signed content, so a signed plaintext cannot be forwarded
to another recipient as if addressed to them. The model is symbolic: keys are names, encryption
and signatures are perfect, and NIP-44's per-message nonce, padding and MAC are folded into one
authenticated encryption. Agent mail over Nostr (`Protocols.Nostr.Mailbox`) and NIP-59 sign
instead an event carrying the ciphertext and the recipient's `p` tag; the method is the same,
with a signing predicate about such events, and `convKey_inj_right` binds a ciphertext to its
recipient.

The plaintexts are names `payload a b i`, labelled "readable by `a` and `b`". Each principal
holds a long-term secret key `sk p`. The attacker initially knows every public key and its own
names `adv i`. The threat model is the standard one: the attacker is the network and can apply
every operation of the message algebra, and it may corrupt any principal at any time, learning
that principal's secret key. A principal sends at any time, and accepts any message the network
delivers that unseals correctly.

Proved for every reachable trace, with any number of principals, messages and corruptions:
* secrecy (`secrecy`): if the attacker knows `payload a b i`, then `a` or `b` has been
  corrupted; so an attacker holding neither secret key does not know it (`secrecy_of_keys`);
* unforgeability (`knows_sign`): a signature under `a`'s key that the attacker knows was made by
  `a` when sending, or `a` has been corrupted;
* authentication (`authentication`): if `b` accepted `m` as coming from `a`, then earlier `a`
  sent `m` to `b`, or `a` had been corrupted; so if the attacker did not know `a`'s key when `b`
  accepted, `a` sent `m` to `b` (`authentication_of_keys`).
Authentication here is agreement on sender, recipient and plaintext, not freshness: a replayed
message is accepted again (a mailbox deduplicates by message identifier). There is no forward
secrecy: a later compromise of `a` or `b` exposes earlier plaintexts.

Sanity checks show that the theorems are not vacuous: an honest run is reachable and ends with
acceptance (`honest_run`); corrupting the sender after a send reveals the plaintext
(`corrupt_reveals`); corrupting the sender lets the attacker make `b` accept a message `a` never
sent (`corrupt_forges`).

The proof instantiates `InvariantProof` (`proof`): name labels, the signing predicate "`a` signs
`⟨pk b, m⟩` only when sending `m` to `b`", and an entry invariant saying that every message on the
network or received is publishable and that every acceptance was preceded by the matching send or
by the sender's corruption.
-/

namespace Mettapedia.Protocols.Symbolic.SealedMessage

open Msg

/-- Names: long-term secret keys, plaintexts, and the attacker's own names. -/
inductive Name (P : Type) where
  | sk (p : P)
  | payload (a b : P) (i : ℕ)
  | adv (i : ℕ)
deriving DecidableEq

/-- Messages of the example. -/
abbrev M (P : Type) := Msg (Name P)

/-- What a principal records: that it sent `m` to `recipient`, or accepted `m` as from
`sender`. -/
inductive Signal (P : Type) where
  | sent (recipient : P) (m : M P)
  | accepted (sender : P) (m : M P)

/-- Trace events of the example. -/
abbrev Ev (P : Type) := Event P (M P) (Signal P)

variable {P : Type}

/-- The secret key of `p`. -/
def skOf (p : P) : M P := .name (.sk p)

/-- The public key of `p`. -/
def pkOf (p : P) : M P := .pk (skOf p)

/-- The `i`-th plaintext from `a` to `b`. -/
def payload (a b : P) (i : ℕ) : M P := .name (.payload a b i)

/-- The conversation key of `a` with `b`: a hash of their Diffie–Hellman secret. -/
def convKey (a b : P) : M P := .hash (dh (skOf a) (pkOf b))

theorem convKey_eq (a b : P) : convKey a b = .hash (.shared s(.sk a, .sk b)) := rfl

/-- Both parties derive the same conversation key. -/
theorem convKey_comm (a b : P) : convKey a b = convKey b a := by
  simp only [convKey_eq, Sym2.eq_swap]

/-- The conversation key determines the peer: `a`'s keys with `b` and with `b'` coincide only
if `b = b'`. A ciphertext under `convKey a b` is therefore bound to its recipient, which is what a
sender signature over a ciphertext (NIP-59, or a NIP-44 encrypted event) relies on. -/
theorem convKey_inj_right {a b b' : P} : convKey a b = convKey a b' ↔ b = b' := by
  simp only [convKey_eq, Msg.hash.injEq, Msg.shared.injEq, Sym2.congr_right, Name.sk.injEq]

/-- The sealed message from `a` to `b` with plaintext `m`. -/
def sealMsg (a b : P) (m : M P) : M P :=
  .senc (convKey a b) (.pair m (.sign (skOf a) (.pair (pkOf b) m)))

variable [DecidableEq P]

/-- `b` opens `c` as a message from `a`: decrypt with the conversation key, then check `a`'s
signature on `⟨pk b, m⟩`. -/
def unsealMsg (b a : P) (c : M P) : Option (M P) :=
  match sdec (convKey b a) c with
  | .pair m s => if verify (pkOf a) s = .pair (pkOf b) m then some m else none
  | _ => none

theorem unsealMsg_sealMsg (a b : P) (m : M P) : unsealMsg b a (sealMsg a b m) = some m := by
  rw [unsealMsg, sealMsg, convKey_comm b a, sdec_senc]
  simp [pkOf]

/-- A message that unseals is a ciphertext under the conversation key of a pair whose second
component verifies under `a`'s public key. -/
theorem unsealMsg_eq_some {b a : P} {c m : M P} (h : unsealMsg b a c = some m) :
    ∃ s, c = .senc (convKey b a) (.pair m s) ∧ verify (pkOf a) s = .pair (pkOf b) m := by
  unfold unsealMsg at h
  generalize hd : sdec (convKey b a) c = d at h
  cases d with
  | pair m' s =>
      by_cases hv : verify (pkOf a) s = .pair (pkOf b) m'
      · simp only [hv, if_true, Option.some.injEq] at h
        subst h
        exact ⟨s, eq_senc_of_sdec hd (by simp), hv⟩
      · simp [hv] at h
  | _ => simp at h

/-! ## Threat model and protocol -/

/-- The attacker's initial knowledge: every public key and its own names. -/
def initialKnowledge : Set (M P) := {m | (∃ p, m = pkOf p) ∨ ∃ i, m = .name (.adv i)}

/-- The standard threat model: the attacker is the network, applies every operation of the
algebra, and corrupting `p` reveals `p`'s secret key. -/
def threat : ThreatModel (Ev P) (M P) :=
  standardThreat DYRule initialKnowledge (fun p => {skOf p})

/-- The honest steps. -/
inductive Step : List (Ev P) → List (Ev P) → Prop
  /-- `a` sends its `i`-th plaintext for `b`, sealed. -/
  | send (τ : List (Ev P)) (a b : P) (i : ℕ) :
      Step τ [.signal a (.sent b (payload a b i)), .send (sealMsg a b (payload a b i))]
  /-- `b` takes `c` from the network and accepts `m` as from `a` when `c` unseals to `m`. -/
  | accept (τ : List (Ev P)) (b a : P) (c m : M P) :
      threat.Knows τ c → unsealMsg b a c = some m → Step τ [.recv b c, .signal b (.accepted a m)]

/-! ## The invariant -/

/-- Intended secrecy of names: `sk p` is readable by `p`, `payload a b i` by `a` and `b`, and the
attacker's names are public. -/
noncomputable def nameLabel : Name P → Label (Ev P)
  | .sk p => Label.after (.corrupt p)
  | .payload a b _ => Label.after (.corrupt a) ⊔ Label.after (.corrupt b)
  | .adv _ => ⊤

/-- Honest `a` signs only `⟨pk b, m⟩` for a message `m` it sent to `b`; encryption is
unrestricted. -/
def preds : CryptoPreds (Ev P) (M P) where
  sign τ k x := ∃ a b m, k = skOf a ∧ x = .pair (pkOf b) m ∧ Event.signal a (.sent b m) ∈ τ
  enc _ _ _ := True
  sign_mono h := fun ⟨a, b, m, hk, hx, hin⟩ => ⟨a, b, m, hk, hx, List.IsPrefix.mem hin h⟩
  enc_mono _ _ := trivial

/-- Publishability for the example. -/
noncomputable def pub : Publishability (Ev P) (M P) DYRule := Msg.publishability nameLabel preds

/-- The entry invariant: messages on the network and received messages are publishable; an
acceptance from `a` follows the matching send by `a` or a corruption of `a`; nobody generates or
stores anything. -/
noncomputable def inv : List (Ev P) → Ev P → Prop
  | τ, .send m => pub.Pub τ m
  | τ, .recv _ m => pub.Pub τ m
  | τ, .signal b (.accepted a m) => Event.signal a (.sent b m) ∈ τ ∨ Event.corrupt a ∈ τ
  | _, .signal _ (.sent _ _) => True
  | _, .corrupt _ => True
  | _, .gen _ _ => False
  | _, .state _ _ => False

theorem label_payload (a b : P) (i : ℕ) (τ : List (Ev P)) :
    pub.label (payload a b i) τ ↔ Event.corrupt a ∈ τ ∨ Event.corrupt b ∈ τ := Iff.rfl

theorem label_sk (p : P) (τ : List (Ev P)) : pub.label (skOf p) τ ↔ Event.corrupt p ∈ τ :=
  Iff.rfl

/-- What `a` sends is publishable once it has recorded the send. -/
theorem sealMsg_pub (τ : List (Ev P)) (a b : P) (i : ℕ)
    (hsent : Event.signal a (.sent b (payload a b i)) ∈ τ) :
    pub.Pub τ (sealMsg a b (payload a b i)) := by
  refine ⟨trivial, ?_, ?_, ?_, Or.inr trivial⟩
  · simp [convKey_eq]
  · exact ⟨trivial, trivial, ⟨trivial, trivial⟩, Or.inr ⟨a, b, payload a b i, rfl, rfl, hsent⟩⟩
  · -- the key is readable by `a` and `b`, exactly as the plaintext
    exact Label.flowsAt_of_le fun _ h => ⟨h, trivial, h⟩

/-- What `b` accepts from `a` was sent by `a` to `b`, or `a` was compromised. -/
theorem accept_inv {τ : List (Ev P)} {b a : P} {c m : M P} (hc : pub.Pub τ c)
    (hu : unsealMsg b a c = some m) :
    Event.signal a (.sent b m) ∈ τ ∨ Event.corrupt a ∈ τ := by
  obtain ⟨s, rfl, hv⟩ := unsealMsg_eq_some hu
  obtain ⟨k, rfl, hk⟩ := eq_sign_of_verify hv (by simp)
  have hk' : k = skOf a := by
    simp only [pkOf, Msg.pk.injEq] at hk
    exact hk.symm
  subst hk'
  have hsig : WellFormed nameLabel preds τ (.sign (skOf a) (.pair (pkOf b) m)) :=
    hc.2.2.1.2
  rcases hsig.sign_allowed with hcor | ⟨a', b', m', hk, hx, hin⟩
  · exact Or.inr hcor
  · simp only [skOf, Msg.name.injEq, Name.sk.injEq] at hk
    simp only [pkOf, skOf, Msg.pair.injEq, Msg.pk.injEq, Msg.name.injEq, Name.sk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    subst hk
    exact Or.inl hin

/-- The invariant proof of the example. -/
noncomputable def proof : InvariantProof (threat (P := P)) Step where
  pub := pub
  inv := inv
  initial_pub := by
    rintro m (⟨p, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨trivial, trivial⟩
    · exact ⟨trivial, trivial⟩
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
        · obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp (show Event.state p m ∈ τ from hm)
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
    intro τ new _ hknows hstep
    cases hstep with
    | send a b i =>
        refine ⟨trivial, sealMsg_pub _ a b i (List.mem_append_right _ (List.mem_singleton_self _)),
          trivial⟩
    | accept b a c m hk hu =>
        refine ⟨hknows c hk, ?_, trivial⟩
        rcases accept_inv (hknows c hk) hu with h | h
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr (List.mem_append_left _ h)

/-! ## Security theorems -/

/-- Secrecy: if the attacker knows the plaintext `payload a b i`, then `a` or `b` has been
corrupted. -/
theorem secrecy {τ : List (Ev P)} (h : Reachable (DYStep threat Step) τ) {a b : P} {i : ℕ}
    (hk : threat.Knows τ (payload a b i)) :
    Event.corrupt a ∈ τ ∨ Event.corrupt b ∈ τ :=
  (label_payload a b i τ).mp (proof.label_corrupt h hk)

/-- An attacker that holds neither `a`'s nor `b`'s secret key does not know `payload a b i`. -/
theorem secrecy_of_keys {τ : List (Ev P)} (h : Reachable (DYStep threat Step) τ) {a b : P}
    {i : ℕ} (ha : ¬ threat.Knows τ (skOf a)) (hb : ¬ threat.Knows τ (skOf b)) :
    ¬ threat.Knows τ (payload a b i) := by
  intro hk
  rcases secrecy h hk with hc | hc
  · obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hc
    exact ha (standardThreat_knows_secret rfl rfl)
  · obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hc
    exact hb (standardThreat_knows_secret rfl rfl)

/-- Unforgeability: a signature under `a`'s key known to the attacker was made by `a` on
`⟨pk b, m⟩` when sending `m` to `b`, or `a` has been corrupted. -/
theorem knows_sign {τ : List (Ev P)} (h : Reachable (DYStep threat Step) τ) {a : P} {x : M P}
    (hk : threat.Knows τ (.sign (skOf a) x)) :
    Event.corrupt a ∈ τ ∨ ∃ b m, x = .pair (pkOf b) m ∧ Event.signal a (.sent b m) ∈ τ := by
  rcases WellFormed.sign_allowed (proof.knows_wf h hk) with hc | ⟨a', b, m, ha, hx, hin⟩
  · exact Or.inl hc
  · simp only [skOf, Msg.name.injEq, Name.sk.injEq] at ha
    subst ha
    exact Or.inr ⟨b, m, hx, hin⟩

/-- Authentication: if `b` accepted `m` as from `a`, then before that `a` sent `m` to `b`, or
`a` had been corrupted. -/
theorem authentication {τ pre post : List (Ev P)} (h : Reachable (DYStep threat Step) τ)
    {a b : P} {m : M P} (he : τ = pre ++ .signal b (.accepted a m) :: post) :
    Event.signal a (.sent b m) ∈ pre ∨ Event.corrupt a ∈ pre :=
  proof.entry h he

/-- If the attacker did not know `a`'s secret key when `b` accepted `m` as from `a`, then `a`
had sent `m` to `b`. -/
theorem authentication_of_keys {τ pre post : List (Ev P)} (h : Reachable (DYStep threat Step) τ)
    {a b : P} {m : M P} (he : τ = pre ++ .signal b (.accepted a m) :: post)
    (ha : ¬ threat.Knows pre (skOf a)) :
    Event.signal a (.sent b m) ∈ pre := by
  rcases authentication h he with hs | hc
  · exact hs
  · obtain ⟨l, r, rfl⟩ := List.mem_iff_append.mp hc
    exact (ha (standardThreat_knows_secret rfl rfl)).elim

/-! ## Sanity checks -/

/-- `a` sends its `i`-th plaintext to `b`. -/
def sendBlock (a b : P) (i : ℕ) : List (Ev P) :=
  [.signal a (.sent b (payload a b i)), .send (sealMsg a b (payload a b i))]

theorem knows_of_sendBlock (a b : P) (i : ℕ) (post : List (Ev P)) :
    threat.Knows (sendBlock a b i ++ post) (sealMsg a b (payload a b i)) :=
  standardThreat_knows_sent (pre := [_]) (post := post) rfl

/-- An honest run is reachable and ends with `b` accepting `a`'s plaintext. -/
theorem honest_run (a b : P) (i : ℕ) :
    Reachable (DYStep threat Step) (sendBlock a b i ++
      [.recv b (sealMsg a b (payload a b i)), .signal b (.accepted a (payload a b i))]) := by
  have h₁ : Reachable (DYStep threat Step) (sendBlock a b i) := by
    simpa [sendBlock] using Reachable.extend Reachable.nil (DYStep.honest (Step.send [] a b i))
  exact Reachable.extend h₁ (DYStep.honest (Step.accept _ b a _ _
    (by simpa using knows_of_sendBlock a b i []) (unsealMsg_sealMsg a b _)))

/-- Corrupting the sender after a send reveals the plaintext, so the exception in `secrecy` is
needed. -/
theorem corrupt_reveals (a b : P) (i : ℕ) :
    Reachable (DYStep threat Step) (sendBlock a b i ++ [.corrupt a]) ∧
      threat.Knows (sendBlock a b i ++ [.corrupt a]) (payload a b i) := by
  refine ⟨Reachable.extend ?_ (DYStep.act ⟨a, rfl⟩), ?_⟩
  · simpa [sendBlock] using Reachable.extend Reachable.nil (DYStep.honest (Step.send [] a b i))
  · set τ := sendBlock a b i ++ [Event.corrupt a]
    have hsk : threat.Knows τ (skOf a) :=
      standardThreat_knows_secret (pre := sendBlock a b i) (post := []) rfl rfl
    have hpk : threat.Knows τ (pkOf b) := ThreatModel.knows_of_initial (Or.inl ⟨b, rfl⟩)
    have hdh : threat.Knows τ (dh (skOf a) (pkOf b)) :=
      ThreatModel.knows_rule (DYRule.dh _ _) (by simp [hsk, hpk])
    have hkey : threat.Knows τ (convKey a b) :=
      ThreatModel.knows_rule (DYRule.hash _) (by simpa using hdh)
    have hc : threat.Knows τ (sealMsg a b (payload a b i)) := knows_of_sendBlock a b i _
    have hdec : threat.Knows τ (sdec (convKey a b) (sealMsg a b (payload a b i))) :=
      ThreatModel.knows_rule (DYRule.sdec _ _) (by simp [hkey, hc])
    have hfst : threat.Knows τ (sdec (convKey a b) (sealMsg a b (payload a b i))).fst :=
      ThreatModel.knows_rule (DYRule.fst _) (by simpa using hdec)
    simpa [sealMsg] using hfst

/-- Corrupting the sender lets the attacker make `b` accept, as from `a`, a message `a` never sent,
so the exception in `authentication` is needed. -/
theorem corrupt_forges (a b : P) :
    Reachable (DYStep threat Step) [.corrupt a, .recv b (sealMsg a b (.name (.adv 0))),
        .signal b (.accepted a (.name (.adv 0)))] ∧
      Event.signal a (.sent b (.name (.adv 0))) ∉
        ([.corrupt a, .recv b (sealMsg a b (.name (.adv 0))),
          .signal b (.accepted a (.name (.adv 0)))] : List (Ev P)) := by
  refine ⟨?_, by simp⟩
  set x : M P := .name (.adv 0)
  have h₁ : Reachable (DYStep threat Step) [.corrupt a] := by
    simpa using Reachable.extend Reachable.nil (DYStep.act (T := threat) (honest := Step)
      (τ := []) ⟨a, rfl⟩)
  set τ : List (Ev P) := [.corrupt a]
  have hsk : threat.Knows τ (skOf a) :=
    standardThreat_knows_secret (pre := []) (post := []) rfl rfl
  have hpk : threat.Knows τ (pkOf b) := ThreatModel.knows_of_initial (Or.inl ⟨b, rfl⟩)
  have hx : threat.Knows τ x := ThreatModel.knows_of_initial (Or.inr ⟨0, rfl⟩)
  have hsigned : threat.Knows τ (.pair (pkOf b) x) :=
    ThreatModel.knows_rule (DYRule.pair _ _) (by simp [hpk, hx])
  have hsig : threat.Knows τ (.sign (skOf a) (.pair (pkOf b) x)) :=
    ThreatModel.knows_rule (DYRule.sign _ _) (by simp [hsk, hsigned])
  have hbody : threat.Knows τ (.pair x (.sign (skOf a) (.pair (pkOf b) x))) :=
    ThreatModel.knows_rule (DYRule.pair _ _) (by simp [hx, hsig])
  have hdh : threat.Knows τ (dh (skOf a) (pkOf b)) :=
    ThreatModel.knows_rule (DYRule.dh _ _) (by simp [hsk, hpk])
  have hkey : threat.Knows τ (convKey a b) :=
    ThreatModel.knows_rule (DYRule.hash _) (by simpa using hdh)
  have hc : threat.Knows τ (sealMsg a b x) :=
    ThreatModel.knows_rule (DYRule.senc _ _) (by simp [hkey, hbody])
  simpa [τ] using
    Reachable.extend h₁ (DYStep.honest (Step.accept τ b a _ _ hc (unsealMsg_sealMsg a b x)))

end Mettapedia.Protocols.Symbolic.SealedMessage
