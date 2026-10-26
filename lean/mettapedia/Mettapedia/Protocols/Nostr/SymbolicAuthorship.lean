import Mettapedia.Protocols.Nostr.Bridge
import Mettapedia.Protocols.Nostr.Sealed

/-!
# The signature assumption of the Nostr model, derived

The string-level Nostr model takes its signature assumption as a hypothesis: `Authorship P`
(`Protocols.Nostr.Event`) says that a signature that verifies under a key the attacker does not
hold is the key owner's, on the identifier of an event the owner composed. The mail client
(`no_impersonation`, `limits_from_parent`, `receipt_sound`), the relay's sign-in
(`Relay.signin_authenticates`) and the bridge into claw-mail (`Gateway.bridge_no_impersonation`)
rest on it. This file shows that the symbolic semantics of agent mail
(`Protocols.Nostr.Sealed`) provides it.

*The primitives of an execution.* Given a reading `R` of strings as symbolic messages and a trace
`τ`, `primitives R τ` hashes an event by writing the hash of its denotation, and accepts a
signature string when its denotation is a valid signature, under the key the key string denotes,
on the identifier the identifier string denotes, and the attacker can derive it at `τ`. So
verification accepts exactly the valid signatures that exist in the execution so far. It agrees
with symbolic verification on everything the network carries, and it only grows as the trace grows
(`primitives_verify_mono`). Hashing is collision free (`collisionFree`).

*The discharge* (`authorship`). On every reachable trace, `Authorship (primitives R τ)` holds with
* `authored u`: `u` carries the key of a principal `p`, and `p` signed `u` in `τ`;
* `compromised k`: every principal whose public key `k` denotes has been corrupted in `τ`, so a key
  that is nobody's, such as the attacker's own, counts as compromised.
Its field `sound` comes from the symbolic invariant: everything the attacker knows is well formed
(`InvariantProof.knows_wf`), and a well-formed signature under an uncorrupted key was allowed by
the signing predicate (`WellFormed.sign_allowed`), which records the honest signing signals.

*Why verification depends on the trace.* `Authorship.sound` quantifies over all strings. A
symbolic signature on an event nobody signed is still a valid signature term, so no fixed
`Primitives` satisfies `Authorship` with `authored` read off a trace. Verification relative to
what exists at `τ` is the reading under which the string-level theorems describe a symbolic
execution: every event a relay or client checks has crossed the network, so its signature is
derivable. The consequences `client_no_impersonation`, `client_receipt_sound` and
`gateway_no_impersonation` transfer the string-level theorems to symbolic executions. On the
honest run, `a`'s mail is valid under the primitives of the run, authored, and signed by an
uncompromised key (`honest_mail_authentic`), so the derived assumption is not vacuous.
-/

namespace Mettapedia.Protocols.Nostr.Sealed

open Mettapedia.Protocols.Symbolic (Msg Reachable DYStep ThreatModel standardThreat_knows_sent)

variable {P : Type} [DecidableEq P] (R : Reading P)

/-- The string primitives of the execution `τ`: hashing writes the hash of an event's
denotation; verification accepts a signature that denotes a valid signature under the denoted key
on the denoted identifier, and that the attacker can derive at `τ`. -/
noncomputable def primitives (τ : List (Ev P)) : Primitives where
  hash u := idOf R u
  verify k d s := by
    classical
    exact decide (Msg.verify (R.read k) (R.read s) = R.read d ∧ R.read d ≠ .fail ∧
      threat.Knows τ (R.read s))

theorem primitives_hash (τ : List (Ev P)) (u : Unsigned) : (primitives R τ).hash u = idOf R u :=
  rfl

theorem primitives_verify {τ : List (Ev P)} {k d s : String} :
    (primitives R τ).verify k d s = true ↔
      Msg.verify (R.read k) (R.read s) = R.read d ∧ R.read d ≠ .fail ∧
        threat.Knows τ (R.read s) := by
  simp [primitives]

/-- Hashing is collision free. -/
theorem collisionFree (τ : List (Ev P)) : (primitives R τ).CollisionFree := by
  intro u v h
  have h' : R.write (.hash (R.event u)) = R.write (.hash (R.event v)) := h
  exact R.event_injective (Msg.hash.inj (R.write_injective h'))

/-- Verification only grows with the trace. -/
theorem primitives_verify_mono {τ τ' : List (Ev P)} (hτ : τ <+: τ') {k d s : String}
    (h : (primitives R τ).verify k d s = true) : (primitives R τ').verify k d s = true := by
  rw [primitives_verify] at h ⊢
  exact ⟨h.1, h.2.1, ThreatModel.knows_mono hτ h.2.2⟩

/-- Signatures are sound on every reachable trace: a signature that verifies, under the
primitives of the execution, with a key that belongs to no corrupted principal, is on the
identifier of an event that carries that key and that the key's owner signed. -/
theorem signature_sound {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ)
    {k d s : String} (hv : (primitives R τ).verify k d s = true)
    (hc : ¬ ∀ p, R.read k = pkOf p → Symbolic.Event.corrupt p ∈ τ) :
    ∃ u, (∃ p, R.read u.pubkey = pkOf p ∧ Symbolic.Event.signal p (.signed u) ∈ τ) ∧
      u.pubkey = k ∧ (primitives R τ).hash u = d := by
  obtain ⟨hver, hne, hks⟩ := (primitives_verify R).mp hv
  obtain ⟨x, hs, hk⟩ := Msg.eq_sign_of_verify hver hne
  rw [hs] at hks
  rcases Msg.WellFormed.sign_allowed ((proof R).knows_wf h hks) with
    hx | ⟨p, u, rfl, hd, hpk, hin⟩
  · refine absurd (fun p hp => ?_) hc
    rw [hk, pkOf, Msg.pk.injEq] at hp
    subst hp
    exact hx
  · refine ⟨u, ⟨p, hpk, hin⟩, R.read_injective (hpk.trans hk.symm), ?_⟩
    rw [primitives_hash, idOf, ← hd, Reading.write_read]

/-- **The signature assumption of the Nostr model holds of the symbolic semantics.** On every
reachable trace, `Authorship` holds of the primitives of the execution, with `authored u` read off
the honest signing signals (`u` carries `p`'s key and `p` signed `u`) and `compromised k` off the
corruption events (every principal whose key `k` denotes has been corrupted). -/
noncomputable def authorship {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ) :
    Authorship (primitives R τ) where
  authored u := ∃ p, R.read u.pubkey = pkOf p ∧ Symbolic.Event.signal p (.signed u) ∈ τ
  compromised k := ∀ p, R.read k = pkOf p → Symbolic.Event.corrupt p ∈ τ
  sound _ _ _ hv hc := signature_sound R h hv hc

theorem authorship_authored {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ)
    (u : Unsigned) :
    (authorship R h).authored u ↔
      ∃ p, R.read u.pubkey = pkOf p ∧ Symbolic.Event.signal p (.signed u) ∈ τ :=
  Iff.rfl

theorem authorship_compromised {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ)
    (k : PubKey) :
    (authorship R h).compromised k ↔ ∀ p, R.read k = pkOf p → Symbolic.Event.corrupt p ∈ τ :=
  Iff.rfl

/-- A principal's key is compromised exactly when the principal has been corrupted. -/
theorem compromised_pkOf {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ) (p : P) :
    (authorship R h).compromised (R.write (pkOf p)) ↔ Symbolic.Event.corrupt p ∈ τ := by
  rw [authorship_compromised]
  constructor
  · exact fun hc => hc p (R.read_write _)
  · intro hc q hq
    rw [Reading.read_write] at hq
    simp only [pkOf, skOf, Msg.pk.injEq, Msg.name.injEq, Name.sk.injEq] at hq
    exact hq ▸ hc

/-- A principal's key is compromised exactly when the attacker holds its secret, as the Nostr
model reads `compromised`. -/
theorem compromised_pkOf_iff_knows {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ)
    (p : P) : (authorship R h).compromised (R.write (pkOf p)) ↔ threat.Knows τ (skOf p) := by
  rw [compromised_pkOf, knows_sk_iff h]

/-! ## The string-level theorems, for symbolic executions -/

/-- The mail client, verifying with the primitives of a symbolic execution, archives mail as from
a member whose key is `p`'s only if `p` signed that event, unless `p` has been corrupted: the
string-level `no_impersonation` with the derived assumption. -/
theorem client_no_impersonation {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ)
    {opener : Opener} {reg : Registry} (hu : (reg.map Prod.fst).Nodup) {me : PubKey}
    {e : Nostr.Event} {l : Letter} (ha : accept (primitives R τ) opener reg me e = some l)
    {n : String} {p : P} (hn : (render reg e l).originator = n)
    (hk : (n, R.write (pkOf p)) ∈ reg) (hc : Symbolic.Event.corrupt p ∉ τ) :
    e.pubkey = R.write (pkOf p) ∧ Symbolic.Event.signal p (.signed e.toUnsigned) ∈ τ := by
  obtain ⟨hpk, q, hq, hin⟩ := no_impersonation (authorship R h) (collisionFree R τ) hu ha hn hk
    (by rwa [compromised_pkOf])
  have hqp : q = p := by
    rw [show e.toUnsigned.pubkey = e.pubkey from rfl, hpk, Reading.read_write] at hq
    simp only [pkOf, skOf, Msg.pk.injEq, Msg.name.injEq, Name.sk.injEq] at hq
    exact hq.symm
  exact ⟨hpk, hqp ▸ hin⟩

/-- A receipt the client believes, verifying with the primitives of a symbolic execution, names a
mail sent to the receipt's signer, and if that signer's key is `b`'s and `b` has not been
corrupted, `b` signed the receipt: the string-level `receipt_sound` with the derived assumption. -/
theorem client_receipt_sound {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ)
    {reg : Registry} {sent : List Mail.Message} {r : Nostr.Event} {m : EventId} {st : String}
    (hb : believes (primitives R τ) reg sent r = some (m, st)) {b : P}
    (hkey : r.pubkey = R.write (pkOf b)) (hc : Symbolic.Event.corrupt b ∉ τ) :
    (∃ s ∈ sent, s.id = m) ∧ Symbolic.Event.signal b (.signed r.toUnsigned) ∈ τ := by
  obtain ⟨s, hs, hid, -, -, -, hauth⟩ := receipt_sound (authorship R h) (collisionFree R τ) hb
  refine ⟨⟨s, hs, hid⟩, ?_⟩
  obtain ⟨q, hq, hin⟩ := hauth (by rw [hkey, compromised_pkOf]; exact hc)
  have hqb : q = b := by
    rw [show r.toUnsigned.pubkey = r.pubkey from rfl, hkey, Reading.read_write] at hq
    simp only [pkOf, skOf, Msg.pk.injEq, Msg.name.injEq, Name.sk.injEq] at hq
    exact hq.symm
  exact hqb ▸ hin

/-- Mail the gateway records in claw-mail as from a member whose key is `p`'s was signed by `p`,
unless `p` has been corrupted, when the gateway verifies with the primitives of a symbolic
execution: the string-level `Gateway.bridge_no_impersonation` with the derived assumption. -/
theorem gateway_no_impersonation {τ : List (Ev P)} (h : Reachable (DYStep threat (Step R)) τ)
    {g : Gateway} (hP : g.P = primitives R τ) (hu : (g.reg.map Prod.fst).Nodup)
    {e : Nostr.Event} {l : Letter} (hk : g.keep e = some l) {n : String} {p : P}
    (hn : (g.delivery e l).sender.agent = bridgedPrefix ++ n) (hreg : (n, R.write (pkOf p)) ∈ g.reg)
    (hc : Symbolic.Event.corrupt p ∉ τ) :
    e.pubkey = R.write (pkOf p) ∧ Symbolic.Event.signal p (.signed e.toUnsigned) ∈ τ := by
  obtain ⟨P', opener, reg, me, account, owner, format⟩ := g
  simp only at hP
  subst hP
  obtain ⟨hpk, q, hq, hin⟩ := Gateway.bridge_no_impersonation (authorship R h) (collisionFree R τ)
    hu hk hn hreg (by rwa [compromised_pkOf])
  have hqp : q = p := by
    rw [show e.toUnsigned.pubkey = e.pubkey from rfl, hpk, Reading.read_write] at hq
    simp only [pkOf, skOf, Msg.pk.injEq, Msg.name.injEq, Name.sk.injEq] at hq
    exact hq.symm
  exact ⟨hpk, hqp ▸ hin⟩

/-- What the symbolic client checks before accepting an event makes the event valid under the
primitives of the execution. -/
theorem valid_of_checks {τ : List (Ev P)} {e : Nostr.Event} {a : P}
    (hk : threat.Knows τ (R.wire e)) (hpk : R.read e.pubkey = pkOf a)
    (hid : R.read e.id = .hash (R.event e.toUnsigned))
    (hv : Msg.verify (pkOf a) (R.read e.sig) = R.read e.id) : e.Valid (primitives R τ) := by
  refine ⟨?_, ?_⟩
  · rw [primitives_hash, idOf, ← hid, Reading.write_read]
  · rw [primitives_verify, hpk]
    refine ⟨hv, by rw [hid]; simp, ?_⟩
    have h₁ : threat.Knows τ (Msg.snd (R.wire e)) :=
      ThreatModel.knows_rule (Symbolic.DYRule.snd _) (by simp [hk])
    have h₂ : threat.Knows τ (Msg.snd (Msg.snd (R.wire e))) :=
      ThreatModel.knows_rule (Symbolic.DYRule.snd _) (by simp [h₁])
    simpa [Reading.wire] using h₂

/-- The derived assumption is not vacuous: on the honest run, `a`'s mail is valid under the
primitives of the run, its key is uncompromised, and the client's string-level authenticity
theorem concludes that `a` signed it. -/
theorem honest_mail_authentic (a b : P) (t t' : ℤ) (i : ℕ) :
    ∃ h : Reachable (DYStep threat (Step R)) (honestRun R a b t t' i),
      (mailMsg R a b t i).Valid (primitives R (honestRun R a b t t' i)) ∧
        ¬ (authorship R h).compromised (mailMsg R a b t i).pubkey ∧
          (authorship R h).authored (mailMsg R a b t i).toUnsigned := by
  obtain ⟨h, -, -⟩ := honest_run (R := R) a b t t' i
  have hsent : threat.Knows (honestRun R a b t t' i) (R.wire (mailMsg R a b t i)) :=
    standardThreat_knows_sent (pre := [_, _]) (post := _) rfl
  obtain ⟨-, hpk, -, hid, hv, -⟩ := mail_checks (R := R) a b t (letterOf a b i)
  have hvalid := valid_of_checks R hsent hpk hid hv
  have hnc : ¬ (authorship R h).compromised (mailMsg R a b t i).pubkey := by
    rw [show (mailMsg R a b t i).pubkey = R.write (pkOf a) from rfl, compromised_pkOf]
    simp [honestRun, mailBlock]
  exact ⟨h, hvalid, hnc, authentic (authorship R h) (collisionFree R _) hvalid hnc⟩

end Mettapedia.Protocols.Nostr.Sealed
