import Mettapedia.Protocols.Nostr.Bridge
import Mettapedia.Protocols.Nostr.Relay

/-!
# Ingress order: every effect takes a verified event

Anyone can send an event with any claimed fields: a key, an identifier, a kind, tags, content.
Only the check of the identifier against the signed fields, and of the signature on it
(`Event.check`), shows that the claims are the key owner's. Ingress is *verify-first* when nothing
that reads a claimed field happens before that check: no database lookup, no pairing entry, no
policy callback, no reply addressed by a claim. A verification cache is part of the check, and
sound only as shown below.

Two things come before the check and are outside these models. Transport checks read only the
connection and the frame's size, such as size limits and per-connection rates. The answer to the
connection that sent the event, such as NIP-01's `OK` with `false`, names the claimed identifier
to that sender alone.

The general theorems, for a handler with any state and any effects:
- `claimBlind_iff`: a handler treats all events that fail the check alike, whatever they claim,
  exactly when any two streams that differ only in their forged events give the same final state
  and the same effects.
- `claimBlind_eq_verifyFirst`: every such handler is verify-first ingress. Its core, the handling
  of verified events, is unrestricted, so the order is the only restriction.
- `verifyFirst_effect`: under verify-first ingress that ignores failures, every effect is the
  core's, on an event of the stream that passed the check, and the forged events can be cut from
  any stream (`verifyFirst_filter`).

Two advisories of 2026 broke the order, and each flawed order is refuted here.
- RUSTSEC-2026-0232, nostr-relay-pool before 0.44.3:
  - Events from a relay went to admission policy and the database before verification, and a
    stored event with the claimed identifier let verification be skipped. An event that claims a
    stored identifier with other fields then reaches processing (`lookupFirst_forgery`). With the
    check first, processing sees only authentic events (`checkedPool_authentic`).
  - The verification cache was keyed by a 64-bit hash of the identifier. Every event with a correct
    identifier whose key is cached passes, whatever its signature (`cachedCheck_of_cached`), so a
    collision of keys lets a forgery pass (`truncatedCache_forgery`). Keyed by the whole
    identifier, the cache is sound (`cachedCheck_authentic`). A hit vouches for the fields and not
    for the signature (`cachedCheck_unsigned`), so what is kept or forwarded after a hit is the copy
    that was checked.
- GHSA-h43v-27wg-5mf9, OpenClaw before 2026.3.31: a DM could make a pending pairing entry and a
  pairing challenge before its signature was checked. A forged DM then makes both for a key whose
  owner sent nothing (`pairFirst_forged`). Pairing after the check names only keys whose owners
  composed a DM of the stream (`pairAfter_authentic`). It does not bound the table: fresh keys
  cost nothing, and valid DMs from them fill it (`pairAfter_fresh_keys`). That bound is a question
  of rates.

The models of our relay, the mailbox client and the gateway follow the order (`publish_forged`,
`accept_forged`, `bridge_forged`).

The equivalences are of behaviour, the final state and the effects. They say nothing of the work a
handler does before its check, such as its time. That running code follows a model is a separate
obligation.

Not modelled: concurrency, where a verification that finishes later must still come before every
effect of its event, and the cost of verification, which is what a cache saves.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.Ingress

open Mettapedia.Protocols

/-! ## Handlers -/

/-- An ingress handler with state `S` and effects `F`: from the state and a received event, the
next state and the effects. -/
abbrev Handler (S F : Type) := S → Event → S × List F

variable {S F : Type}

/-- A handler run over a stream of received events, in order: the final state, and the effects in
the order they happened. -/
def run (h : Handler S F) : S → List Event → S × List F
  | s, [] => (s, [])
  | s, e :: es => ((run h (h s e).1 es).1, (h s e).2 ++ (run h (h s e).1 es).2)

@[simp] theorem run_nil (h : Handler S F) (s : S) : run h s [] = (s, []) := rfl

@[simp] theorem run_cons (h : Handler S F) (s : S) (e : Event) (es : List Event) :
    run h s (e :: es) = ((run h (h s e).1 es).1, (h s e).2 ++ (run h (h s e).1 es).2) := rfl

/-- An event whose identifier and signature have been checked. -/
abbrev Verified (P : Primitives) := {e : Event // e.Valid P}

/-- Verify-first ingress: an event reaches `core` only after the check, and every event that fails
it gets the one response `fail`, which sees nothing of the event. -/
def verifyFirst (P : Primitives) (core : S → Verified P → S × List F) (fail : S → S × List F) :
    Handler S F :=
  fun s e => if hc : e.check P then core s ⟨e, (Event.check_iff P e).mp hc⟩ else fail s

/-- The response to failure that changes nothing. -/
def ignore : S → S × List F := fun s => (s, [])

/-- A handler is blind to claims when it handles all events that fail the check alike: what a
forged event claims cannot steer its handling. -/
def ClaimBlind (P : Primitives) (h : Handler S F) : Prop :=
  ∀ s e e', e.check P = false → e'.check P = false → h s e = h s e'

/-- What a handler blind to claims can tell apart in a stream: the events that pass the check, and
a hole where each one that fails it was. -/
def shape (P : Primitives) (es : List Event) : List (Option Event) :=
  es.map fun e => if e.check P then some e else none

/-- **Blindness over streams.** A handler is blind to claims exactly when any two streams that
differ only in their forged events, one for one, give the same final state and the same effects. -/
theorem claimBlind_iff (P : Primitives) (h : Handler S F) :
    ClaimBlind P h ↔ ∀ s es es', shape P es = shape P es' → run h s es = run h s es' := by
  constructor
  · intro hb s es
    induction es generalizing s with
    | nil =>
      intro es' hs
      cases es' with
      | nil => rfl
      | cons e' es' => simp [shape] at hs
    | cons e es ih =>
      intro es' hs
      cases es' with
      | nil => simp [shape] at hs
      | cons e' es' =>
        simp only [shape, List.map_cons, List.cons.injEq] at hs
        obtain ⟨h1, h2⟩ := hs
        have hstep : h s e = h s e' := by
          by_cases hc : e.check P <;> by_cases hc' : e'.check P <;> simp [hc, hc'] at h1
          · rw [h1]
          · exact hb s e e' (by simpa using hc) (by simpa using hc')
        rw [run_cons, run_cons, hstep, ih _ es' h2]
  · intro hr s e e' he he'
    have := hr s [e] [e'] (by simp [shape, he, he'])
    simp only [run_cons, run_nil, List.append_nil] at this
    exact Prod.ext (congrArg Prod.fst this) (congrArg Prod.snd this)

/-- Verify-first ingress is blind to claims, whatever its core. -/
theorem verifyFirst_claimBlind (P : Primitives) (core : S → Verified P → S × List F)
    (fail : S → S × List F) : ClaimBlind P (verifyFirst P core fail) := by
  intro s e e' he he'
  simp [verifyFirst, he, he']

/-- **The shape of every blind handler.** A handler blind to claims is verify-first ingress, with
its own handling of verified events as the core and its handling of any one forged event as the
response to failure. Nothing restricts the core. -/
theorem claimBlind_eq_verifyFirst {P : Primitives} {h : Handler S F} (hb : ClaimBlind P h)
    (e₀ : Event) (h₀ : e₀.check P = false) :
    h = verifyFirst P (fun s v => h s v.1) (fun s => h s e₀) := by
  funext s e
  unfold verifyFirst
  split
  · rfl
  · next hc => exact hb s e e₀ (by simpa using hc) h₀

/-- **Every effect takes a verified event.** Each effect of a run of verify-first ingress that
ignores failures is an effect of the core on an event of the stream that passed the check. -/
theorem verifyFirst_effect {P : Primitives} {core : S → Verified P → S × List F} (s : S)
    (es : List Event) {x : F} (hx : x ∈ (run (verifyFirst P core ignore) s es).2) :
    ∃ e ∈ es, ∃ (hv : e.Valid P) (s' : S), x ∈ (core s' ⟨e, hv⟩).2 := by
  induction es generalizing s with
  | nil => simp at hx
  | cons e es ih =>
    rw [run_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · by_cases hc : e.check P
      · exact ⟨e, by simp, (Event.check_iff P e).mp hc, s, by simpa [verifyFirst, hc] using hx⟩
      · simp [verifyFirst, hc, ignore] at hx
    · obtain ⟨e', he', hv, s', hx'⟩ := ih _ hx
      exact ⟨e', List.mem_cons_of_mem _ he', hv, s', hx'⟩

/-- **Forged events are inert.** Under verify-first ingress that ignores failures, the events that
fail the check can be cut from any stream without changing the final state or any effect. -/
theorem verifyFirst_filter (P : Primitives) (core : S → Verified P → S × List F) (s : S)
    (es : List Event) :
    run (verifyFirst P core ignore) s es =
      run (verifyFirst P core ignore) s (es.filter (·.check P)) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    by_cases hc : e.check P
    · rw [List.filter_cons_of_pos hc, run_cons, run_cons, ih]
    · have hf : verifyFirst P core ignore s e = (s, []) := by simp [verifyFirst, hc, ignore]
      rw [List.filter_cons_of_neg hc, run_cons, hf, ih]
      simp

/-! ## A relay pool: lookup before verification (RUSTSEC-2026-0232) -/

/-- The pool's database holds an event with this identifier. -/
def known (db : List Event) (id : EventId) : Bool := db.any (·.id == id)

/-- The pool's handling of an event taken as authentic: a new one is stored, and either way it goes
on to processing (admission policy, callbacks, propagation). -/
def ingest (db : List Event) (e : Event) : List Event × List Event :=
  if known db e.id then (db, [e]) else (db ++ [e], [e])

theorem ingest_effects (db : List Event) (e : Event) : (ingest db e).2 = [e] := by
  unfold ingest
  split <;> rfl

/-- The flawed order: a stored event with the claimed identifier lets verification be skipped. -/
def lookupFirst (P : Primitives) : Handler (List Event) Event :=
  fun db e => if known db e.id || e.check P then ingest db e else (db, [])

/-- The fixed order: verification first. -/
def checkedPool (P : Primitives) : Handler (List Event) Event :=
  verifyFirst P (fun db v => ingest db v.1) ignore

/-- **Lookup before verification admits forgery.** Once the database holds a valid event, an event
that claims its identifier with other fields, any key, content and signature, goes on to
processing, although it fails the check. -/
theorem lookupFirst_forgery {P : Primitives} (cf : P.CollisionFree) {db : List Event}
    {g f : Event} (hg : g ∈ db) (hgv : g.Valid P) (hid : f.id = g.id)
    (hne : f.toUnsigned ≠ g.toUnsigned) :
    (lookupFirst P db f).2 = [f] ∧ f.check P = false := by
  have hk : known db f.id = true := List.any_eq_true.mpr ⟨g, hg, by simp [hid]⟩
  refine ⟨by simp [lookupFirst, hk, ingest_effects], ?_⟩
  by_contra hc
  have hv : f.Valid P := (Event.check_iff P f).mp (by simpa using hc)
  exact hne (signed_fields_eq cf hv hgv hid)

/-- The hypotheses of `lookupFirst_forgery` can all hold: the attacker's key `c` stored a valid
event, and an event claiming its identifier, from the uncompromised key `a` whose owner composed
nothing, goes on to processing. The hash is collision free and the signature assumption holds. -/
theorem lookupFirst_forgery_instance :
    ∃ (P : Primitives) (A : Authorship P) (g f : Event),
      P.CollisionFree ∧ g.Valid P ∧ f.id = g.id ∧ f.toUnsigned ≠ g.toUnsigned ∧
      (lookupFirst P [g] f).2 = [f] ∧ ¬ A.compromised f.pubkey ∧ ¬ A.authored f.toUnsigned := by
  obtain ⟨h, hinj⟩ := exists_injective_hash
  let gu : Unsigned := ⟨"c", 0, 1, [], "mine"⟩
  let fu : Unsigned := ⟨"a", 0, 1, [], "forged"⟩
  let P : Primitives := ⟨h, fun k _ s => k == "c" && s == "sigC"⟩
  let A : Authorship P :=
    { authored := fun u => u.pubkey = "c"
      compromised := fun k => k = "c"
      sound := fun k d s hv hc => by
        simp only [P, Bool.and_eq_true, beq_iff_eq] at hv
        exact absurd hv.1 hc }
  let g : Event := { gu with id := h gu, sig := "sigC" }
  let f : Event := { fu with id := h gu, sig := "" }
  have hgv : g.Valid P := ⟨rfl, by simp [P, g, gu]⟩
  have hne : f.toUnsigned ≠ g.toUnsigned := by simp [f, g, fu, gu]
  refine ⟨P, A, g, f, hinj, hgv, rfl, hne,
    (lookupFirst_forgery (P := P) (f := f) hinj (List.mem_singleton_self g) hgv rfl hne).1, ?_, ?_⟩
  · simp [A, f, fu]
  · simp [A, f, fu]

/-- With verification first, every event the pool processes is an event of the stream that passed
the check. -/
theorem checkedPool_processed {P : Primitives} (db es : List Event) {x : Event}
    (hx : x ∈ (run (checkedPool P) db es).2) : x ∈ es ∧ x.Valid P := by
  obtain ⟨e, he, hv, s', hx'⟩ := verifyFirst_effect db es hx
  have hxe : x = e := by simpa [ingest_effects] using hx'
  exact hxe ▸ ⟨he, hv⟩

/-- **With verification first, processing sees only authentic events.** An event the pool
processes under an uncompromised key was composed by that key's owner, exactly as it reads. -/
theorem checkedPool_authentic {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    (db es : List Event) {x : Event} (hx : x ∈ (run (checkedPool P) db es).2)
    (hk : ¬ A.compromised x.pubkey) : A.authored x.toUnsigned :=
  authentic A cf (checkedPool_processed db es hx).2 hk

/-! ## A verification cache (RUSTSEC-2026-0232) -/

/-- A check with a cache of the keys of the identifiers that passed it. The identifier is
recomputed from the fields, and the signature is checked only when the identifier's key is not
cached. -/
def cachedCheck {K : Type} [DecidableEq K] (P : Primitives) (key : EventId → K) (cache : List K)
    (e : Event) : Bool :=
  e.id == P.hash e.toUnsigned && (cache.contains (key e.id) || P.verify e.pubkey e.id e.sig)

/-- The cache holds only keys of identifiers of valid events. -/
def CacheSound {K : Type} (P : Primitives) (key : EventId → K) (cache : List K) : Prop :=
  ∀ c ∈ cache, ∃ g : Event, g.Valid P ∧ key g.id = c

/-- The cached check accepts every event with a correct identifier whose key is cached, whatever
its signature. -/
theorem cachedCheck_of_cached {K : Type} [DecidableEq K] (P : Primitives) (key : EventId → K)
    {cache : List K} {e : Event} (hid : e.id = P.hash e.toUnsigned) (hk : key e.id ∈ cache) :
    cachedCheck P key cache e = true := by
  have h1 : (e.id == P.hash e.toUnsigned) = true := by simp [hid]
  simp [cachedCheck, h1, hk]

/-- **A cache keyed by the whole identifier is sound.** When the cache holds only identifiers of
valid events, an event the cached check accepts under an uncompromised key was composed by that
key's owner, exactly as it reads. -/
theorem cachedCheck_authentic {K : Type} [DecidableEq K] {P : Primitives} (A : Authorship P)
    (cf : P.CollisionFree) {key : EventId → K} (hkey : Function.Injective key) {cache : List K}
    (hc : CacheSound P key cache) {e : Event} (he : cachedCheck P key cache e = true)
    (hk : ¬ A.compromised e.pubkey) : A.authored e.toUnsigned := by
  simp only [cachedCheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem] at he
  obtain ⟨hid, hhit | hsig⟩ := he
  · obtain ⟨g, hgv, hg⟩ := hc _ hhit
    have hu : g.toUnsigned = e.toUnsigned := cf (hgv.1.symm.trans ((hkey hg).trans hid))
    have hgk : ¬ A.compromised g.pubkey := by
      rw [show g.pubkey = e.pubkey from congrArg Unsigned.pubkey hu]
      exact hk
    exact hu ▸ authentic A cf hgv hgk
  · exact authentic A cf ⟨hid, hsig⟩ hk

/-- **A key that is not the whole identifier admits forgery.** The cache holds only the key of a
valid event, yet when another identifier has that key, an event claiming the uncompromised key
`a`, whose owner composed nothing, passes with an empty signature. The hash is collision free and
the signature assumption holds. -/
theorem truncatedCache_forgery :
    ∃ (P : Primitives) (A : Authorship P) (key : EventId → Bool) (g e : Event),
      P.CollisionFree ∧ CacheSound P key [key g.id] ∧ cachedCheck P key [key g.id] e = true ∧
      ¬ A.compromised e.pubkey ∧ ¬ A.authored e.toUnsigned := by
  obtain ⟨h, hinj⟩ := exists_injective_hash
  let gu : Unsigned := ⟨"c", 0, 1, [], "mine"⟩
  let eu : Unsigned := ⟨"a", 0, 1, [], "forged"⟩
  let P : Primitives := ⟨h, fun k _ s => k == "c" && s == "sigC"⟩
  let A : Authorship P :=
    { authored := fun u => u.pubkey = "c"
      compromised := fun k => k = "c"
      sound := fun k d s hv hc => by
        simp only [P, Bool.and_eq_true, beq_iff_eq] at hv
        exact absurd hv.1 hc }
  let g : Event := { gu with id := h gu, sig := "sigC" }
  let e : Event := { eu with id := h eu, sig := "" }
  refine ⟨P, A, fun _ => true, g, e, hinj, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    exact ⟨g, ⟨rfl, by simp [P, g, gu]⟩, hc.symm⟩
  · exact cachedCheck_of_cached P _ rfl (by simp)
  · simp [A, e, eu]
  · simp [A, e, eu]

/-- **A hit vouches for the fields, not for the signature.** Even keyed by the whole identifier,
the cached check accepts a copy of a checked event whose signature does not verify. -/
theorem cachedCheck_unsigned :
    ∃ (P : Primitives) (g e : Event), P.CollisionFree ∧ CacheSound P id [g.id] ∧
      cachedCheck P id [g.id] e = true ∧ e.toUnsigned = g.toUnsigned ∧ ¬ e.Valid P := by
  obtain ⟨h, hinj⟩ := exists_injective_hash
  let gu : Unsigned := ⟨"a", 0, 1, [], "hello"⟩
  let P : Primitives := ⟨h, fun _ _ s => s == "good"⟩
  let g : Event := { gu with id := h gu, sig := "good" }
  let e : Event := { gu with id := h gu, sig := "bad" }
  refine ⟨P, g, e, hinj, ?_, cachedCheck_of_cached P id rfl (by simp [e, g]), rfl, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    exact ⟨g, ⟨rfl, by simp [P, g]⟩, hc.symm⟩
  · rintro ⟨-, hv⟩
    simp [P, e] at hv

/-! ## DM pairing (GHSA-h43v-27wg-5mf9) -/

/-- A pairing step for a DM from the key `k`: a key without a pending entry gets one, and a
challenge, while the table has room. -/
def pairStep (cap : ℕ) (pending : List PubKey) (k : PubKey) : List PubKey × List PubKey :=
  if pending.contains k || cap ≤ pending.length then (pending, []) else (pending ++ [k], [k])

/-- The flawed order: pairing from the claimed key, before the signature is checked. -/
def pairFirst (cap : ℕ) : Handler (List PubKey) PubKey := fun s e => pairStep cap s e.pubkey

/-- The fixed order: pairing only after the check. -/
def pairAfter (cap : ℕ) (P : Primitives) : Handler (List PubKey) PubKey :=
  verifyFirst P (fun s v => pairStep cap s v.1.pubkey) ignore

theorem pairStep_effects (cap : ℕ) (s : List PubKey) (k : PubKey) {x : PubKey}
    (hx : x ∈ (pairStep cap s k).2) : x = k := by
  unfold pairStep at hx
  split at hx <;> simp_all

theorem pairStep_pending (cap : ℕ) (s : List PubKey) (k : PubKey) {x : PubKey}
    (hx : x ∈ (pairStep cap s k).1) : x ∈ s ∨ x = k := by
  unfold pairStep at hx
  split at hx
  · exact Or.inl hx
  · simpa using hx

/-- **Pairing before the check.** A forged DM claiming the uncompromised key `a`, whose owner
composed nothing, makes a pending entry for `a` and a challenge sent to `a`. Pairing after the
check changes nothing. The hash is collision free and the signature assumption holds. -/
theorem pairFirst_forged :
    ∃ (P : Primitives) (A : Authorship P) (e : Event),
      P.CollisionFree ∧ e.check P = false ∧ ¬ A.compromised e.pubkey ∧
      (∀ u : Unsigned, A.authored u → u.pubkey ≠ e.pubkey) ∧
      pairFirst 1 [] e = ([e.pubkey], [e.pubkey]) ∧ pairAfter 1 P [] e = ([], []) := by
  obtain ⟨h, hinj⟩ := exists_injective_hash
  let eu : Unsigned := ⟨"a", 0, 4, [], "pair me"⟩
  let P : Primitives := ⟨h, fun k _ _ => k == "c"⟩
  let A : Authorship P :=
    { authored := fun u => u.pubkey = "c"
      compromised := fun k => k = "c"
      sound := fun k d s hv hc => by
        simp only [P, beq_iff_eq] at hv
        exact absurd hv hc }
  let e : Event := { eu with id := h eu, sig := "" }
  have hcheck : e.check P = false := by simp [Event.check, P, e, eu]
  refine ⟨P, A, e, hinj, hcheck, by simp [A, e, eu], ?_, ?_, ?_⟩
  · intro u hu
    simp only [A] at hu
    simp [hu, e, eu]
  · simp [pairFirst, pairStep]
  · simp [pairAfter, verifyFirst, hcheck, ignore]

/-- Every key pending after pairing after the check was pending before, or is the key of a DM of
the stream that passed the check. -/
theorem pairAfter_pending {cap : ℕ} {P : Primitives} (s : List PubKey) (es : List Event)
    {k : PubKey} (hk : k ∈ (run (pairAfter cap P) s es).1) :
    k ∈ s ∨ ∃ e ∈ es, e.Valid P ∧ e.pubkey = k := by
  induction es generalizing s with
  | nil => exact Or.inl hk
  | cons e es ih =>
    rw [run_cons] at hk
    rcases ih _ hk with h | ⟨e', he', hv, rfl⟩
    · by_cases hc : e.check P
      · have h' : k ∈ (pairStep cap s e.pubkey).1 := by simpa [pairAfter, verifyFirst, hc] using h
        rcases pairStep_pending cap s e.pubkey h' with h'' | rfl
        · exact Or.inl h''
        · exact Or.inr ⟨e, by simp, (Event.check_iff P e).mp hc, rfl⟩
      · exact Or.inl (by simpa [pairAfter, verifyFirst, hc, ignore] using h)
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hv, rfl⟩

/-- **Pairing after the check.** Every key with a pending entry and every key sent a challenge,
when uncompromised, is the key of an owner who composed a DM of the stream. -/
theorem pairAfter_authentic {cap : ℕ} {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    (es : List Event) {k : PubKey}
    (hk : k ∈ (run (pairAfter cap P) [] es).1 ∨ k ∈ (run (pairAfter cap P) [] es).2)
    (hc : ¬ A.compromised k) : ∃ e ∈ es, e.pubkey = k ∧ A.authored e.toUnsigned := by
  have hfrom : ∃ e ∈ es, e.Valid P ∧ e.pubkey = k := by
    rcases hk with hk | hk
    · simpa using pairAfter_pending [] es hk
    · obtain ⟨e, he, hv, s', hx⟩ := verifyFirst_effect [] es hk
      exact ⟨e, he, hv, (pairStep_effects cap s' e.pubkey hx).symm⟩
  obtain ⟨e, he, hv, rfl⟩ := hfrom
  exact ⟨e, he, rfl, authentic A cf hv hc⟩

/-- **What the order does not give.** Pairing after the check does not bound the table: valid DMs
from the fresh keys `x` and `y` fill a table of two, and `z` gets no challenge. -/
theorem pairAfter_fresh_keys :
    let P : Primitives := ⟨fun u => u.pubkey, fun _ _ _ => true⟩
    let dm (k : PubKey) : Event := ⟨⟨k, 0, 4, [], ""⟩, k, ""⟩
    run (pairAfter 2 P) [] [dm "x", dm "y", dm "z"] = (["x", "y"], ["x", "y"]) := by
  decide

/-- Pairing after the check is blind to claims. -/
theorem pairAfter_claimBlind (cap : ℕ) (P : Primitives) : ClaimBlind P (pairAfter cap P) :=
  verifyFirst_claimBlind P _ _

/-- The pool with verification first is blind to claims. -/
theorem checkedPool_claimBlind (P : Primitives) : ClaimBlind P (checkedPool P) :=
  verifyFirst_claimBlind P _ _

/-! ## Our models follow the order -/

/-- The mailbox client keeps nothing that fails the check. -/
theorem accept_forged {P : Primitives} {opener : Opener} {reg : Registry} {me : PubKey}
    {e : Event} (h : e.check P = false) : accept P opener reg me e = none := by
  simp [accept, h]

/-- The gateway brings nothing that fails the check into claw-mail. -/
theorem bridge_forged {g : Gateway} {s : ClawMail.State} {e : Event} (h : e.check g.P = false) :
    g.bridge s e = s := by
  simp [Gateway.bridge, Gateway.keep, accept_forged h]

/-- The relay stores and sends nothing of a published event that fails the check. Its one reply
is the refusal to the connection that sent it. -/
theorem publish_forged (cfg : Config) {P : Primitives} (now : Int) (r : Relay) (c : ConnId)
    {e : Event} (h : e.check P = false) :
    r.step cfg P now (.publish c e) = (r, [(c, .ok e.id false)]) := by
  simp only [Relay.step]
  split
  · rfl
  · simp [Relay.refused, h]

end Mettapedia.Protocols.Nostr.Ingress
