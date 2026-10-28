import Mettapedia.Protocols.Nostr.Filter

/-!
# A gated Nostr relay (NIP-01, NIP-09, NIP-42)

The relay of a closed agent-mail fabric, as NuNet's `gated_relay.py` implements
it. Each connection is sent a fresh challenge, and nothing is served until the
connection signs in (NIP-42) with a key on the allowlist. A signed-in key may
publish only events it signed, and may read only events it wrote or that name
it in a `p` tag. The allowlist can change at any time, and a removed key loses
access at its next message. A deletion request (NIP-09) removes only its
author's events. Ephemeral events are relayed and not stored.

The theorems:
- `served`: an event goes to a connection only while the connection is signed
  in with a key on the current allowlist, and only if that key wrote the event
  or a `p` tag names it. This holds for stored answers and live delivery alike.
- `delivered_live`: every event the relay newly accepts reaches each open subscription
  that matches it on a connection allowed to read it.
- `step_storeValid`: the store holds only well-formed, signed, storable events,
  each identifier once.
- `added_by_author`: an event enters the store only when its author, signed in,
  publishes it.
- `removed_by_author`: an event leaves the store only through a deletion request
  by its author that names it.
- `signin_sound`: a connection is signed in as a key only after an AUTH event of
  that key names the connection's challenge and an address this relay accepts.
- `signin_authenticates`: hence, when the key's owner signs AUTH events only for
  challenges it received, the owner received this connection's challenge from
  one of this relay's addresses. With fresh challenges, and addresses that reach
  no other relay, that connection is the owner's own. If the relay's address
  list is empty, a sign-in can be forwarded from another relay
  (`forwarded_signin`).

Not modelled: message sizes and the counts of subscriptions and filters (those
checks only refuse), address normalization, the information document and the
transport. Each step here is atomic. The real handler yields between the
events of an answer, so an event published meanwhile can reach a subscription
twice, live and in the answer, and readers deduplicate by identifier.
-/

namespace Mettapedia.Protocols.Nostr

/-- The key may read the event: it wrote it, or a `p` tag names it. -/
def readableBy (e : Event) (k : PubKey) : Bool := e.pubkey == k || (tagValues e.tags "p").contains k

/-- A connection's identity at the relay. -/
abbrev ConnId := Nat
/-- A subscription's name, chosen by the client. -/
abbrev SubId := String

/-- Relay settings. -/
structure Config where
  /-- The addresses an AUTH event may name. An empty list accepts any. -/
  relayUrls : List String
  /-- How far an event's time may lie in the future, in seconds. -/
  rejectFuture : Int := 1800
  /-- How far an AUTH event's time may be off, in seconds. -/
  authWindow : Int := 600
  /-- The most events one filter returns. -/
  maxLimit : Nat := 5000

/-- A connection: its challenge, the key it signed in with, its subscriptions. -/
structure Conn where
  id : ConnId
  challenge : String
  key : Option PubKey
  subs : List (SubId × List Filter)

/-- The relay: the allowlist, the stored events and the open connections. -/
structure Relay where
  allow : List PubKey
  store : List Event
  conns : List Conn

/-- What a relay receives: client messages, connection events, and allowlist reloads. -/
inductive Input
  | connect (c : ConnId) (challenge : String)
  | auth (c : ConnId) (e : Event)
  | publish (c : ConnId) (e : Event)
  | req (c : ConnId) (sub : SubId) (filters : List Filter)
  | close (c : ConnId) (sub : SubId)
  | disconnect (c : ConnId)
  | reload (allow : List PubKey)

/-- What a relay sends to a connection. -/
inductive Reply
  | challenge (s : String)
  | ok (id : EventId) (accepted : Bool)
  | event (sub : SubId) (e : Event)
  | eose (sub : SubId)
  | closed (sub : SubId)

/-- Each identifier once, keeping the first occurrence. -/
def dedupById : List EventId → List Event → List Event
  | _, [] => []
  | seen, e :: es => if seen.contains e.id then dedupById seen es else e :: dedupById (e.id :: seen) es

theorem mem_of_mem_dedupById : ∀ {seen : List EventId} {l : List Event} {e : Event},
    e ∈ dedupById seen l → e ∈ l
  | _, [], _, h => by simp [dedupById] at h
  | seen, x :: xs, e, h => by
    unfold dedupById at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_of_mem_dedupById h)
    · rcases List.mem_cons.mp h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (mem_of_mem_dedupById h)

/-- Remove the author's events among the named ones. -/
def deleteBy (store : List Event) (ids : List EventId) (author : PubKey) : List Event :=
  store.filter fun e => !(ids.contains e.id && e.pubkey == author)

namespace Relay

/-- A relay with no events and no connections. -/
def empty (allow : List PubKey) : Relay := ⟨allow, [], []⟩

/-- The connection with an identity. -/
def conn? (r : Relay) (c : ConnId) : Option Conn := r.conns.find? (·.id == c)

/-- A connection's key while that key is on the allowlist. -/
def keyOf (r : Relay) (conn : Conn) : Option PubKey :=
  match conn.key with
  | some k => if r.allow.contains k then some k else none
  | none => none

/-- The key a connection is signed in with, if it is still allowlisted. -/
def signedIn (r : Relay) (c : ConnId) : Option PubKey := (r.conn? c).bind r.keyOf

/-- Change a connection's record. -/
def update (r : Relay) (c : ConnId) (f : Conn → Conn) : Relay :=
  { r with conns := r.conns.map fun x => if x.id = c then f x else x }

/-- Live delivery: the event to each matching subscription on every connection
whose signed-in key may read it. -/
def broadcast (r : Relay) (e : Event) : List (ConnId × Reply) :=
  r.conns.flatMap fun conn =>
    match r.keyOf conn with
    | some k =>
      if readableBy e k then
        (conn.subs.filter fun s => acceptsAny s.2 e).map fun s => (conn.id, .event s.1 e)
      else []
    | none => []

/-- The store holds an event with this identifier. -/
def has (r : Relay) (id : EventId) : Bool := r.store.any (·.id == id)

/-- The stored answer to a subscription: each filter's selection among the
events the key may read, in turn, each event once. -/
def answer (cfg : Config) (r : Relay) (me : PubKey) (fs : List Filter) : List Event :=
  dedupById [] (fs.flatMap fun f => f.select cfg.maxLimit (readableBy · me) r.store)

/-- An AUTH event signs a connection in: it is well formed and signed, of the
AUTH kind, names the connection's challenge, is recent, names an address of this
relay (when the relay lists any), and its key is allowlisted. -/
def authOk (cfg : Config) (P : Primitives) (now : Int) (r : Relay) (conn : Conn) (a : Event) : Bool :=
  a.check P && a.kind == kindAuth && (tagValues a.tags "challenge").contains conn.challenge &&
    decide (now - cfg.authWindow ≤ a.createdAt ∧ a.createdAt ≤ now + cfg.authWindow) &&
    (cfg.relayUrls.isEmpty || (tagValues a.tags "relay").any cfg.relayUrls.contains) &&
    r.allow.contains a.pubkey

/-- A published event is refused when it is malformed or badly signed, not the
publisher's own, an AUTH event, or too far in the future. -/
def refused (cfg : Config) (P : Primitives) (now : Int) (me : PubKey) (e : Event) : Bool :=
  !e.check P || e.pubkey != me || e.kind == kindAuth || decide (now + cfg.rejectFuture < e.createdAt)

/-- One input, with the replies it sends. -/
def step (cfg : Config) (P : Primitives) (now : Int) (r : Relay) :
    Input → Relay × List (ConnId × Reply)
  | .connect c ch => ({ r with conns := r.conns.filter (·.id ≠ c) ++ [⟨c, ch, none, []⟩] },
      [(c, .challenge ch)])
  | .auth c a =>
    match r.conn? c with
    | none => (r, [])
    | some conn =>
      if r.authOk cfg P now conn a then
        (r.update c fun x => { x with key := some a.pubkey }, [(c, .ok a.id true)])
      else (r, [(c, .ok a.id false)])
  | .publish c e =>
    match r.signedIn c with
    | none => (r, [(c, .ok e.id false)])
    | some me =>
      if refused cfg P now me e then (r, [(c, .ok e.id false)])
      else if ephemeral e.kind then (r, r.broadcast e ++ [(c, .ok e.id true)])
      else if r.has e.id then (r, [(c, .ok e.id true)])
      else
        let kept := if e.kind == kindDeletion then deleteBy r.store (tagValues e.tags "e") me else r.store
        let r' : Relay := { r with store := kept ++ [e] }
        (r', (c, .ok e.id true) :: r'.broadcast e)
  | .req c sub fs =>
    match r.signedIn c with
    | none => (r, [(c, .closed sub)])
    | some me =>
      (r.update c fun x => { x with subs := x.subs.filter (·.1 ≠ sub) ++ [(sub, fs)] },
        (r.answer cfg me fs).map (fun e => (c, .event sub e)) ++ [(c, .eose sub)])
  | .close c sub => (r.update c fun x => { x with subs := x.subs.filter (·.1 ≠ sub) }, [])
  | .disconnect c => ({ r with conns := r.conns.filter (·.id ≠ c) }, [])
  | .reload allow => ({ r with allow := allow }, [])

/-- Timed inputs, in order. -/
def run (cfg : Config) (P : Primitives) : Relay → List (Int × Input) → Relay
  | r, [] => r
  | r, (now, i) :: rest => run cfg P (r.step cfg P now i).1 rest

/-! ## Who is served -/

theorem conn?_some {r : Relay} {c : ConnId} {conn : Conn} (h : r.conn? c = some conn) :
    conn ∈ r.conns ∧ conn.id = c := by
  unfold conn? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem signedIn_some {r : Relay} {c : ConnId} {k : PubKey} (h : r.signedIn c = some k) :
    ∃ conn ∈ r.conns, conn.id = c ∧ r.keyOf conn = some k := by
  unfold signedIn at h
  obtain ⟨conn, hc, hk⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨mem, hid⟩ := conn?_some hc
  exact ⟨conn, mem, hid, hk⟩

theorem keyOf_allowed {r : Relay} {conn : Conn} {k : PubKey} (h : r.keyOf conn = some k) :
    k ∈ r.allow ∧ conn.key = some k := by
  unfold keyOf at h
  split at h
  · next k' hk' =>
    split at h
    · next hc => cases h; exact ⟨by simpa using hc, hk'⟩
    · cases h
  · cases h

theorem mem_broadcast {r : Relay} {e e' : Event} {c : ConnId} {sub : SubId}
    (h : (c, Reply.event sub e') ∈ r.broadcast e) :
    e' = e ∧ ∃ conn ∈ r.conns, conn.id = c ∧ ∃ k, r.keyOf conn = some k ∧ readableBy e k = true ∧
      ∃ fs, (sub, fs) ∈ conn.subs ∧ acceptsAny fs e = true := by
  unfold broadcast at h
  obtain ⟨conn, mem, h⟩ := List.mem_flatMap.mp h
  split at h
  · next k hk =>
    split at h
    · next hr =>
      obtain ⟨s, hs, heq⟩ := List.mem_map.mp h
      simp only [Prod.mk.injEq, Reply.event.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      obtain ⟨hs, hm⟩ := List.mem_filter.mp hs
      exact ⟨rfl, conn, mem, rfl, k, hk, hr, s.2, hs, hm⟩
    · simp at h
  · simp at h

/-- An event goes to a connection only while it is signed in with an allowlisted
key, and only if that key wrote the event or a `p` tag names it. -/
theorem served {cfg : Config} {P : Primitives} {now : Int} {r : Relay} {i : Input} {c : ConnId}
    {sub : SubId} {e : Event} (h : (c, Reply.event sub e) ∈ (r.step cfg P now i).2) :
    ∃ conn ∈ r.conns, conn.id = c ∧ ∃ k, r.keyOf conn = some k ∧ readableBy e k = true := by
  cases i with
  | connect c' ch => simp [step] at h
  | auth c' a =>
    simp only [step] at h
    split at h
    · simp at h
    · split at h <;> simp at h
  | publish c' d =>
    simp only [step] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rcases List.mem_append.mp h with h | h
          · obtain ⟨rfl, conn, mem, hid, k, hk, hr, -⟩ := mem_broadcast h
            exact ⟨conn, mem, hid, k, hk, hr⟩
          · simp at h
        · split at h
          · simp at h
          · rcases List.mem_cons.mp h with h | h
            · simp at h
            · obtain ⟨rfl, conn, mem, hid, k, hk, hr, -⟩ := mem_broadcast h
              exact ⟨conn, mem, hid, k, hk, hr⟩
  | req c' sub' fs =>
    simp only [step] at h
    split at h
    · simp at h
    · next me hme =>
      rcases List.mem_append.mp h with h | h
      · obtain ⟨e', he', heq⟩ := List.mem_map.mp h
        simp only [Prod.mk.injEq, Reply.event.injEq] at heq
        obtain ⟨rfl, -, rfl⟩ := heq
        obtain ⟨conn, mem, hid, hk⟩ := signedIn_some hme
        obtain ⟨f, -, hf⟩ := List.mem_flatMap.mp (mem_of_mem_dedupById he')
        exact ⟨conn, mem, hid, me, hk, (Filter.mem_select hf).2.1⟩
      · simp at h
  | close c' sub' => simp [step] at h
  | disconnect c' => simp [step] at h
  | reload allow => simp [step] at h

/-- Revocation is immediate: no event goes to a key that is off the allowlist. -/
theorem served_allowed {cfg : Config} {P : Primitives} {now : Int} {r : Relay} {i : Input}
    {c : ConnId} {sub : SubId} {e : Event} (h : (c, Reply.event sub e) ∈ (r.step cfg P now i).2) :
    ∃ conn ∈ r.conns, conn.id = c ∧ ∃ k ∈ r.allow, conn.key = some k := by
  obtain ⟨conn, mem, hid, k, hk, -⟩ := served h
  exact ⟨conn, mem, hid, k, keyOf_allowed hk⟩

/-- Every event the relay accepts reaches each matching subscription on every
connection allowed to read it. -/
theorem delivered_live {cfg : Config} {P : Primitives} {now : Int} {r : Relay} {c : ConnId}
    {e : Event} {me : PubKey} (hme : r.signedIn c = some me) (hok : refused cfg P now me e = false)
    (hnew : ephemeral e.kind = true ∨ r.has e.id = false)
    {conn : Conn} (mem : conn ∈ r.conns) {k : PubKey} (hk : r.keyOf conn = some k)
    (hr : readableBy e k = true) {sub : SubId} {fs : List Filter} (hs : (sub, fs) ∈ conn.subs)
    (hm : acceptsAny fs e = true) :
    (conn.id, Reply.event sub e) ∈ (r.step cfg P now (.publish c e)).2 := by
  have hb : ∀ r' : Relay, r'.conns = r.conns → r'.allow = r.allow →
      (conn.id, Reply.event sub e) ∈ r'.broadcast e := by
    intro r' hc ha
    unfold broadcast
    refine List.mem_flatMap.mpr ⟨conn, hc ▸ mem, ?_⟩
    have : r'.keyOf conn = some k := by unfold keyOf at hk ⊢; rw [ha]; exact hk
    rw [this]
    simp only [hr, if_true]
    exact List.mem_map.mpr ⟨(sub, fs), List.mem_filter.mpr ⟨hs, hm⟩, rfl⟩
  simp only [step, hme, hok]
  by_cases he : ephemeral e.kind = true
  · simp only [he, if_true]
    exact List.mem_append_left _ (hb r rfl rfl)
  · have hh : r.has e.id = false := hnew.resolve_left he
    simp only [he, hh]
    exact List.mem_cons_of_mem _ (hb _ rfl rfl)

/-! ## What is stored -/

/-- The store invariant: well-formed, signed, storable events, each identifier once. -/
def StoreValid (P : Primitives) (r : Relay) : Prop :=
  (∀ e ∈ r.store, e.Valid P ∧ ephemeral e.kind = false ∧ e.kind ≠ kindAuth) ∧
    (r.store.map (·.id)).Nodup

theorem empty_storeValid (P : Primitives) (allow : List PubKey) : (empty allow).StoreValid P :=
  ⟨by simp [empty], by simp [empty]⟩

theorem has_false {r : Relay} {id : EventId} (h : r.has id = false) : id ∉ r.store.map (·.id) := by
  simpa [has] using h

theorem step_storeValid {cfg : Config} {P : Primitives} {now : Int} {r : Relay} (hr : r.StoreValid P)
    (i : Input) : (r.step cfg P now i).1.StoreValid P := by
  cases i with
  | publish c e =>
    simp only [step]
    split
    · exact hr
    · next me hme =>
      split
      · exact hr
      · next hok =>
        have hok : refused cfg P now me e = false := Bool.eq_false_iff.mpr hok
        simp only [refused, Bool.or_eq_false_iff] at hok
        split
        · exact hr
        · next heph =>
          have heph : ephemeral e.kind = false := Bool.eq_false_iff.mpr heph
          split
          · exact hr
          · next hhas =>
            have hhas : r.has e.id = false := Bool.eq_false_iff.mpr hhas
            have hv : e.Valid P := (Event.check_iff P e).mp (by simpa using hok.1.1.1)
            have hka : e.kind ≠ kindAuth := by simpa using hok.1.2
            have sub : (if e.kind == kindDeletion then deleteBy r.store (tagValues e.tags "e") me
                else r.store).Sublist r.store := by
              split
              · exact List.filter_sublist
              · exact List.Sublist.refl _
            refine ⟨fun x hx => ?_, ?_⟩
            · rcases List.mem_append.mp hx with hx | hx
              · exact hr.1 x (sub.subset hx)
              · simp only [List.mem_singleton] at hx
                subst hx
                exact ⟨hv, heph, hka⟩
            · rw [List.map_append, List.map_singleton]
              exact (hr.2.sublist (sub.map _)).append (List.nodup_singleton _)
                (List.disjoint_singleton.mpr fun hmem => has_false hhas ((sub.map _).subset hmem))
  | connect c ch => exact hr
  | auth c a =>
    simp only [step]
    split
    · exact hr
    · split <;> exact hr
  | req c sub fs =>
    simp only [step]
    split
    · exact hr
    · exact hr
  | close c sub => exact hr
  | disconnect c => exact hr
  | reload allow => exact hr

/-- An event enters the store only when its author, signed in, publishes it. -/
theorem added_by_author {cfg : Config} {P : Primitives} {now : Int} {r : Relay} {i : Input}
    {e : Event} (h : e ∈ (r.step cfg P now i).1.store) (hn : e ∉ r.store) :
    ∃ c, i = .publish c e ∧ r.signedIn c = some e.pubkey := by
  cases i with
  | publish c d =>
    simp only [step] at h
    split at h
    · exact absurd h hn
    · next me hme =>
      split at h
      · exact absurd h hn
      · next hok =>
        have hok : refused cfg P now me d = false := Bool.eq_false_iff.mpr hok
        simp only [refused, Bool.or_eq_false_iff] at hok
        split at h
        · exact absurd h hn
        · split at h
          · exact absurd h hn
          · rcases List.mem_append.mp h with h | h
            · exfalso
              apply hn
              split at h
              · exact List.mem_of_mem_filter h
              · exact h
            · simp only [List.mem_singleton] at h
              subst h
              have : e.pubkey = me := by simpa using hok.1.1.2
              exact ⟨c, rfl, this ▸ hme⟩
  | connect c ch => exact absurd h hn
  | auth c a =>
    simp only [step] at h
    split at h
    · exact absurd h hn
    · split at h <;> exact absurd h hn
  | req c sub fs =>
    simp only [step] at h
    split at h <;> exact absurd h hn
  | close c sub => exact absurd h hn
  | disconnect c => exact absurd h hn
  | reload allow => exact absurd h hn

/-- An event leaves the store only through a deletion request of its author that
names it. -/
theorem removed_by_author {cfg : Config} {P : Primitives} {now : Int} {r : Relay} {i : Input}
    {e : Event} (h : e ∈ r.store) (hn : e ∉ (r.step cfg P now i).1.store) :
    ∃ c d, i = .publish c d ∧ d.kind = kindDeletion ∧ d.Valid P ∧ r.signedIn c = some d.pubkey ∧
      d.pubkey = e.pubkey ∧ e.id ∈ tagValues d.tags "e" := by
  cases i with
  | publish c d =>
    simp only [step] at hn
    split at hn
    · exact absurd h hn
    · next me hme =>
      split at hn
      · exact absurd h hn
      · next hok =>
        have hok : refused cfg P now me d = false := Bool.eq_false_iff.mpr hok
        simp only [refused, Bool.or_eq_false_iff] at hok
        have hpk : d.pubkey = me := by simpa using hok.1.1.2
        split at hn
        · exact absurd h hn
        · split at hn
          · exact absurd h hn
          · have hk : ¬ e ∈ (if d.kind == kindDeletion then deleteBy r.store (tagValues d.tags "e") me
                else r.store) := fun hk => hn (List.mem_append_left _ hk)
            split at hk
            · next hdel =>
              simp only [deleteBy, List.mem_filter, h, true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
                Bool.and_eq_false_iff, not_or, Bool.not_eq_false, List.contains_iff_mem,
                beq_iff_eq] at hk
              refine ⟨c, d, rfl, by simpa using hdel, (Event.check_iff P d).mp (by simpa using hok.1.1.1),
                hpk ▸ hme, hpk.trans hk.2.symm, ?_⟩
              simpa using hk.1
            · exact absurd h hk
  | connect c ch => exact absurd h hn
  | auth c a =>
    simp only [step] at hn
    split at hn
    · exact absurd h hn
    · split at hn <;> exact absurd h hn
  | req c sub fs =>
    simp only [step] at hn
    split at hn <;> exact absurd h hn
  | close c sub => exact absurd h hn
  | disconnect c => exact absurd h hn
  | reload allow => exact absurd h hn

/-! ## Signing in -/

/-- Connection identities are unique. -/
def ConnsValid (r : Relay) : Prop := (r.conns.map (·.id)).Nodup

theorem update_ids (r : Relay) (c : ConnId) {f : Conn → Conn} (hf : ∀ x, (f x).id = x.id) :
    (r.update c f).conns.map (·.id) = r.conns.map (·.id) := by
  simp only [update, List.map_map]
  congr 1
  funext x
  simp only [Function.comp_apply]
  split <;> simp [hf]

theorem update_nodup {r : Relay} {c : ConnId} {f : Conn → Conn} (hr : (r.conns.map (·.id)).Nodup)
    (hf : ∀ x, (f x).id = x.id) : ((r.update c f).conns.map (·.id)).Nodup := by
  rw [update_ids r c hf]; exact hr

theorem step_connsValid {cfg : Config} {P : Primitives} {now : Int} {r : Relay} (hr : r.ConnsValid)
    (i : Input) : (r.step cfg P now i).1.ConnsValid := by
  unfold ConnsValid at *
  cases i with
  | connect c ch =>
    simp only [step, List.map_append, List.map_cons, List.map_nil]
    refine (hr.sublist (List.filter_sublist.map _)).append (List.nodup_singleton _) ?_
    refine List.disjoint_singleton.mpr fun hmem => ?_
    obtain ⟨x, hx, hid⟩ := List.mem_map.mp hmem
    simp only [List.mem_filter, decide_eq_true_eq] at hx
    exact hx.2 hid
  | auth c a =>
    simp only [step]
    split
    · exact hr
    · split
      · exact update_nodup hr (fun _ => rfl)
      · exact hr
  | publish c e =>
    simp only [step]
    split
    · exact hr
    · split
      · exact hr
      · split
        · exact hr
        · split
          · exact hr
          · exact hr
  | req c sub fs =>
    simp only [step]
    split
    · exact hr
    · exact update_nodup hr (fun _ => rfl)
  | close c sub => exact update_nodup hr (fun _ => rfl)
  | disconnect c => exact hr.sublist (List.filter_sublist.map _)
  | reload allow => exact hr

/-- An AUTH event that signs in a connection with this challenge as this key. -/
def Authorizes (cfg : Config) (P : Primitives) (a : Event) (challenge : String) (k : PubKey) : Prop :=
  a.Valid P ∧ a.kind = kindAuth ∧ a.pubkey = k ∧ challenge ∈ tagValues a.tags "challenge" ∧
    (cfg.relayUrls = [] ∨ ∃ u ∈ tagValues a.tags "relay", u ∈ cfg.relayUrls)

theorem authOk_authorizes {cfg : Config} {P : Primitives} {now : Int} {r : Relay} {conn : Conn}
    {a : Event} (h : r.authOk cfg P now conn a = true) : Authorizes cfg P a conn.challenge a.pubkey := by
  simp only [authOk, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, Bool.or_eq_true,
    List.isEmpty_iff, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hc, hk⟩, hch⟩, -⟩, hurl⟩, -⟩ := h
  refine ⟨(Event.check_iff P a).mp hc, hk, rfl, hch, ?_⟩
  rcases hurl with h | ⟨u, hu, hin⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, hu, by simpa using hin⟩

/-- A key on a connection after a step was there before, or the step's AUTH
event, accepted against that connection's challenge, put it there. -/
theorem key_established {cfg : Config} {P : Primitives} {now : Int} {r : Relay} (hr : r.ConnsValid)
    {i : Input} {conn' : Conn} (h : conn' ∈ (r.step cfg P now i).1.conns) {k : PubKey}
    (hk : conn'.key = some k) :
    ∃ conn ∈ r.conns, conn.id = conn'.id ∧ conn.challenge = conn'.challenge ∧
      (conn.key = some k ∨ ∃ a, i = .auth conn.id a ∧ r.authOk cfg P now conn a = true ∧ a.pubkey = k) := by
  have unchanged : conn' ∈ r.conns → ∃ conn ∈ r.conns, conn.id = conn'.id ∧
      conn.challenge = conn'.challenge ∧
      (conn.key = some k ∨ ∃ a, i = .auth conn.id a ∧ r.authOk cfg P now conn a = true ∧ a.pubkey = k) :=
    fun hm => ⟨conn', hm, rfl, rfl, Or.inl hk⟩
  have viaUpdate : ∀ (c : ConnId) (f : Conn → Conn), conn' ∈ (r.update c f).conns →
      (∀ x, (f x).id = x.id ∧ (f x).challenge = x.challenge ∧ (f x).key = x.key) →
      ∃ conn ∈ r.conns, conn.id = conn'.id ∧
      conn.challenge = conn'.challenge ∧
      (conn.key = some k ∨ ∃ a, i = .auth conn.id a ∧ r.authOk cfg P now conn a = true ∧ a.pubkey = k) := by
    intro c f hm hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    by_cases hid : x.id = c
    · simp only [hid, if_true] at hk ⊢
      exact ⟨x, hx, (hf x).1.symm, (hf x).2.1.symm, Or.inl (by rw [← (hf x).2.2]; exact hk)⟩
    · simp only [hid, if_false] at hk ⊢
      exact ⟨x, hx, rfl, rfl, Or.inl hk⟩
  cases i with
  | connect c ch =>
    simp only [step] at h
    rcases List.mem_append.mp h with h | h
    · exact unchanged (List.mem_of_mem_filter h)
    · simp only [List.mem_singleton] at h
      subst h
      cases hk
  | auth c a =>
    simp only [step] at h
    split at h
    · exact unchanged h
    · next conn hconn =>
      split at h
      · next hok =>
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
        by_cases hid : x.id = c
        · have hcm := conn?_some hconn
          have hxc : x = conn := List.inj_on_of_nodup_map hr hx hcm.1 (hid.trans hcm.2.symm)
          subst hxc
          have hk' : a.pubkey = k := by simpa [hid] using hk
          exact ⟨x, hx, by simp [hid], by simp [hid], Or.inr ⟨a, by rw [hid], hok, hk'⟩⟩
        · simp only [hid, if_false] at hk ⊢
          exact ⟨x, hx, rfl, rfl, Or.inl hk⟩
      · exact unchanged h
  | publish c e =>
    simp only [step] at h
    split at h
    · exact unchanged h
    · split at h
      · exact unchanged h
      · split at h
        · exact unchanged h
        · split at h
          · exact unchanged h
          · exact unchanged h
  | req c sub fs =>
    simp only [step] at h
    split at h
    · exact unchanged h
    · exact viaUpdate c _ h (fun _ => ⟨rfl, rfl, rfl⟩)
  | close c sub =>
    simp only [step] at h
    exact viaUpdate c _ h (fun _ => ⟨rfl, rfl, rfl⟩)
  | disconnect c => exact unchanged (List.mem_of_mem_filter h)
  | reload allow => exact unchanged h

theorem run_signin {cfg : Config} {P : Primitives} :
    ∀ (inputs : List (Int × Input)) (r : Relay) (H : List (Int × Input)), r.ConnsValid →
      (∀ conn ∈ r.conns, ∀ k, conn.key = some k →
        ∃ now a, (now, Input.auth conn.id a) ∈ H ∧ Authorizes cfg P a conn.challenge k) →
      ∀ conn ∈ (run cfg P r inputs).conns, ∀ k, conn.key = some k →
        ∃ now a, (now, Input.auth conn.id a) ∈ H ++ inputs ∧ Authorizes cfg P a conn.challenge k
  | [], r, H, _, hH => by simpa [run] using hH
  | (now, i) :: rest, r, H, hv, hH => by
    have := run_signin (cfg := cfg) (P := P) rest (r.step cfg P now i).1 (H ++ [(now, i)])
      (step_connsValid hv i) ?_
    · simpa [run, List.append_assoc] using this
    intro conn' hc' k hk
    obtain ⟨conn, hc, hid, hch, hkey⟩ := key_established hv hc' hk
    rcases hkey with hkey | ⟨a, rfl, hok, rfl⟩
    · obtain ⟨n, a, ha, hauth⟩ := hH conn hc k hkey
      exact ⟨n, a, List.mem_append_left _ (hid ▸ ha), hch ▸ hauth⟩
    · exact ⟨now, a, by simp [hid], hch ▸ authOk_authorizes hok⟩

/-- A connection is signed in as a key only after an AUTH event of that key named
the connection's challenge and, when the relay lists addresses, one of them. -/
theorem signin_sound {cfg : Config} {P : Primitives} {allow : List PubKey}
    {inputs : List (Int × Input)} {conn : Conn} (h : conn ∈ (run cfg P (empty allow) inputs).conns)
    {k : PubKey} (hk : conn.key = some k) :
    ∃ now a, (now, Input.auth conn.id a) ∈ inputs ∧ Authorizes cfg P a conn.challenge k := by
  simpa using run_signin inputs (empty allow) [] (by simp [ConnsValid, empty]) (by simp [empty]) conn h k hk

/-- Honest owners sign in only where they were challenged: each challenge an
owner's AUTH event names was received from each address the event names.
`received k url ch` says that the owner of `k`, connected to the relay at `url`,
received the challenge `ch` there. -/
def HonestSignIn {P : Primitives} (A : Authorship P) (received : PubKey → String → String → Prop) :
    Prop :=
  ∀ u, A.authored u → u.kind = kindAuth →
    ∀ ch ∈ tagValues u.tags "challenge", ∀ url ∈ tagValues u.tags "relay", received u.pubkey url ch

/-- Sign-in authenticates: a connection signed in as an uncompromised key carries
a challenge that the key's owner received from one of this relay's addresses. -/
theorem signin_authenticates {cfg : Config} {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    {received : PubKey → String → String → Prop} (honest : HonestSignIn A received)
    (hurls : cfg.relayUrls ≠ []) {allow : List PubKey} {inputs : List (Int × Input)} {conn : Conn}
    (h : conn ∈ (run cfg P (empty allow) inputs).conns) {k : PubKey} (hk : conn.key = some k)
    (hc : ¬ A.compromised k) : ∃ url ∈ cfg.relayUrls, received k url conn.challenge := by
  obtain ⟨-, a, -, hv, hkind, rfl, hch, hurl⟩ := signin_sound h hk
  have hauth := authentic A cf hv hc
  obtain ⟨url, hu, hin⟩ := hurl.resolve_left hurls
  exact ⟨url, hin, honest _ hauth hkind _ hch _ hu⟩

/-- Without an address list a sign-in can be forwarded. An honest owner that only
ever received the challenge from another relay signs it in there, and its AUTH
event signs in a connection here that the owner never opened. Listing this
relay's address refuses the same event. -/
theorem forwarded_signin : ∃ (P : Primitives) (A : Authorship P)
    (received : PubKey → String → String → Prop) (a : Event) (r : Relay),
    P.CollisionFree ∧ HonestSignIn A received ∧ ¬ A.compromised a.pubkey ∧
      (∀ url ch, received a.pubkey url ch → url = "wss://elsewhere") ∧
      (r.step { relayUrls := [] } P 0 (.auth 0 a)).1.signedIn 0 = some a.pubkey ∧
      (r.step { relayUrls := ["wss://here"] } P 0 (.auth 0 a)).1.signedIn 0 = none := by
  obtain ⟨h, hinj⟩ := exists_injective_hash
  let u : Unsigned := ⟨"K", 0, kindAuth, [["relay", "wss://elsewhere"], ["challenge", "ch"]], ""⟩
  let P : Primitives := ⟨h, fun k d _ => k == "K" && d == h u⟩
  let A : Authorship P := ⟨(· = u), fun _ => False, fun k d s hv _ => by
    simp only [P, Bool.and_eq_true, beq_iff_eq] at hv
    exact ⟨u, rfl, hv.1.symm, hv.2.symm⟩⟩
  refine ⟨P, A, fun k url ch => k = "K" ∧ url = "wss://elsewhere" ∧ ch = "ch", ⟨u, h u, "sig"⟩,
    ⟨["K"], [], [⟨0, "ch", none, []⟩]⟩, hinj, ?_, fun h => h, fun _ _ h => h.2.1, ?_, ?_⟩
  · rintro v rfl -
    simp [u, tagValues]
  · simp [step, conn?, authOk, Event.check, P, u, tagValues, kindAuth, signedIn, update, keyOf]
  · simp [step, conn?, authOk, Event.check, P, u, tagValues, kindAuth, signedIn, keyOf]

end Relay

end Mettapedia.Protocols.Nostr
