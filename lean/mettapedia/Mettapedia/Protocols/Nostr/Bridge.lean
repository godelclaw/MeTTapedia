import Mettapedia.Protocols.Nostr.Mailbox
import Mettapedia.Protocols.ClawMail

/-!
# From Nostr mail to claw-mail

A gateway brings Nostr mail into claw-mail. Each event the relay delivers for a
local agent's key goes through the mailbox client's checks (`accept`) and is
sent, as the archived message, on that agent's claw-mail channel. Its
occurrence identity is the event identifier. Its sender is the gateway's own
account, which the claw-mail service authenticates, with the registry name of
the key that signed the event. No tag and no part of the content takes part in
naming the sender.

The theorems:
- `bridge_exactly_once`: whatever the relay delivers, in any order and with any
  repetitions, each accepted event is in the ledger exactly once, recorded as its
  own delivery. A repeated event is a duplicate send and never a conflict: its
  identifier names one set of signed fields, and the delivery depends on nothing
  else.
- `signature_conflict`: a delivery that also recorded the signature would be
  refused as a conflict on a re-signed copy of the same event.
- `bridge_no_impersonation`: mail recorded as from a member whose key is
  uncompromised was signed by that member's key and composed by its owner.
- `bridgeAll_frame`: bridging leaves every other channel's inbox as it was.
-/

namespace Mettapedia.Protocols.Nostr

open Mettapedia.Protocols

/-- The claw-mail agent name of a key: its registry name. -/
def agentName (reg : Registry) (k : PubKey) : String := (nameOf reg k).getD k

/-- The delivery a kept mail becomes. -/
def toDelivery (gateway : ClawMail.Account) (reg : Registry) (owner : ClawMail.Channel)
    (format : Mail.Message → String) (e : Event) (l : Letter) : ClawMail.Delivery :=
  { id := e.id, channel := owner, sender := ⟨gateway, agentName reg e.pubkey⟩,
    body := format (render reg e l) }

/-- The gateway's settings: the primitives, how the agent's key opens mail, the
registry, the agent's key, the gateway's account, the agent's channel and the
message format. -/
structure Gateway where
  P : Primitives
  opener : Opener
  reg : Registry
  me : PubKey
  account : ClawMail.Account
  owner : ClawMail.Channel
  format : Mail.Message → String

namespace Gateway

/-- The mail a gateway keeps, with its letter. -/
def keep (g : Gateway) (e : Event) : Option Letter := accept g.P g.opener g.reg g.me e

/-- The delivery of a kept event. -/
def delivery (g : Gateway) (e : Event) (l : Letter) : ClawMail.Delivery :=
  toDelivery g.account g.reg g.owner g.format e l

/-- Bring one delivered event into claw-mail. -/
def bridge (g : Gateway) (s : ClawMail.State) (e : Event) : ClawMail.State :=
  match g.keep e with
  | some l => (s.post g.account (g.delivery e l)).2
  | none => s

/-- Bring a sequence of delivered events into claw-mail, in order. -/
def bridgeAll (g : Gateway) (s : ClawMail.State) (es : List Event) : ClawMail.State :=
  es.foldl g.bridge s

theorem post_delivery (g : Gateway) (s : ClawMail.State) (e : Event) (l : Letter) :
    s.post g.account (g.delivery e l) = s.send (g.delivery e l) := rfl

/-- Two valid events with one identifier are kept alike and deliver alike. -/
theorem keep_congr {g : Gateway} (cf : g.P.CollisionFree) {e e' : Event} (hv : e.Valid g.P)
    (hv' : e'.Valid g.P) (h : e.id = e'.id) :
    g.keep e = g.keep e' ∧ ∀ l, g.delivery e l = g.delivery e' l := by
  have hu := signed_fields_eq cf hv hv' h
  have hc : e.check g.P = true := (Event.check_iff _ _).mpr hv
  have hc' : e'.check g.P = true := (Event.check_iff _ _).mpr hv'
  rcases e with ⟨u, id, sig⟩
  rcases e' with ⟨u', id', sig'⟩
  simp only at hu h
  subst hu h
  refine ⟨?_, fun l => rfl⟩
  simp only [keep, accept, hc, hc']
  rfl

/-- The ledger invariant of a bridge run: one record per identity, the recorded
identities are exactly those of the kept events, and each kept event is
recorded as its own delivery. -/
def Recorded (g : Gateway) (s : ClawMail.State) (es : List Event) : Prop :=
  s.Valid ∧ (∀ id, id ∈ s.ids ↔ ∃ e ∈ es, e.id = id ∧ (g.keep e).isSome) ∧
    ∀ e ∈ es, ∀ l, g.keep e = some l → s.find e.id = some (g.delivery e l)

theorem find_of_mem {s : ClawMail.State} {id : ClawMail.Occurrence} {d : ClawMail.Delivery}
    (h : s.find id = some d) (dd : ClawMail.Delivery) :
    (⟨s.ledger ++ [dd], s.stage⟩ : ClawMail.State).find id = some d := by
  unfold ClawMail.State.find at *
  rw [List.find?_append, h]
  rfl

theorem bridge_recorded {g : Gateway} (cf : g.P.CollisionFree) {s : ClawMail.State}
    {es : List Event} (hr : g.Recorded s es) (x : Event) : g.Recorded (g.bridge s x) (es ++ [x]) := by
  obtain ⟨hv, hids, hfind⟩ := hr
  unfold bridge
  split
  · next l hl =>
    rw [post_delivery]
    have hval : (s.send (g.delivery x l)).2.Valid := ClawMail.State.send_valid hv _
    unfold ClawMail.State.send
    split
    · next hnone =>
      have fresh : x.id ∉ s.ids := ClawMail.State.find_none.mp hnone
      refine ⟨by simpa [ClawMail.State.send, hnone] using hval, fun id => ?_, fun e he l' hl' => ?_⟩
      · change id ∈ (s.ledger ++ [g.delivery x l]).map ClawMail.Delivery.id ↔ _
        rw [List.map_append, List.mem_append, List.map_singleton, List.mem_singleton]
        change id ∈ s.ids ∨ id = x.id ↔ _
        rw [hids]
        constructor
        · rintro (⟨e, he, hid, hk⟩ | rfl)
          · exact ⟨e, List.mem_append_left _ he, hid, hk⟩
          · exact ⟨x, List.mem_append_right _ (List.mem_singleton_self _), rfl, by simp [hl]⟩
        · rintro ⟨e, he, hid, hk⟩
          rcases List.mem_append.mp he with he | he
          · exact Or.inl ⟨e, he, hid, hk⟩
          · rw [List.mem_singleton] at he
            subst he
            exact Or.inr hid.symm
      · rcases List.mem_append.mp he with he | he
        · have hm : e.id ∈ s.ids := (hids e.id).mpr ⟨e, he, rfl, by simp [hl']⟩
          obtain ⟨d, hd⟩ : ∃ d, s.find e.id = some d := by
            cases h : s.find e.id with
            | none => exact absurd hm (ClawMail.State.find_none.mp h)
            | some d => exact ⟨d, rfl⟩
          have := hfind e he l' hl'
          rw [hd] at this
          cases this
          exact find_of_mem hd _
        · simp only [List.mem_singleton] at he
          subst he
          rw [hl] at hl'
          cases hl'
          have h0 : s.find e.id = none := hnone
          unfold ClawMail.State.find at h0 ⊢
          rw [List.find?_append, h0]
          simp [delivery, toDelivery]
    · next old hold =>
      have hm : x.id ∈ s.ids := by
        obtain ⟨mem, hid⟩ := ClawMail.State.find_some hold
        have : old.id ∈ s.ids := List.mem_map_of_mem mem
        simpa [delivery, toDelivery, hid] using this
      obtain ⟨e, he, hid, hk⟩ := (hids x.id).mp hm
      obtain ⟨lE, hle⟩ := Option.isSome_iff_exists.mp hk
      have hxv : x.Valid g.P := (accept_some hl).1
      have hev : e.Valid g.P := (accept_some hle).1
      obtain ⟨hkeq, hdeq⟩ := keep_congr cf hev hxv hid
      rw [hle, hl] at hkeq
      cases hkeq
      have hrec := hfind e he l hle
      have hsame : old = g.delivery x l := by
        rw [hdeq l, hid] at hrec
        have : s.find x.id = some old := hold
        rw [hrec] at this
        exact (Option.some.inj this).symm
      split
      · refine ⟨hv, fun id => ?_, fun e' he' l' hl' => ?_⟩
        · rw [hids]
          constructor
          · rintro ⟨e', he', h1, h2⟩; exact ⟨e', List.mem_append_left _ he', h1, h2⟩
          · rintro ⟨e', he', h1, h2⟩
            rcases List.mem_append.mp he' with he' | he'
            · exact ⟨e', he', h1, h2⟩
            · simp only [List.mem_singleton] at he'
              subst he'
              exact ⟨e, he, hid.trans h1, hk⟩
        · rcases List.mem_append.mp he' with he' | he'
          · exact hfind e' he' l' hl'
          · simp only [List.mem_singleton] at he'
            subst he'
            rw [hl] at hl'
            cases hl'
            rw [← hsame]
            simpa [delivery, toDelivery] using hold
      · next hne => exact absurd hsame hne
  · next hnone =>
    refine ⟨hv, fun id => ?_, fun e he l hl => ?_⟩
    · rw [hids]
      constructor
      · rintro ⟨e, he, h1, h2⟩; exact ⟨e, List.mem_append_left _ he, h1, h2⟩
      · rintro ⟨e, he, h1, h2⟩
        rcases List.mem_append.mp he with he | he
        · exact ⟨e, he, h1, h2⟩
        · simp only [List.mem_singleton] at he
          subst he
          simp [hnone] at h2
    · rcases List.mem_append.mp he with he | he
      · exact hfind e he l hl
      · simp only [List.mem_singleton] at he
        subst he
        rw [hnone] at hl
        cases hl

/-- Exactly once: whatever the relay delivers, in any order and with any
repetitions, each kept event is in the ledger once, recorded as its own
delivery, and nothing else is. -/
theorem bridge_exactly_once {g : Gateway} (cf : g.P.CollisionFree) (es : List Event) :
    let s := g.bridgeAll ClawMail.State.empty es
    s.ids.Nodup ∧ (∀ id, id ∈ s.ids ↔ ∃ e ∈ es, e.id = id ∧ (g.keep e).isSome) ∧
      ∀ e ∈ es, ∀ l, g.keep e = some l → s.find e.id = some (g.delivery e l) := by
  suffices ∀ (es : List Event) (s : ClawMail.State) (pre : List Event), g.Recorded s pre →
      g.Recorded (es.foldl g.bridge s) (pre ++ es) by
    obtain ⟨hv, hids, hfind⟩ := this es ClawMail.State.empty []
      ⟨ClawMail.State.empty_valid, by simp [ClawMail.State.empty, ClawMail.State.ids], by simp⟩
    simp only [List.nil_append] at hids hfind
    exact ⟨hv.unique, hids, hfind⟩
  intro es
  induction es with
  | nil => intro s pre hr; simpa using hr
  | cons x rest ih =>
    intro s pre hr
    have := ih (g.bridge s x) (pre ++ [x]) (bridge_recorded cf hr x)
    simpa [List.foldl_cons, List.append_assoc] using this

/-- A send on one channel leaves every other channel's inbox as it was. -/
theorem send_inbox_other {s : ClawMail.State} {d : ClawMail.Delivery} {o : ClawMail.Channel}
    (ho : d.channel ≠ o) : (s.send d).2.inbox o = s.inbox o := by
  unfold ClawMail.State.send
  split
  · next hnone =>
    have fresh : d.id ∉ s.ids := ClawMail.State.find_none.mp hnone
    have hf : (s.ledger ++ [d]).filter (fun x => decide (x.channel = o)) =
        s.ledger.filter (fun x => decide (x.channel = o)) := by
      rw [List.filter_append]
      simp [ho]
    simp only [ClawMail.State.inbox, hf]
    congr 2
    apply List.filter_congr
    intro x hx
    have hne : x.id ≠ d.id := fun h =>
      fresh (h ▸ List.mem_map_of_mem (f := ClawMail.Delivery.id) (List.mem_of_mem_filter hx))
    simp [Function.update_of_ne hne]
  · split <;> rfl

theorem bridge_valid {g : Gateway} {s : ClawMail.State} (hs : s.Valid) (e : Event) :
    (g.bridge s e).Valid := by
  unfold bridge
  split
  · rw [post_delivery]; exact ClawMail.State.send_valid hs _
  · exact hs

/-- Bridging leaves every other channel's inbox as it was. -/
theorem bridgeAll_frame {g : Gateway} {o : ClawMail.Channel} (ho : g.owner ≠ o) :
    ∀ (es : List Event) (s : ClawMail.State), (g.bridgeAll s es).inbox o = s.inbox o
  | [], _ => rfl
  | e :: rest, s => by
    have step : (g.bridge s e).inbox o = s.inbox o := by
      unfold bridge
      split
      · rw [post_delivery]; exact send_inbox_other ho
      · rfl
    show (rest.foldl g.bridge (g.bridge s e)).inbox o = s.inbox o
    rw [show rest.foldl g.bridge (g.bridge s e) = g.bridgeAll (g.bridge s e) rest from rfl,
      bridgeAll_frame ho rest, step]

/-- Mail recorded as from a member whose key is uncompromised was signed by that
member's key and composed by its owner. -/
theorem bridge_no_impersonation {g : Gateway} (A : Authorship g.P) (cf : g.P.CollisionFree)
    (hu : (g.reg.map Prod.fst).Nodup) {e : Event} {l : Letter} (hk : g.keep e = some l) {n : String}
    {k : PubKey} (hn : (g.delivery e l).sender.agent = n) (hreg : (n, k) ∈ g.reg)
    (hc : ¬ A.compromised k) : e.pubkey = k ∧ A.authored e.toUnsigned := by
  obtain ⟨-, -, -, n', hn'⟩ := accept_some hk
  apply no_impersonation A cf hu hk (n := n) _ hreg hc
  simp only [delivery, toDelivery, agentName, hn', Option.getD_some] at hn
  simp [render, hn', hn]

end Gateway

namespace Gateway

/-- A delivery that recorded the signature as well. -/
def deliveryWithSig (g : Gateway) (e : Event) (l : Letter) : ClawMail.Delivery :=
  { g.delivery e l with body := (g.delivery e l).body ++ e.sig }

/-- Recording the signature would make a re-signed copy of an event conflict with
the first: both copies are kept, with one identifier and one letter, and the
second send is refused. -/
theorem signature_conflict : ∃ (g : Gateway) (e e' : Event) (l : Letter),
    e.Valid g.P ∧ e'.Valid g.P ∧ e.id = e'.id ∧ g.keep e = some l ∧ g.keep e' = some l ∧
      ((ClawMail.State.empty.send (g.deliveryWithSig e l)).2.send (g.deliveryWithSig e' l)).1 =
        .conflict := by
  let u : Unsigned := ⟨"K", 0, kindMail, [["p", "A"]], "sealed"⟩
  let l : Letter := ⟨"subject", "body", none, none⟩
  let g : Gateway := ⟨⟨fun _ => "id", fun _ d s => d == "id" && (s == "s1" || s == "s2")⟩,
    fun _ _ _ => some l, [("member", "K")], "A", "gateway", "agent", fun _ => ""⟩
  exact ⟨g, ⟨u, "id", "s1"⟩, ⟨u, "id", "s2"⟩, l, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, by decide, by decide,
    by decide⟩

end Gateway

end Mettapedia.Protocols.Nostr
