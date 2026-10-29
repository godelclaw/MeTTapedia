import Mettapedia.Protocols.Nostr.Event
import Mettapedia.Protocols.Injection.Terminal
import Mettapedia.Protocols.Nostr.Display

/-!
# Every mailbox decision depends on keys only

The mailbox decides five things about a key:
- whether its mail and receipts are admitted;
- where a receipt to it is sent;
- whether its `reset` answers this avatar's checkpoint;
- whether mail to it counts as mail to this avatar itself;
- which address stands for it.

`registry.json` gives each name a key and the relays it reads, and names are
whatever an entry's author wrote. Release 9183c70 made these decisions through
the cleaned name: the first line of the first name for the key, with controls
removed, as `reg_name` printed it. Cleaning can merge two names (`lead` and
`lead` with a bell) and empty a name made only of controls.

The current mailbox decides by key. Its decisions see the registry only through
its key view: which keys have entries, the relays of each key's first entry, and
the parent's key.

The theorems:
- `fixed_factors`: two registries with one key view, the same team and the same
  sends get the same decisions.
- `route_by_entry`: a receipt goes to the relays of the first entry with the key.
- `v5_reset_differs`, `v5_route_differs`, `v5_overdue_differs`,
  `v5_address_differs`, `v5_admit_differs`, `v5_alias_reset_differs`: for each
  decision, two registries with one key view on which 9183c70 decides
  differently.
- `fixed_legacy_reads_names`: a record archived without `X-Nostr-Recipient`
  (mail older than the recipient header) is matched by name, as the fallback
  must.
- `fixed_eq_v5`: for registries whose names are plain and whose keys are
  distinct, the two releases decide alike, so the change alters nothing for
  ordinary registries.

The model covers the five decisions as `mailbox` computes them, with archives
as `render` writes them from the registry (newest first): at 9183c70 `reg_name`
(381-382), `nak_ack` (278-283), `last_sent_type` (465-472, used at 515-517),
`ack_overdue` (1213-1227), `render` (714-721), `cmd_fetch` (865) and `ack_claim`
(643); at 023974f `admit_sender`, `route_receipt`, `last_sent_type`,
`overdue_skip`, `shown_address` and `shown_name`. Keys are opaque
strings. Not modelled: the team's children and review partners (`role_of_key`,
which `Names.lean` covers), and the shell's I/O.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.KeyView

open Mettapedia.Protocols.Nostr

/-- A name as written in `registry.json`. -/
abbrev Name := List Char

/-- An entry of `registry.json`: its name, its key, and the relays it reads
(`none` when the field is absent). -/
structure Entry where
  name : Name
  key : PubKey
  relays : Option (List String)
deriving DecidableEq, Repr

/-- `registry.json`, in file order. -/
abbrev Registry := List Entry

/-- jq reads the registry as an object, so its names are distinct. -/
def Registry.WF (r : Registry) : Prop := (r.map Entry.name).Nodup

/-- Some entry has the key. -/
def hasKey (r : Registry) (k : PubKey) : Bool := r.any (·.key == k)

/-- The first entry with the key: `reg_entry`. -/
def entryOfKey (r : Registry) (k : PubKey) : Option Entry := r.find? (·.key == k)

/-- The entry under a name: jq's `.[$n]`. -/
def entryOfName (r : Registry) (n : Name) : Option Entry := r.find? (·.name == n)

/-- `one_value`: the first line, controls removed (patch 6). -/
def clean (n : Name) : Name := Injection.Terminal.printable (n.takeWhile (· ≠ '\n'))

/-- 9183c70's `reg_name`: the first name with the key, cleaned, or nothing. -/
def regNameV5 (r : Registry) (k : PubKey) : Name := ((entryOfKey r k).map fun e => clean e.name).getD []

/-! ## Relays -/

/-- This avatar's relays, by name, in its order, and whether one URL overrides them. -/
structure Relays where
  override : Bool
  ours : List (String × String)

def everyRelay (rs : Relays) : List String := rs.ours.map (·.2)

/-- Our relays a contact reads: all of them when its list is empty. -/
def reading (rs : Relays) (want : List String) : List String :=
  if want = [] then everyRelay rs else (rs.ours.filter fun p => want.contains p.1).map (·.2)

/-- `routes_to <name>` (mailbox:232-240). -/
def routesTo (rs : Relays) (r : Registry) (n : Name) : List String :=
  if rs.override then everyRelay rs else reading rs (((entryOfName r n).bind (·.relays)).getD [])

/-- 9183c70's `nak_ack`: through the cleaned name. -/
def routeV5 (rs : Relays) (r : Registry) (k : PubKey) : List String := routesTo rs r (regNameV5 r k)

/-- The current `route_receipt`: through the first entry with the key. -/
def routeFixed (rs : Relays) (r : Registry) (k : PubKey) : List String :=
  if rs.override then everyRelay rs
  else match entryOfKey r k with
    | some e => routesTo rs r e.name
    | none => everyRelay rs

/-- Routing by a key's relays: the relays of its first entry. -/
def routeByRelays (rs : Relays) (o : Option (Option (List String))) : List String :=
  if rs.override then everyRelay rs
  else match o with
    | some rel => reading rs (rel.getD [])
    | none => everyRelay rs

theorem entryOfName_of_mem {r : Registry} (h : r.WF) {e : Entry} (he : e ∈ r) :
    entryOfName r e.name = some e := by
  induction r with
  | nil => cases he
  | cons e' r ih =>
    simp only [Registry.WF, List.map_cons, List.nodup_cons] at h
    simp only [entryOfName, List.find?_cons]
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · have hne : e'.name ≠ e.name := fun heq => h.1 (heq ▸ List.mem_map_of_mem he)
      have hb : (e'.name == e.name) = false := by simp [hne]
      rw [hb]
      simpa [entryOfName] using ih h.2 he

theorem mem_of_entryOfKey {r : Registry} {k : PubKey} {e : Entry} (h : entryOfKey r k = some e) :
    e ∈ r := List.mem_of_find?_eq_some h

/-- **A receipt goes to the relays of the first entry with the key.** -/
theorem route_by_entry (rs : Relays) {r : Registry} (h : r.WF) (k : PubKey) :
    routeFixed rs r k = routeByRelays rs ((entryOfKey r k).map (·.relays)) := by
  unfold routeFixed routeByRelays
  split
  · rfl
  · cases he : entryOfKey r k with
    | none => rfl
    | some e =>
      unfold routesTo
      simp [*, entryOfName_of_mem h (mem_of_entryOfKey he)]

/-! ## The archive -/

/-- A file in `.Sent`: its `To:` name, its `X-Nostr-Recipient`, and its type. -/
structure Sent where
  toName : Name
  recipient : Option PubKey
  type : Option String
deriving DecidableEq, Repr

/-- What 9183c70's `render` writes for a send to `k`. -/
def renderV5 (r : Registry) (avatar : Name) (k : PubKey) (t : Option String) : Sent :=
  ⟨if regNameV5 r k = [] then avatar else regNameV5 r k, some k, t⟩

/-- What the current `render` writes: the shown name of the first entry. -/
def renderFixed (r : Registry) (avatar : Name) (k : PubKey) (t : Option String) : Sent :=
  ⟨match entryOfKey r k with
    | some e => Display.shown e.name
    | none => Display.shown avatar, some k, t⟩

/-- The archive of sends (oldest first), newest first as `find | sort -r` reads it. -/
def archive (render : PubKey → Option String → Sent) (sends : List (PubKey × Option String)) :
    List Sent :=
  (sends.map fun s => render s.1 s.2).reverse

/-! ## The decisions -/

/-- 9183c70's `last_sent_type`: by the `To:` name against the raw name. -/
def lastSentTypeV5 (sent : List Sent) (name : Name) : Option String :=
  (sent.find? fun s => s.toName == name && s.type.isSome).bind Sent.type

/-- The current `last_sent_type`: by the recipient key; a record without one, by
the shown name. -/
def lastSentTypeFixed (sent : List Sent) (name : Name) (key : Option PubKey) : Option String :=
  (sent.find? fun s =>
    (match s.recipient with
      | some k => key == some k
      | none => s.toName == Display.shown name) && s.type.isSome).bind Sent.type

/-- The key `registry.json` gives the team's parent name. -/
def parentKey (r : Registry) (parent : Option Name) : Option PubKey :=
  parent.bind fun n => (entryOfName r n).map (·.key)

def resetV5 (sent : List Sent) (parent : Option Name) : Bool :=
  lastSentTypeV5 sent (parent.getD []) == some "checkpoint"

def resetFixed (r : Registry) (sent : List Sent) (parent : Option Name) : Bool :=
  lastSentTypeFixed sent (parent.getD []) (parentKey r parent) == some "checkpoint"

/-- 9183c70's `ack_overdue` test for mail to this avatar itself. -/
def selfV5 (avatar : Name) (s : Sent) : Bool := s.toName == avatar

/-- The current `overdue_skip`. -/
def selfFixed (me : PubKey) (avatar : Name) (s : Sent) : Bool :=
  match s.recipient with
  | some k => k == me
  | none => s.toName == Display.shown avatar

def admitV5 (r : Registry) (k : PubKey) : Bool := regNameV5 r k != []

def admitFixed (r : Registry) (k : PubKey) : Bool := hasKey r k

/-- The address shown for a key. -/
inductive Address
  | npub (k : PubKey)
  | hex (k : PubKey)
deriving DecidableEq, Repr

def addressV5 (r : Registry) (me : PubKey) (k : PubKey) (isTo : Bool) : Address :=
  if regNameV5 r k != [] then .npub k else if isTo then .npub me else .hex k

def addressFixed (r : Registry) (me : PubKey) (k : PubKey) (isTo : Bool) : Address :=
  if hasKey r k then .npub k else if isTo then .npub me else .hex k

/-- What stays the same between the registries compared: this avatar's relays and
key, its name, and the sends it made, oldest first. -/
structure Inputs where
  rs : Relays
  me : PubKey
  avatar : Name
  sends : List (PubKey × Option String)

/-- The five decisions of the current mailbox. -/
def fixed (i : Inputs) (r : Registry) (parent : Option Name) :
    (PubKey → Bool) × (PubKey → List String) × Bool × List Bool × (PubKey → Bool → Address) :=
  let sent := archive (renderFixed r i.avatar) i.sends
  (admitFixed r, routeFixed i.rs r, resetFixed r sent parent, sent.map (selfFixed i.me i.avatar),
    addressFixed r i.me)

/-- The five decisions of 9183c70. -/
def v5 (i : Inputs) (r : Registry) (parent : Option Name) :
    (PubKey → Bool) × (PubKey → List String) × Bool × List Bool × (PubKey → Bool → Address) :=
  let sent := archive (renderV5 r i.avatar) i.sends
  (admitV5 r, routeV5 i.rs r, resetV5 sent parent, sent.map (selfV5 i.avatar), addressV5 r i.me)

/-! ## The key view -/

/-- What a decision may depend on. -/
structure View where
  has : PubKey → Bool
  relaysOf : PubKey → Option (Option (List String))
  parent : Option PubKey

def view (r : Registry) (parent : Option Name) : View :=
  ⟨hasKey r, fun k => (entryOfKey r k).map (·.relays), parentKey r parent⟩

/-- Records that agree on recipient and type, each with a recipient, read alike. -/
theorem lastSentTypeFixed_congr :
    ∀ {l₁ l₂ : List Sent}, l₁.map (fun s => (s.recipient, s.type)) = l₂.map (fun s => (s.recipient, s.type)) →
      (∀ s ∈ l₁, s.recipient.isSome) → ∀ (n₁ n₂ : Name) (key : Option PubKey),
        lastSentTypeFixed l₁ n₁ key = lastSentTypeFixed l₂ n₂ key
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _, _ => by simp at h
  | s₁ :: l₁, s₂ :: l₂, h, hs, n₁, n₂, key => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hr, ht⟩, hl⟩ := h
    have hrec := hs s₁ List.mem_cons_self
    have ih := lastSentTypeFixed_congr hl (fun s hm => hs s (List.mem_cons_of_mem _ hm)) n₁ n₂ key
    unfold lastSentTypeFixed at ih ⊢
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hrec
    simp only [List.find?_cons, hk, ← hr, ← ht]
    split <;> simp_all

theorem archive_recipients (render : PubKey → Option String → Sent)
    (hr : ∀ k t, (render k t).recipient = some k ∧ (render k t).type = t)
    (sends : List (PubKey × Option String)) :
    (archive render sends).map (fun s => (s.recipient, s.type)) = (sends.map fun s => (some s.1, s.2)).reverse ∧
      ∀ s ∈ archive render sends, s.recipient.isSome := by
  refine ⟨?_, ?_⟩
  · simp only [archive, List.map_reverse, List.map_map]
    congr 1
    apply List.map_congr_left
    intro s _
    simp [Function.comp, (hr s.1 s.2).1, (hr s.1 s.2).2]
  · intro s hs
    simp only [archive, List.mem_reverse, List.mem_map] at hs
    obtain ⟨x, _, rfl⟩ := hs
    simp [(hr x.1 x.2).1]

theorem renderFixed_keys (r : Registry) (avatar : Name) (k : PubKey) (t : Option String) :
    (renderFixed r avatar k t).recipient = some k ∧ (renderFixed r avatar k t).type = t :=
  ⟨rfl, rfl⟩

/-- **Every decision depends on keys only.** -/
theorem fixed_factors (i : Inputs) {r₁ r₂ : Registry} {p₁ p₂ : Option Name}
    (h₁ : r₁.WF) (h₂ : r₂.WF) (hv : view r₁ p₁ = view r₂ p₂) :
    fixed i r₁ p₁ = fixed i r₂ p₂ := by
  have hhas : hasKey r₁ = hasKey r₂ := congrArg View.has hv
  have hrel : (fun k => (entryOfKey r₁ k).map (·.relays)) = (fun k => (entryOfKey r₂ k).map (·.relays)) :=
    congrArg View.relaysOf hv
  have hpar : parentKey r₁ p₁ = parentKey r₂ p₂ := congrArg View.parent hv
  obtain ⟨hm₁, hs₁⟩ := archive_recipients _ (renderFixed_keys r₁ i.avatar) i.sends
  obtain ⟨hm₂, hs₂⟩ := archive_recipients _ (renderFixed_keys r₂ i.avatar) i.sends
  have hreset : resetFixed r₁ (archive (renderFixed r₁ i.avatar) i.sends) p₁ =
      resetFixed r₂ (archive (renderFixed r₂ i.avatar) i.sends) p₂ := by
    unfold resetFixed
    rw [hpar, lastSentTypeFixed_congr (hm₁.trans hm₂.symm) hs₁ _ (p₂.getD []) (parentKey r₂ p₂)]
  have hself : (archive (renderFixed r₁ i.avatar) i.sends).map (selfFixed i.me i.avatar) =
      (archive (renderFixed r₂ i.avatar) i.sends).map (selfFixed i.me i.avatar) := by
    simp only [archive, List.map_reverse, List.map_map]
    congr 1
  have hroute : routeFixed i.rs r₁ = routeFixed i.rs r₂ := by
    funext k
    rw [route_by_entry i.rs h₁, route_by_entry i.rs h₂]
    exact congrArg (routeByRelays i.rs) (congrFun hrel k)
  have haddr : addressFixed r₁ i.me = addressFixed r₂ i.me := by
    funext k isTo
    simp only [addressFixed, hhas]
  have hadmit : admitFixed r₁ = admitFixed r₂ := by
    funext k
    simp only [admitFixed, hhas]
  simp only [fixed, hadmit, hroute, hreset, hself, haddr]

/-! ## 9183c70 decides by names -/

def bel : Char := Char.ofNat 7
def keyL : PubKey := "L"
def keyB : PubKey := "B"
def keyM : PubKey := "M"
def twoRelays : Relays := ⟨false, [("public", "wss://public"), ("private", "wss://private")]⟩

/-- `lead`, and `lead` with a bell. -/
def belled : Registry :=
  [⟨"lead".toList, keyL, some ["public"]⟩, ⟨"lead".toList ++ [bel], keyB, some ["private"]⟩]

/-- The same keys and relays, under plain names. -/
def plain : Registry :=
  [⟨"lead".toList, keyL, some ["public"]⟩, ⟨"zed".toList, keyB, some ["private"]⟩]

theorem belled_wf : belled.WF := by unfold Registry.WF; decide
theorem plain_wf : plain.WF := by unfold Registry.WF; decide

theorem belled_view : view belled (some "lead".toList) = view plain (some "lead".toList) := by
  simp only [view, View.mk.injEq]
  refine ⟨?_, ?_, by decide⟩
  · funext k; simp [hasKey, belled, plain]
  · funext k; simp only [entryOfKey, belled, plain, List.find?_cons, List.find?_nil]; split <;> (try split) <;> simp_all

def avatarMe : Name := "me".toList

/-- The child sent a checkpoint to the lead, then a status to the other entry. -/
def checkpointThenStatus : Inputs := ⟨twoRelays, keyM, avatarMe, [(keyL, some "checkpoint"), (keyB, some "status")]⟩

/-- Under `belled`, 9183c70 refuses the lead's reset; under `plain` it allows it. -/
theorem v5_reset_differs :
    (v5 checkpointThenStatus belled (some "lead".toList)).2.2.1 = false ∧
      (v5 checkpointThenStatus plain (some "lead".toList)).2.2.1 = true := by
  decide

/-- 9183c70 sends `belled`'s receipt for `B` to the lead's relay. -/
theorem v5_route_differs :
    routeV5 twoRelays belled keyB = ["wss://public"] ∧ routeV5 twoRelays plain keyB = ["wss://private"] := by
  decide

/-- An entry `me` with a bell, beside this avatar's own. -/
def selfBelled : Registry := [⟨avatarMe, keyM, none⟩, ⟨avatarMe ++ [bel], keyB, none⟩]
def selfPlain : Registry := [⟨avatarMe, keyM, none⟩, ⟨"kay".toList, keyB, none⟩]

theorem self_view : view selfBelled none = view selfPlain none := by
  simp only [view, View.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · funext k; simp [hasKey, selfBelled, selfPlain]
  · funext k; simp only [entryOfKey, selfBelled, selfPlain, List.find?_cons, List.find?_nil]; split <;> (try split) <;> simp_all

/-- 9183c70 takes mail to `me` with a bell for mail to itself, and never raises
it overdue. -/
theorem v5_overdue_differs :
    (v5 ⟨twoRelays, keyM, avatarMe, [(keyB, none)]⟩ selfBelled none).2.2.2.1 = [true] ∧
      (v5 ⟨twoRelays, keyM, avatarMe, [(keyB, none)]⟩ selfPlain none).2.2.2.1 = [false] := by
  decide

/-- An entry whose name is only a bell, and the same key under a plain name. -/
def bellOnly : Registry := [⟨[bel], keyB, none⟩]
def xOnly : Registry := [⟨"x".toList, keyB, none⟩]

theorem bell_view : view bellOnly none = view xOnly none := by
  simp only [view, View.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · funext k; simp [hasKey, bellOnly, xOnly]
  · funext k; simp only [entryOfKey, bellOnly, xOnly, List.find?_cons, List.find?_nil]; split <;> simp_all

/-- 9183c70 shows mail to the bell-named key as addressed to this avatar. -/
theorem v5_address_differs :
    addressV5 bellOnly keyM keyB true = .npub keyM ∧ addressV5 xOnly keyM keyB true = .npub keyB := by
  decide

/-- 9183c70 rejects the bell-named sender as "not in the registry". -/
theorem v5_admit_differs : admitV5 bellOnly keyB = false ∧ admitV5 xOnly keyB = true := by
  decide

/-- The parent as the second entry for its key. -/
def aliased : Registry := [⟨"boss".toList, keyL, none⟩, ⟨"lead".toList, keyL, none⟩]
def single : Registry := [⟨"lead".toList, keyL, none⟩]

theorem alias_view : view aliased (some "lead".toList) = view single (some "lead".toList) := by
  simp only [view, View.mk.injEq]
  refine ⟨?_, ?_, by decide⟩
  · funext k; simp [hasKey, aliased, single]
  · funext k; simp only [entryOfKey, aliased, single, List.find?_cons, List.find?_nil]; split <;> (try split) <;> simp_all

/-- 9183c70 never matches a parent that is the second entry for its key. -/
theorem v5_alias_reset_differs :
    (v5 ⟨twoRelays, keyM, avatarMe, [(keyL, some "checkpoint")]⟩ aliased (some "lead".toList)).2.2.1 = false ∧
      (v5 ⟨twoRelays, keyM, avatarMe, [(keyL, some "checkpoint")]⟩ single (some "lead".toList)).2.2.1 = true := by
  decide

/-- The current mailbox allows the reset in both, as `fixed_factors` says. -/
example : (fixed checkpointThenStatus belled (some "lead".toList)).2.2.1 = true ∧
    (fixed checkpointThenStatus plain (some "lead".toList)).2.2.1 = true := by
  decide

/-! ## Older mail is matched by name -/

/-- A record archived without a recipient is matched by its `To:` name. -/
theorem fixed_legacy_reads_names :
    lastSentTypeFixed [⟨"lead".toList, none, some "checkpoint"⟩] "lead".toList none = some "checkpoint" ∧
      lastSentTypeFixed [⟨"zed".toList, none, some "checkpoint"⟩] "lead".toList none = none := by
  decide


/-! ## For ordinary registries nothing changes -/

/-- A name that cleaning and display both leave as it is, and that is not empty. -/
def Plain (n : Name) : Prop := clean n = n ∧ Display.shown n = n ∧ n ≠ []

theorem find?_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.find?_cons, h x List.mem_cons_self]
    split
    · rfl
    · exact find?_congr fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem entryOfKey_spec {r : Registry} {k : PubKey} {e : Entry} (h : entryOfKey r k = some e) :
    e ∈ r ∧ e.key = k :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem entryOfName_spec {r : Registry} {n : Name} {e : Entry} (h : entryOfName r n = some e) :
    e ∈ r ∧ e.name = n :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem hasKey_iff {r : Registry} {k : PubKey} : hasKey r k = (entryOfKey r k).isSome := by
  unfold hasKey entryOfKey
  rw [Bool.eq_iff_iff, List.any_eq_true, Option.isSome_iff_exists]
  constructor
  · rintro ⟨x, hx, hk⟩
    cases h : r.find? (·.key == k) with
    | none => exact absurd hk (by simpa using List.find?_eq_none.mp h x hx)
    | some y => exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, List.mem_of_find?_eq_some hy, by simpa using List.find?_some hy⟩

theorem regNameV5_of_plain {r : Registry} (hp : ∀ e ∈ r, Plain e.name) (k : PubKey) :
    regNameV5 r k = ((entryOfKey r k).map (·.name)).getD [] := by
  unfold regNameV5
  cases h : entryOfKey r k with
  | none => rfl
  | some e => simp [(hp e (entryOfKey_spec h).1).1]

theorem regNameV5_ne_nil_iff {r : Registry} (hp : ∀ e ∈ r, Plain e.name) (k : PubKey) :
    (regNameV5 r k != []) = hasKey r k := by
  rw [regNameV5_of_plain hp, hasKey_iff]
  cases h : entryOfKey r k with
  | none => rfl
  | some e => simpa using (hp e (entryOfKey_spec h).1).2.2

/-- Under plain names, the two renderers write the same file for a registered key. -/
theorem render_eq {r : Registry} (hp : ∀ e ∈ r, Plain e.name) (avatar : Name) {k : PubKey}
    (hk : hasKey r k = true) (t : Option String) : renderV5 r avatar k t = renderFixed r avatar k t := by
  rw [hasKey_iff, Option.isSome_iff_exists] at hk
  obtain ⟨e, he⟩ := hk
  have hpe := hp e (entryOfKey_spec he).1
  simp [renderV5, renderFixed, regNameV5, he, hpe.1, hpe.2.1, hpe.2.2]

/-- With distinct names and keys, a registered key's entry has a name exactly when it has the
key that name stands for. -/
theorem name_eq_iff_key_eq {r : Registry} (hwf : r.WF) (hkeys : (r.map Entry.key).Nodup)
    {e : Entry} (he : e ∈ r) (n : Name) :
    (e.name == n) = ((entryOfName r n).map (·.key) == some e.key) := by
  cases h : entryOfName r n with
  | none =>
    have : e.name ≠ n := by
      rintro rfl
      rw [entryOfName_of_mem hwf he] at h
      cases h
    simp [this]
  | some p =>
    obtain ⟨hp, hpn⟩ := entryOfName_spec h
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, Option.map_some, Option.some.injEq]
    constructor
    · intro hn
      have := List.inj_on_of_nodup_map hwf he hp (hn.trans hpn.symm)
      rw [this]
    · intro hk
      have := List.inj_on_of_nodup_map hkeys hp he hk
      rw [← hpn, this]

/-- **For ordinary registries the change alters nothing.** With plain names, distinct names
and keys, sends to registered keys, and this avatar registered under its key, the two
releases make the same five decisions. -/
theorem fixed_eq_v5 (i : Inputs) {r : Registry} {parent : Option Name}
    (hwf : r.WF) (hkeys : (r.map Entry.key).Nodup) (hp : ∀ e ∈ r, Plain e.name)
    (hsends : ∀ s ∈ i.sends, hasKey r s.1 = true)
    (hme : ∃ a ∈ r, a.name = i.avatar ∧ a.key = i.me)
    (hpar : ∀ n, parent = some n → n ≠ []) :
    v5 i r parent = fixed i r parent := by
  have harch : archive (renderV5 r i.avatar) i.sends = archive (renderFixed r i.avatar) i.sends := by
    unfold archive
    congr 1
    exact List.map_congr_left fun s hs => render_eq hp i.avatar (hsends s hs) s.2
  -- every archived record is a registered key's entry
  have hrec : ∀ s ∈ archive (renderFixed r i.avatar) i.sends,
      ∃ e ∈ r, s.toName = e.name ∧ s.recipient = some e.key := by
    intro s hs
    simp only [archive, List.mem_reverse, List.mem_map] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    have hk := hsends x hx
    rw [hasKey_iff, Option.isSome_iff_exists] at hk
    obtain ⟨e, he⟩ := hk
    obtain ⟨hmem, hkey⟩ := entryOfKey_spec he
    refine ⟨e, hmem, ?_, by simp [renderFixed, hkey]⟩
    simp [renderFixed, he, (hp e hmem).2.1]
  have hadmit : admitV5 r = admitFixed r := by
    funext k; exact regNameV5_ne_nil_iff hp k
  have haddr : addressV5 r i.me = addressFixed r i.me := by
    funext k isTo; simp only [addressV5, addressFixed, regNameV5_ne_nil_iff hp]
  have hroute : routeV5 i.rs r = routeFixed i.rs r := by
    funext k
    unfold routeV5 routeFixed
    rw [regNameV5_of_plain hp]
    split
    · simp [routesTo, *]
    · cases h : entryOfKey r k with
      | some e => rfl
      | none =>
        have hnone : entryOfName r [] = none := by
          cases h' : entryOfName r [] with
          | none => rfl
          | some e =>
            obtain ⟨hm, hn⟩ := entryOfName_spec h'
            exact absurd hn (hp e hm).2.2
        simp [routesTo, *, reading]
  have hreset : resetV5 (archive (renderFixed r i.avatar) i.sends) parent =
      resetFixed r (archive (renderFixed r i.avatar) i.sends) parent := by
    unfold resetV5 resetFixed lastSentTypeV5 lastSentTypeFixed
    congr 2
    apply find?_congr
    intro s hs
    obtain ⟨e, he, hto, hr⟩ := hrec s hs
    rw [hto, hr]
    congr 1
    cases parent with
    | none =>
      have : (e.name == ([] : Name)) = false := by simpa using (hp e he).2.2
      simp [this, parentKey]
    | some n =>
      simpa [parentKey] using name_eq_iff_key_eq hwf hkeys he n
  have hself : (archive (renderFixed r i.avatar) i.sends).map (selfV5 i.avatar) =
      (archive (renderFixed r i.avatar) i.sends).map (selfFixed i.me i.avatar) := by
    apply List.map_congr_left
    intro s hs
    obtain ⟨e, he, hto, hr⟩ := hrec s hs
    obtain ⟨a, ha, han, hak⟩ := hme
    have := name_eq_iff_key_eq hwf hkeys he i.avatar
    have hea : entryOfName r i.avatar = some a := han ▸ entryOfName_of_mem hwf ha
    rw [hea] at this
    simp only [selfV5, selfFixed, hto, hr]
    rw [this]
    simp [hak, Option.map_some, eq_comm]
  simp only [v5, fixed, harch, hadmit, haddr, hroute, hreset, hself]

/-- The hypotheses meet: a registry of this avatar and its lead, with plain names. -/
example : let r : Registry := [⟨avatarMe, keyM, none⟩, ⟨"lead".toList, keyL, some ["public"]⟩]
    r.WF ∧ (r.map Entry.key).Nodup ∧ (∀ e ∈ r, Plain e.name) := by
  refine ⟨by unfold Registry.WF; decide, by decide, ?_⟩
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> refine ⟨by decide, by decide, by decide⟩

end Mettapedia.Protocols.Nostr.KeyView
