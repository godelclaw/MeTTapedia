import Mettapedia.Protocols.Nostr.RegistryVersions
import Mathlib.Data.Set.Basic

/-!
# Grants: anyone may send, and what a message may cause is granted

Sending is open: any key may send to an agent. What a message may cause is not. Each action
needs a grant, held by a principal that the message's key speaks for in the reader's current
registry version (`RegistryVersions`), and the receiver takes no action outside its own authority.
Nothing here restricts who is heard. A key that speaks for nobody causes nothing.

Agents create children, such as helpers and sub-agents, and declare grants for them. A child's
effective grants are those declared for it and for every agent above it, up to the root, so
delegation can only narrow them (attenuation, as in macaroons and UCAN).

Theorems:
- `causes_authorized`: when the message's key and the authority's are uncompromised, an action
  that a message causes was asked for in an event its key's owner composed, lies within the
  receiver's authority, and is granted to a principal for which the pinned version, or a version
  the authority issued, lists the key. A key that speaks for nobody causes nothing
  (`nobody_causes_nothing`).
- `ambient_deputy`: a receiver that acts on any valid message within its own authority lets a key
  that speaks for nobody cause an action the receiver may take: the confused deputy (Hardy 1988).
  The sender's grant must be checked.
- `effective_append`: along any chain of delegation, an agent below another holds no more than it.
  Granted what is declared for it alone, a child holds more than its parent
  (`unchecked_escalates`).
- `revoke_cascades`: since effective grants are computed through the chain, a grant revoked at an
  agent ends at once for every agent below it. Copied into a child when it was created, the grant
  outlives the revocation (`copied_outlives`).

The chain must be the agent's authenticated chain of ancestors. A revocation takes effect at once
in the table a receiver consults; how fast a change reaches receivers is not modelled. These are
properties of the policy, and that a running service applies it, with its checks of validity,
keys and grants, is a separate obligation.

Not modelled: how a delegation is published and verified, for example as events signed by the
parent's key, and grants that expire.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.Grants

open Mettapedia.Protocols.Nostr Mettapedia.Protocols.Nostr.RegistryVersions

variable {Act : Type}

/-- The actions granted to each principal. -/
abbrev GrantTable (Act : Type) := Principal → Set Act

/-- What a message from the key `k` may cause under the version `v`: the actions within the
receiver's own authority `own` that are granted to a principal for which `v` lists `k`. -/
def allowed (v : Version) (g : GrantTable Act) (own : Set Act) (k : PubKey) : Set Act :=
  {a | a ∈ own ∧ ∃ p, speaksFor v k p ∧ a ∈ g p}

/-- A receiver: how it follows the registry, its pinned version, the grants, its own authority,
and how a message's content names the action it asks for. -/
structure Receiver (Act : Type) where
  reader : Reader
  pinned : Version
  grants : GrantTable Act
  own : Set Act
  request : String → Option Act

namespace Receiver

/-- A message causes an action, after the registry events `regs`: the message is valid, asks for
the action, and the version followed so far allows it for the message's key. -/
def Causes (Rc : Receiver Act) (P : Primitives) (regs : List Event) (m : Event) (a : Act) : Prop :=
  m.Valid P ∧ Rc.request m.content = some a ∧
    a ∈ allowed (Rc.reader.follow P Rc.pinned regs) Rc.grants Rc.own m.pubkey

/-- The receiver acting on any valid message within its own authority. -/
def CausesAmbient (Rc : Receiver Act) (P : Primitives) (m : Event) (a : Act) : Prop :=
  m.Valid P ∧ Rc.request m.content = some a ∧ a ∈ Rc.own

end Receiver

/-- **Every caused action is authorized.** It was asked for in an event that its key's owner
composed, when the key is uncompromised. It lies within the receiver's authority. It is granted to
a principal for which the pinned version, or a version that the authority's owner issued, lists
the key. -/
theorem causes_authorized {Rc : Receiver Act} {P : Primitives} (A : Authorship P)
    (cf : P.CollisionFree) (hauth : ¬ A.compromised Rc.reader.authority) {regs : List Event}
    {m : Event} {a : Act} (h : Rc.Causes P regs m a) (hk : ¬ A.compromised m.pubkey) :
    A.authored m.toUnsigned ∧ a ∈ Rc.own ∧
      ∃ p, a ∈ Rc.grants p ∧
        (speaksFor Rc.pinned m.pubkey p ∨ ∃ v, Issued Rc.reader A v ∧ speaksFor v m.pubkey p) := by
  obtain ⟨hv, -, hown, p, hs, hg⟩ := h
  exact ⟨authentic A cf hv hk, hown, p, hg, speaksFor_sound A cf hauth Rc.pinned regs hs⟩

/-- A message from a key that speaks for nobody causes nothing. -/
theorem nobody_causes_nothing {Rc : Receiver Act} {P : Primitives} {regs : List Event} {m : Event}
    (hn : ∀ p, ¬ speaksFor (Rc.reader.follow P Rc.pinned regs) m.pubkey p) (a : Act) :
    ¬ Rc.Causes P regs m a := by
  rintro ⟨-, -, -, p, hs, -⟩
  exact hn p hs

/-- **The confused deputy.** The receiver may deploy, and only `alice` holds that grant. Acting on
any valid message within its own authority, it deploys at the request of a stranger, whose key
speaks for nobody. With the sender's grant checked, the stranger's message causes nothing, while
the same request from `alice`'s key causes the deployment. -/
theorem ambient_deputy :
    ∃ (Rc : Receiver String) (P : Primitives) (m m' : Event),
      (∀ p, ¬ speaksFor Rc.pinned m.pubkey p) ∧ Rc.CausesAmbient P m "deploy" ∧
        ¬ Rc.Causes P [] m "deploy" ∧ Rc.Causes P [] m' "deploy" := by
  let Rc : Receiver String :=
    { reader := ⟨"auth", fun _ => none⟩
      pinned := ⟨0, fun p => if p = "alice" then ["a"] else []⟩
      grants := fun p => if p = "alice" then {"deploy"} else ∅
      own := {"deploy"}
      request := fun s => some s }
  let P : Primitives := ⟨fun _ => "id", fun _ _ _ => true⟩
  let m : Event := ⟨⟨"stranger", 0, 1, [], "deploy"⟩, "id", ""⟩
  have hn : ∀ p, ¬ speaksFor Rc.pinned m.pubkey p := by
    intro p
    by_cases hp : p = "alice" <;> simp [speaksFor, Rc, m, hp]
  let m' : Event := ⟨⟨"a", 0, 1, [], "deploy"⟩, "id", ""⟩
  refine ⟨Rc, P, m, m', hn, ⟨⟨rfl, rfl⟩, rfl, rfl⟩, nobody_causes_nothing ?_ _,
    ⟨⟨rfl, rfl⟩, rfl, ?_⟩⟩
  · simpa [Reader.follow] using hn
  · exact ⟨rfl, "alice", by simp [speaksFor, Reader.follow, Rc, m'], by simp [Rc]⟩

/-! ## Delegation -/

/-- The effective grants of an agent, from its chain of delegation, root first: the grants
declared for every agent on the chain. -/
def effective (declared : GrantTable Act) : List Principal → Set Act
  | [] => Set.univ
  | p :: ps => declared p ∩ effective declared ps

/-- **Delegation only narrows.** An agent below another holds no more than it. -/
theorem effective_append (declared : GrantTable Act) (ps qs : List Principal) :
    effective declared (ps ++ qs) ⊆ effective declared ps := by
  induction ps with
  | nil => exact Set.subset_univ _
  | cons p ps ih => exact Set.inter_subset_inter_right _ ih

/-- An agent holds no more than is declared for any agent on its chain. -/
theorem effective_subset_of_mem (declared : GrantTable Act) {ps : List Principal} {p : Principal}
    (hp : p ∈ ps) : effective declared ps ⊆ declared p := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Set.inter_subset_left
    · exact Set.inter_subset_right.trans (ih hp)

/-- **Necessity of the bound.** The root `r` holds `read`, and declares `read` and `deploy` for
its child `c`. Granted what is declared for it alone, `c` holds `deploy`, which `r` does not. Its
effective grants hold only `read`. -/
theorem unchecked_escalates :
    let declared : GrantTable String := fun p => if p = "r" then {"read"} else {"read", "deploy"}
    "deploy" ∈ declared "c" ∧ "deploy" ∉ effective declared ["r"] ∧
      "deploy" ∉ effective declared ["r", "c"] := by
  simp [effective]

/-- **Revocation cascades.** When the grants declared for an agent change to `D`, every agent on
a chain through it holds at most `D`, at once. -/
theorem revoke_cascades (declared : GrantTable Act) (p : Principal) (D : Set Act)
    {ps : List Principal} (hp : p ∈ ps) : effective (Function.update declared p D) ps ⊆ D := by
  simpa using effective_subset_of_mem (Function.update declared p D) hp

/-- **Necessity of computing grants through the chain.** The child `c` was created while the root
`r` held `deploy`, and its grants were copied then. After `deploy` is revoked at `r`, the copy
still holds it, while the effective grants of `c` do not. -/
theorem copied_outlives :
    let before : GrantTable String := fun _ => {"read", "deploy"}
    let after : GrantTable String := Function.update before "r" {"read"}
    "deploy" ∈ effective before ["r", "c"] ∧ "deploy" ∉ effective after ["r", "c"] := by
  simp [effective]

end Mettapedia.Protocols.Nostr.Grants
